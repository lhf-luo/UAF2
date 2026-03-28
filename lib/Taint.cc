// Modified Taint.cc with field-sensitive intra-procedural alias analysis and enhanced taint propagation
#include "Taint.h"
#include "Common.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/BinaryFormat/Dwarf.h" 
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/CallGraph.h"  
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Operator.h"
#include "llvm/Pass.h"
#include <llvm/IR/InlineAsm.h>

using namespace llvm;

int TaintPass::TraceArgToCallerParam(Value *arg, Function *F, AliasContext *ctx) {
    if (!arg || !F || !ctx) return -1;

    Value *base = getBasePointer(arg);

    int param_idx = 0;
    for (auto &param : F->args()) {
        if (base == &param) {
            return param_idx;
        }
        param_idx++;
    }

    AliasNode *base_node = getNode(base, ctx);
    if (base_node) {
        param_idx = 0;
        for (auto &param : F->args()) {
            AliasNode *param_node = getNode(&param, ctx);
            if (param_node && param_node == base_node) {
                return param_idx;
            }
            param_idx++;
        }
    }

    if (base_node) {
        param_idx = 0;
        for (auto &param : F->args()) {
            AliasNode *param_node = getNode(&param, ctx);
            if (param_node && checkNodeConnectivity(param_node, base_node, ctx)) {
                return param_idx;
            }
            param_idx++;
        }
    }

    std::set<Value*> baseAliasSet;
    getPreviousValues(base, baseAliasSet, ctx);

    if (!baseAliasSet.empty()) {
        param_idx = 0;
        for (auto &param : F->args()) {
            if (baseAliasSet.count(&param)) {
                return param_idx;
            }
            param_idx++;
        }
    }

    return -1;
}

// 合并两个字段路径
std::vector<int> TaintPass::MergeFieldPaths(const std::vector<int> &prefix, 
                                            const std::vector<int> &suffix) {
    std::vector<int> result = prefix;
    result.insert(result.end(), suffix.begin(), suffix.end());
    
    // 规范化路径：移除连续的 -1（解引用）
    std::vector<int> normalized;
    for (size_t i = 0; i < result.size(); ++i) {
        if (result[i] == -1 && i + 1 < result.size() && result[i + 1] == -1) {
            continue; // 跳过冗余的解引用
        }
        normalized.push_back(result[i]);
    }
    
    return normalized;
}

// ========== TaintPass Class Implementation ========== 

uint64_t TaintPass::getPointerSize(Type *PT, const DataLayout &DL)
{
    Type *ElementType = PT->getPointerElementType();
    if (ElementType->isSized()) {
      return DL.getTypeStoreSize(ElementType);
    }
    return 1;
}

size_t TaintPass::getInstSourceInfo(CallInst* CI) {
    std::hash<std::string> hasher;
    std::string info;
    
    if (CI->getDebugLoc()) {
        info = CI->getDebugLoc()->getFilename().str() + ":" + 
               std::to_string(CI->getDebugLoc()->getLine()) + ":" + 
               std::to_string(CI->getDebugLoc()->getColumn());
    } else {
        info = CI->getFunction()->getName().str() + ":" + 
               std::to_string(reinterpret_cast<uintptr_t>(CI));
    }
    
    return hasher(info);
}

// ========== Function-Level Alias Analysis Cache ========== 

AliasContext* TaintPass::GetOrBuildFunctionAlias(Function *F) {
    // Use the ReleaseWrapperAnalyzer's helper to access/build the alias context
    return RWAnalyzer.GetOrBuildFunctionAlias(F);
}

// ========== Simple Intra-Procedural Alias Check ========== 

bool TaintPass::IsAliased(Value *V1, Value *V2, AliasContext *aliasCtx) {
    if (V1 == V2) return true;
    if (!V1 || !V2 || !aliasCtx) return false;
    
    // Safety check for pointers
    if (V1->getValueID() > Value::InstructionVal + 100) return false; // Simple sanity
    if (V2->getValueID() > Value::InstructionVal + 100) return false; 

    AliasNode *N1 = getNode(V1, aliasCtx);
    AliasNode *N2 = getNode(V2, aliasCtx);
    
    if (N1 && N2 && N1 == N2) return true;
    
    // Simple syntactic alias check
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V1)) {
        if (GEP->getPointerOperand() == V2) return true;
    }
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V2)) {
        if (GEP->getPointerOperand() == V1) return true;
    }
    if (BitCastInst *BC = dyn_cast<BitCastInst>(V1)) {
        if (BC->getOperand(0) == V2) return true;
    }
    if (BitCastInst *BC = dyn_cast<BitCastInst>(V2)) {
        if (BC->getOperand(0) == V1) return true;
    }
    
    return false;
}

bool TaintPass::IsDangerousFunction(StringRef FuncName) {
    static std::set<StringRef> DangerousFuncs = {
        "memcpy", "strcpy", "strlen", "sprintf", "printf", "fprintf",
        "memset", "memmove", "strcat", "strcmp", "strncmp", "sscanf"
    };
    
    for (StringRef Dangerous : DangerousFuncs) {
        if (FuncName.contains(Dangerous)) {
            return true;
        }
    }
    return false;
}

// ========== Error Handling Block Identification ========== 

bool TaintPass::isErrorHandlingBlock(BasicBlock *BB) {
    // 1. Name suggests error handling
    if (BB->getName().contains("err") || BB->getName().contains("fail") || 
        BB->getName().contains("out") || BB->getName().contains("cleanup")) {
        return true;
    }
    
    // 2. Contains early returns with negative values
    for (auto &I : *BB) {
        if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
            Value *RetVal = RI->getReturnValue();
            if (RetVal) {
                if (ConstantInt *CI = dyn_cast<ConstantInt>(RetVal)) {
                    if (CI->isNegative()) {
                        return true;
                    }
                }
            }
        }
    }
    
    // 3. Contains calls to cleanup/free/destroy functions
    for (auto &I : *BB) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            Function *Callee = CI->getCalledFunction();
            if (Callee) {
                StringRef Name = Callee->getName();
                if (Name.contains("free") || Name.contains("cleanup") || 
                    Name.contains("destroy") || Name.contains("release")) {
                    return true;
                }
            }
        }
    }
    
    // 4. Contains a limited number of instructions before return
    unsigned InstCount = 0;
    bool HasReturn = false;
    for (auto &I : *BB) {
        InstCount++;
        if (isa<ReturnInst>(&I)) {
            HasReturn = true;
        }
    }
    
    if (HasReturn && InstCount < 8) {
        return true;
    }
    
    return false;
}

// ========== Error Return Function Analysis ========== 
//The error return point is associated with the freePointer information.
void TaintPass::ErrorReturnFuncAnalysis(Function *F) {
    // Step 1: Identify all error code variables as taint sources
    std::set<Value*> ErrorCodeVars;
    std::set<Value*> ErrorCodeVarsFromERR; //ret 
    bool isErrorReturnFunc = false;
    
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
                Value *Val = SI->getValueOperand();
                Value *Ptr = SI->getPointerOperand();
                
                // Check if a null pointer is stored
                if (isa<ConstantPointerNull>(Val)) {
                    ErrorCodeVars.insert(Ptr);
                }
                
                // Check if a negative constant is stored
                if (ConstantInt *CI = dyn_cast<ConstantInt>(Val)) {
                    if (CI->isNegative()) {
                        ErrorCodeVars.insert(Ptr);
                    }
                }
            }
            
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                Function *Callee = CI->getCalledFunction();
                if (Callee && Callee->getName().find("ERR_PTR") != std::string::npos) {
                    ErrorCodeVars.insert(CI);
                    ErrorCodeVarsFromERR.insert(CI);
                }
                if (Callee && Callee->getName().find("PTR_ERR") != std::string::npos) {
                    ErrorCodeVars.insert(CI);
                    ErrorCodeVarsFromERR.insert(CI);
                }
            }
        }
    }
    
    if (ErrorCodeVars.empty()) {
        return;
    }
    
    //errs() << "Found " << ErrorCodeVars.size() << " error code variables in function " 
           //<< F->getName() << ", running taint analysis...\n";
    
    // Step 2: Identify all possible sink points
    std::set<Value*> SinkArgs;
    std::set<ReturnInst*> SinkReturns;
    
    for (Argument &Arg : F->args()) {
        if (Arg.getType()->isPointerTy()) {
            SinkArgs.insert(&Arg);
        }
    }
    
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                SinkReturns.insert(RI);
            }
        }
    }
    
    // Step 3: Perform taint analysis
    std::set<Value*> TaintedValues;
    std::set<ReturnInst*> TaintedSinks; //not use
    std::map<Value*,Instruction*> ErrorValidations;
    
    std::queue<Value*> WorkList; // all ErrReturn
    for (Value *ErrorCode : ErrorCodeVars) {
        TaintedValues.insert(ErrorCode);
        WorkList.push(ErrorCode);
    }
    
    while (!WorkList.empty()) {
        Value *TaintedValue = WorkList.front();
        WorkList.pop();
        
        for (User *U : TaintedValue->users()) {
            if (Instruction *I = dyn_cast<Instruction>(U)) {
                if (BasicBlock *B = I->getParent())
                    if (B->getParent() != F) continue;
                
                if (TaintedValues.count(I)) continue;
                
                bool NewTaint = false;
                
                if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
                    if (LI->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                    if (SI->getValueOperand() == TaintedValue) {
                        Value *Ptr = SI->getPointerOperand();
                        if (!TaintedValues.count(Ptr)) {
                            TaintedValues.insert(Ptr);
                            WorkList.push(Ptr);
                        }
                    }
                } else if (CastInst *CI = dyn_cast<CastInst>(I)) {
                    NewTaint = true;
                } else if (PHINode *PHI = dyn_cast<PHINode>(I)) {
                    for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
                        if (PHI->getIncomingValue(i) == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I)) {
                    if (GEP->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (CallInst *CallI = dyn_cast<CallInst>(I)) {
                    for (unsigned i = 0; i < CallI->arg_size(); i++) {
                        if (CallI->getArgOperand(i) == TaintedValue) {
                            if (!CallI->getType()->isVoidTy()) {
                                NewTaint = true;
                            }
                            break;
                        }
                    }
                } else if (BinaryOperator *BinOp = dyn_cast<BinaryOperator>(I)) {
                    if (BinOp->getOperand(0) == TaintedValue || 
                        BinOp->getOperand(1) == TaintedValue) {
                        NewTaint = true;
                    }
                } else if(ICmpInst *Cmp = dyn_cast<ICmpInst>(I)){

                    if (Cmp->getOperand(0) == TaintedValue || Cmp->getOperand(1) == TaintedValue) {
                        //ErrorCodeVarsFromERR
                        Value* V=isFromERR(TaintedValue,ErrorCodeVarsFromERR);
                        if(V){
                            ErrorValidations[V]=Cmp;
                        }
                        NewTaint = true;
                    }
                }else {
                    for (Use &U : I->operands()) {
                        if (U.get() == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                }
                
                if (NewTaint) {
                    TaintedValues.insert(I);
                    WorkList.push(I);
                }
            }
        }
    }
    
    // Step 4: Check if return statement sinks are tainted
    for (ReturnInst *RI : SinkReturns) {
        if (Value *RetVal = RI->getReturnValue()) {
            if (TaintedValues.count(RetVal)) {
                TaintedSinks.insert(RI);
                isErrorReturnFunc = true;
            }
        }
    }
    
    if (!isErrorReturnFunc) {
        //errs() << "\nFunction " << F->getName() << " identified as an error-propagating function\n";
        return;
    }
    Ctx->ErrorReturnFuncs.insert(F);
    errs() << "\nFunction " << F->getName() << " identified as an error-propagating function";
    // TaintedSinks is return ERROR
    
    std::map<Value*,std::set<llvm::BasicBlock*>> retValueBB;
    for (auto pair : ErrorValidations) {
        Instruction *Validation=pair.second;
        Value* retValue=pair.first;
        for (User *U : Validation->users()) {
            if (BranchInst *BI = dyn_cast<BranchInst>(U)) {
                if (BI->isConditional() && BI->getCondition() == Validation) {
                    BasicBlock *TrueBB = BI->getSuccessor(0);
                    BasicBlock *FalseBB = BI->getSuccessor(1);
                    
                    bool errorInTrueBranch = DetermineErrorBranch(Validation);
                    
                    if (errorInTrueBranch) {
                        retValueBB[retValue].insert(TrueBB);
                    } else {
                        retValueBB[retValue].insert(FalseBB);
                    }
                    //DirectErrorBBs.insert(BI->getParent());
                }
            }
        }
    }

    std::set<BasicBlock*> BackReachable;
    std::vector<BasicBlock*> BackWorkList;
    std::set<BasicBlock*> SinkBlocks;

    for(ReturnInst* RI: TaintedSinks){
        SinkBlocks.insert(RI->getParent());
    }

    for (BasicBlock *BB : SinkBlocks) {
        BackReachable.insert(BB);
        BackWorkList.push_back(BB);
    }

    
    while (!BackWorkList.empty()) {
        BasicBlock *CurrentBB = BackWorkList.back();
        BackWorkList.pop_back();
        
        for (BasicBlock *Pred : predecessors(CurrentBB)) {
            if (BackReachable.insert(Pred).second) {
                BackWorkList.push_back(Pred);
            }
        }
    }
    for(auto &pair:retValueBB){
        std::queue<BasicBlock*> BBWorkList;
        std::set<BasicBlock*> DirectErrorBBs=pair.second;
        std::set<BasicBlock*> Visited;
        for (BasicBlock *DirectErrorBB : DirectErrorBBs){
            BBWorkList.push(DirectErrorBB);
            Visited.insert(DirectErrorBB);
        }

        while (!BBWorkList.empty()){
            BasicBlock *CurrentBB = BBWorkList.front();
            BBWorkList.pop();
            for (BasicBlock *Succ : successors(CurrentBB)) {
                if (Visited.count(Succ)) continue;
                if(BackReachable.count(Succ)){
                    BBWorkList.push(Succ);
                    Visited.insert(Succ);
                }
            }
        }
        pair.second.insert(Visited.begin(),Visited.end());
    }

    // TODO handle release in ErrorBB

    bool isChange=false;
    for(auto &pair:retValueBB){
        Value* ret=pair.first;
        retFunction[F].insert(ret);
        std::vector<FreePointInfo> NodeFreePoints;
        for (BasicBlock *BB : pair.second) {
            FindDirectFreePoints(BB, NodeFreePoints);
            FindReleaseWrapperFreePoints(BB, NodeFreePoints);
            FindExternalFreePoints(BB, NodeFreePoints);  
        }
        for (const FreePointInfo &FreePoint : NodeFreePoints){
            //has connect with Arg?
            retFreePoint[ret].insert(FreePoint);
            errs()<<"find condition release in "<<F->getName();
        }
        isChange|=ConditionReleaseWrapperAnalysis(ret,std::move(NodeFreePoints)); 
    }

    for(CallInst* CI:Ctx->Callers[F]){
        IdentifyErrReturnRelease(CI,isChange);
    }

}


void TaintPass::IdentifyErrReturnRelease(CallInst* CI,bool isConditionReleaseWapperChange){
    Function* F=CI->getFunction();

    if(F->getName().contains("mlx5_ib_add")){
        printInstruction(CI);
    }
    
    if(F->getName().contains("mlx5_ib_stage_post_ib_reg_umr_init")){
        printInstruction(CI);
    }
    llvm::BasicBlock* CIBB=CI->getParent();
    if(retFunction.count(F) && retFunction[F].count(CI)){
        //Just focus on conditional release
        if(isConditionReleaseWapperChange){
            std::vector<FreePointInfo> NodeFreePoints;
            FindConditionReleaseWrapperFreePoints(CI, NodeFreePoints);

            for (const FreePointInfo &FreePoint : NodeFreePoints){
                retFreePoint[CI].insert(FreePoint);
            }
            bool isChange=ConditionReleaseWrapperAnalysis(CI,std::move(NodeFreePoints));
            for(CallInst* CI:Ctx->Callers[F]){
                
                IdentifyErrReturnRelease(CI,isChange);
            }
        }
        else{
            return ;
        }
    }
    
    
    std::set<ICmpInst*> ErrorValidations;
    std::set<Value*> TaintedValues;
    std::set<ReturnInst*> TaintedReturns;
    std::queue<Value*> WorkList;

    //
    
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
                Value *Val = SI->getValueOperand();
                Value *Ptr = SI->getPointerOperand();
                
                // Check if a null pointer is stored
                if (isa<ConstantPointerNull>(Val)) {
                    TaintedValues.insert(Ptr);
                    WorkList.push(Ptr);
                }
                
                // Check if a negative constant is stored
                if (ConstantInt *CI = dyn_cast<ConstantInt>(Val)) {
                    if (CI->isNegative()) {
                        TaintedValues.insert(Ptr);
                        WorkList.push(Ptr);
                    }
                }
            }
        }
    }

    

    
    WorkList.push(CI);
    TaintedValues.insert(CI);

    if(F->getName().contains("mlx5_ib_stage_post_ib_reg_umr_init")){
        errs()<<"debug";
        printInstruction(CI);
    }
    while (!WorkList.empty()){
        Value* TaintedValue = WorkList.front();
        WorkList.pop();
        for (User* U : TaintedValue->users()){
            if (Instruction* I = dyn_cast<Instruction>(U)){
                if (BasicBlock* B = I->getParent())
                    if (B->getParent() != F) continue;
                if (TaintedValues.count(I)) continue;
                bool NewTaint = false;

                if (LoadInst* LI = dyn_cast<LoadInst>(I)) {
                    if (LI->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                }
                else if (StoreInst* SI = dyn_cast<StoreInst>(I)) {
                    if (SI->getValueOperand() == TaintedValue) {
                        Value* Ptr = SI->getPointerOperand();
                        if (!TaintedValues.count(Ptr)) {
                            TaintedValues.insert(Ptr);
                            WorkList.push(Ptr);
                        }
                    }
                }
                else if (CastInst* CI = dyn_cast<CastInst>(I)) {
                    NewTaint = true;
                }
                else if (PHINode* PHI = dyn_cast<PHINode>(I)) {
                    for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
                        if (PHI->getIncomingValue(i) == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                }
                else if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(I)) {
                    if (GEP->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                }
                else if (CallInst* CallI = dyn_cast<CallInst>(I)) {
                    for (unsigned i = 0; i < CallI->arg_size(); i++) {
                        if (CallI->getArgOperand(i) == TaintedValue) {
                            if (!CallI->getType()->isVoidTy()) {
                                NewTaint = true;
                            }
                            break;
                        }
                    }
                }
                else if (BinaryOperator* BinOp = dyn_cast<BinaryOperator>(I)) {
                    if (BinOp->getOperand(0) == TaintedValue ||
                        BinOp->getOperand(1) == TaintedValue) {
                        NewTaint = true;
                    }
                }
                else if (ReturnInst* RI = dyn_cast<ReturnInst>(I)) {
                    Value* RetVal = RI->getReturnValue();
                    if (RetVal == TaintedValue) {
                        TaintedReturns.insert(RI);
                    }
                }
                else if (ICmpInst* Cmp = dyn_cast<ICmpInst>(I)) {

                    if (Cmp->getOperand(0) == TaintedValue || Cmp->getOperand(1) == TaintedValue) {
                        llvm::BasicBlock* CmpB=Cmp->getParent();

                        if(CIBB==CmpB){
                            ErrorValidations.insert(Cmp);
                        }
                        NewTaint = true;
                    }
                }
                else {
                    for (Use& Op : I->operands()) {
                        if (Op.get() == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                }
                if (NewTaint) {
                    TaintedValues.insert(I);
                    WorkList.push(I);
                }

            }
        }
    }

    
    bool isErrorReturn=!TaintedReturns.empty(); //


    if(!isErrorReturn){
        return ;
    }
    

    // -------------------------------------
    Ctx->ErrorReturnFuncs.insert(F);
    retFunction[F].insert(CI);


    std::set<llvm::BasicBlock*> DirectErrorBBs;
    for (ICmpInst* Cmp : ErrorValidations){ //There should be only one.
        for (User* U : Cmp->users()){
            if (BranchInst* BI = dyn_cast<BranchInst>(U)) {
                if (BI->isConditional() && BI->getCondition() == Cmp) {
                    BasicBlock* TrueBB = BI->getSuccessor(0);
                    BasicBlock* FalseBB = BI->getSuccessor(1);

                    bool errorInTrueBranch = DetermineErrorBranch(Cmp);

                    if (errorInTrueBranch) {
                        DirectErrorBBs.insert(TrueBB);
                    }
                    else {
                        DirectErrorBBs.insert(FalseBB);
                    }
                    //DirectErrorBBs.insert(BI->getParent());
                }
            }
        }
    }
    std::queue<BasicBlock*> BBWorkList;
    std::set<BasicBlock*> Visited;

    for (BasicBlock* DirectErrorBB : DirectErrorBBs) {
        BBWorkList.push(DirectErrorBB);
        Visited.insert(DirectErrorBB);
    }

    while (!BBWorkList.empty()) {
        BasicBlock* CurrentBB = BBWorkList.front();
        BBWorkList.pop();
        for (BasicBlock* Succ : successors(CurrentBB)) {
            if (Visited.count(Succ)) continue;
            BBWorkList.push(Succ);
            Visited.insert(Succ);
        }
    }
    DirectErrorBBs.insert(Visited.begin(), Visited.end());

    
    std::vector<FreePointInfo> NodeFreePoints;
    bool isFindConditionRelease=false;
    for (BasicBlock* BB : DirectErrorBBs){
        FindDirectFreePoints(BB, NodeFreePoints);
        FindReleaseWrapperFreePoints(BB, NodeFreePoints);
        FindExternalFreePoints(BB, NodeFreePoints);
            //The conditional release corresponding to the error return.
    }
    if(isConditionReleaseWapperChange){
        FindConditionReleaseWrapperFreePoints(CI, NodeFreePoints);
    }
    
    for (const FreePointInfo &FreePoint : NodeFreePoints){
        //has connect with Arg?
        retFreePoint[CI].insert(FreePoint);
        printInstruction(FreePoint.FreeCall);
        errs()<<":find condition release in "<<F->getName();
    }

    bool isChange=ConditionReleaseWrapperAnalysis(CI,std::move(NodeFreePoints));

    for(CallInst* CI:Ctx->Callers[F]){
        if(CI->getFunction()->getName().contains("__mlx5_ib_add")){
            errs()<<"DEBUG";
        }
        IdentifyErrReturnRelease(CI,isChange);
    }

}

bool TaintPass::ConditionReleaseWrapperAnalysis(Value* V,std::vector<FreePointInfo> NodeFreePoints){
    bool isChange=false;
    for (const FreePointInfo &FreePoint : NodeFreePoints){
        std::map<int, std::string> arg_access_map;
        Value* FreedPointer=FreePoint.FreedPointer;//
        Function * F=FreePoint.ContainingFunc;
        CallInst* CI=FreePoint.FreeCall;

        checkValueComesFromArg(F,FreedPointer,arg_access_map);
        
        for (const auto& pair : arg_access_map){
            string local_path = pair.second;
            std::vector<int> FieldPath;
            getFieldPath(local_path,FieldPath);
            FieldPath.insert(FieldPath.end(),FreePoint.FieldPath.begin(),FreePoint.FieldPath.end());
            
            ConditionReleaseWrapper CRW(F,FieldPath,CI,pair.first);

            
            auto p=retConditionReleaseWrapper[V].insert(CRW);
            isChange|=p.second;
            errs()<<"\nfind condition release wrapper"<<F->getName(); 
        }
    }
    return isChange;
}


void TaintPass::getFieldPath(std::string& PathHash,std::vector<int>& FieldPath){
    std::stringstream ss(PathHash);
    std::string segment;
    while (std::getline(ss, segment, '|')) {
        try {
            if (segment == "*") {
                FieldPath.push_back(-1);
            } else if (segment == "?") {
                FieldPath.push_back(99);
            } else {
                FieldPath.push_back(std::stoi(segment));
            }
        } catch (...) {

        }
    }
}

void TaintPass::checkValueComesFromArg(Function* F,Value* FreedPointer,std::map<int, std::string>& arg_access_map){
    
    AliasContext* aliasCtx=GetOrBuildFunctionAlias(F);
    AliasNode* n_freed_v = getNode(FreedPointer, aliasCtx);

    if (!n_freed_v) return;
    int arg_idx = -1;
    for (auto it = F->arg_begin(); it != F->arg_end(); it++){
        arg_idx++;
        Argument* arg = &*it;
        if (!arg->getType()->isPointerTy()) continue;
        AliasNode* n_arg = getNode(arg, aliasCtx);
        if (!n_arg) continue;
        string access_hash;
        if (getAliasNodeAccessArr(aliasCtx, n_arg, n_freed_v, access_hash)){
            arg_access_map[arg_idx] = access_hash;
            continue;
        }
        std::map<std::string, Value*> container_map;
        getContainerOfArgs(F, arg_idx, container_map, aliasCtx);
        
        for (auto& container_pair : container_map) {
            string pre_hash = container_pair.first;//
            if(pre_hash!=""){
                pre_hash+="|";
            }

            Value* arg_container = container_pair.second;

            AliasNode* n_arg_container = getNode(arg_container, aliasCtx);
            if (!n_arg_container) continue;

            string access_hash_inner;
            if (getAliasNodeAccessArr(aliasCtx, n_arg_container, n_freed_v, access_hash_inner)) {
                access_hash_inner = pre_hash + access_hash_inner;
                if (!access_hash_inner.empty() && access_hash_inner.back() == '|') {
                    access_hash_inner.pop_back();
                }
                arg_access_map[arg_idx] = access_hash_inner;
                continue;
            }
        }

    }
}


Value* TaintPass::isFromERR(Value* TaintedValue,set<Value*>& ErrorCodeVarsFromERR){
    if(!TaintedValue){
        return nullptr;
    }
    if(ErrorCodeVarsFromERR.count(TaintedValue)){
        return TaintedValue;
    } 

    if(LoadInst* load = dyn_cast<LoadInst>(TaintedValue)){
        Instruction *PrevInst = load->getPrevNonDebugInstruction();
        if(!PrevInst){
            return nullptr;
        }
        if(StoreInst* SI=dyn_cast<StoreInst>(PrevInst)){
            Value* V=SI->getValueOperand();
            if(V){
                if(ErrorCodeVarsFromERR.count(V)){
                    return V;
                } 
            }

        }
    }
    return nullptr;
}

/*
bool TaintPass::InterproceduralErrorAnalysis(Function *F) {
    std::set<Value*> ErrorReturnCalls; // change
    std::map<CallInst*, Value*> ErrorReturnVars;

    std::map<Value*,std::set<Function*>> ErrorReturnFunction;
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                
                Function *Callee = CI->getCalledFunction();
                
                if (Callee && Ctx->ErrorReturnFuncs.count(Callee)) {
                    ErrorReturnCalls.insert(CI);
                    ErrorReturnVars[CI] = CI;
                    ErrorReturnFunction[CI].insert(Callee);
                    
                    continue;
                }
                
                if (!Callee) {
                    auto Callees = Ctx->Callees.find(CI);
                    if (Callees != Ctx->Callees.end()) {
                        for (Function *PotentialCallee : Callees->second) {
                            if (Ctx->ErrorReturnFuncs.count(PotentialCallee)) {
                                ErrorReturnCalls.insert(CI);
                                ErrorReturnVars[CI] = CI;
                                ErrorReturnFunction[CI].insert(PotentialCallee);
                              
                                break;
                            }
                        }
                    }
                }
            }
        
        }
    }
    
    if (ErrorReturnCalls.empty()) {
        return false;
    }
    
    //errs() << "Found " << ErrorReturnCalls.size() << " calls to error-returning functions in " 
           //<< F->getName() << ", running interprocedural taint analysis...\n";
    
    /*
    std::set<ReturnInst*> SinkReturns;//not use
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                SinkReturns.insert(RI);
            }
        }
    }
    

    
    std::set<Value*> TaintedValues;
    std::set<ReturnInst*> TaintedReturns;
    std::map<Value*, Instruction*> ErrorValidations; //Which jump statement is callInst associated with?
    
    std::queue<Value*> WorkList;
    for (auto &Entry : ErrorReturnVars) {
        Value *ErrorRetVal = Entry.second;
        TaintedValues.insert(ErrorRetVal);
        WorkList.push(ErrorRetVal);
    }
    
    while (!WorkList.empty()) {
        Value *TaintedValue = WorkList.front();
        WorkList.pop();
        if(Instruction* I=dyn_cast<Instruction>(TaintedValue)){
            printInstruction(I);
        }
        for (User *U : TaintedValue->users()) {
            if (Instruction *I = dyn_cast<Instruction>(U)) {
                printInstruction(I);
                if (BasicBlock *B = I->getParent())
                    if (B->getParent() != F) continue;
                
                if (TaintedValues.count(I)) continue;
                
                bool NewTaint = false;
                
                if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
                    if (LI->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                    if (SI->getValueOperand() == TaintedValue) {
                        Value *Ptr = SI->getPointerOperand();
                        if (!TaintedValues.count(Ptr)) {
                            TaintedValues.insert(Ptr);
                            WorkList.push(Ptr);
                        }
                    }
                } else if (CastInst *CI = dyn_cast<CastInst>(I)) {
                    NewTaint = true;
                } else if (PHINode *PHI = dyn_cast<PHINode>(I)) {
                    for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
                        if (PHI->getIncomingValue(i) == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I)) {
                    if (GEP->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (CallInst *CallI = dyn_cast<CallInst>(I)) {
                    for (unsigned i = 0; i < CallI->arg_size(); i++) {
                        if (CallI->getArgOperand(i) == TaintedValue) {
                            if (!CallI->getType()->isVoidTy()) {
                                NewTaint = true;
                            }
                            break;
                        }
                    }
                } else if (BinaryOperator *BinOp = dyn_cast<BinaryOperator>(I)) {
                    if (BinOp->getOperand(0) == TaintedValue || 
                        BinOp->getOperand(1) == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
                    Value *RetVal = RI->getReturnValue();
                    if (RetVal == TaintedValue) {
                        TaintedReturns.insert(RI);
                    }
                } else if (ICmpInst* Cmp = dyn_cast<ICmpInst>(I)) {

                    if (Cmp->getOperand(0) == TaintedValue || Cmp->getOperand(1) == TaintedValue) {
                        Value* V = isFromERR(TaintedValue, ErrorReturnCalls);
                        if (V) {
                            ErrorValidations[V] = Cmp;
                        }
                        
                        NewTaint = true;
                    }
                }else {
                    for (Use &Op : I->operands()) {
                        if (Op.get() == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                }
                
                if (NewTaint) {
                    TaintedValues.insert(I);
                    WorkList.push(I);
                    
                    if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
                        Value *RetVal = RI->getReturnValue();
                        if (RetVal && TaintedValues.count(RetVal)) {
                            TaintedReturns.insert(RI);
                        }
                    }
                }
            }
        }
    }
    
    bool IsErrorPropagatingFunc = !TaintedReturns.empty();
    
    if (!IsErrorPropagatingFunc) {
        
        return false;
    }
    Ctx->ErrorReturnFuncs.insert(F);
    //errs() << "\nFunction " << F->getName() << " identified as an interprocedural error-propagating function\n";
        

    //------------------------------------------
    std::map<Value*, std::set<llvm::BasicBlock*>> retValueBB;
    for (auto pair : ErrorValidations) {
        Instruction* Validation = pair.second;
        Value* retValue = pair.first;
        for (User* U : Validation->users()) {
            if (BranchInst* BI = dyn_cast<BranchInst>(U)) {
                if (BI->isConditional() && BI->getCondition() == Validation) {
                    BasicBlock* TrueBB = BI->getSuccessor(0);
                    BasicBlock* FalseBB = BI->getSuccessor(1);

                    bool errorInTrueBranch = DetermineErrorBranch(Validation);

                    if (errorInTrueBranch) {
                        retValueBB[retValue].insert(TrueBB);
                    }
                    else {
                        retValueBB[retValue].insert(FalseBB);
                    }
                    //DirectErrorBBs.insert(BI->getParent());
                }
            }
        }
    }

    std::set<BasicBlock*> BackReachable;
    std::vector<BasicBlock*> BackWorkList;
    std::set<BasicBlock*> SinkBlocks;

    for (ReturnInst* RI : TaintedReturns) {
        SinkBlocks.insert(RI->getParent());
    }

    for (BasicBlock* BB : SinkBlocks) {
        BackReachable.insert(BB);
        BackWorkList.push_back(BB);
    }


    while (!BackWorkList.empty()) {
        BasicBlock* CurrentBB = BackWorkList.back();
        BackWorkList.pop_back();

        for (BasicBlock* Pred : predecessors(CurrentBB)) {
            if (BackReachable.insert(Pred).second) {
                BackWorkList.push_back(Pred);
            }
        }
    }
    for (auto& pair : retValueBB) {
        std::queue<BasicBlock*> BBWorkList;
        std::set<BasicBlock*> DirectErrorBBs = pair.second;
        std::set<BasicBlock*> Visited;
        for (BasicBlock* DirectErrorBB : DirectErrorBBs) {
            BBWorkList.push(DirectErrorBB);
            Visited.insert(DirectErrorBB);
        }

        while (!BBWorkList.empty()) {
            BasicBlock* CurrentBB = BBWorkList.front();
            BBWorkList.pop();
            for (BasicBlock* Succ : successors(CurrentBB)) {
                if (Visited.count(Succ)) continue;
                if (BackReachable.count(Succ)) {
                    BBWorkList.push(Succ);
                    Visited.insert(Succ);
                }
            }
        }
        pair.second.insert(Visited.begin(), Visited.end());
    }

    // TODO handle release in ErrorBB
    for (auto& pair : retValueBB) {
        Value* ret = pair.first;
        retFunction[F].insert(ret);
        std::vector<FreePointInfo> NodeFreePoints;

        for (BasicBlock* BB : pair.second) {
            FindDirectFreePoints(BB, NodeFreePoints);
            FindReleaseWrapperFreePoints(BB, NodeFreePoints);
            FindExternalFreePoints(BB, NodeFreePoints);
            //The conditional release corresponding to the error return.
            FindConditionReleaseWrapperFreePoints(ret,NodeFreePoints);
        }
        for (const FreePointInfo& FreePoint : NodeFreePoints) {
                
                retFreePoint[ret].push_back(FreePoint);
                errs()<<"find condition release in "<<F->getName()<<" ";
                
        }
        //has connect with Arg?
        ConditionReleaseWrapperAnalysis(ret,std::move(NodeFreePoints));
    }
    return true;
}
*/

void TaintPass::FindConditionReleaseWrapperFreePoints(Value *V, std::vector<FreePointInfo> &FreePoints){
    // all error return freepoint

    CallInst *CI = dyn_cast<CallInst>(V);
    Function *ParentF=CI->getFunction();
    if(!CI){
        return;
    }
    Function *Callee = CI->getCalledFunction();
    std::set<Function*> CalledFunction;
    if (Callee) {
        CalledFunction.insert(Callee);
    }else{
        auto Callees = Ctx->Callees.find(CI);
        if (Callees != Ctx->Callees.end())
        for (Function *PotentialCallee : Callees->second){
            CalledFunction.insert(PotentialCallee);
        }
    }
    
    for(Function* F:CalledFunction){
        for(Value* retValue:retFunction[F]){
            for(const ConditionReleaseWrapper& CRW:retConditionReleaseWrapper[retValue]){
                std::string freeType = "condition_release[" + 
                      CRW.path + "]"+" when condition fail of "+F->getName().str()\
                      +" in "+ParentF->getName().str();

        
      
    
                Value *BasePtr = CI->getArgOperand(CRW.argIdx);           
                FreePointInfo FreePoint(CI, BasePtr, CI->getFunction(), CI->getParent(), CI, freeType);
                FreePoint.FieldPath=CRW.FiledPath;

                FreePoints.push_back(FreePoint);
                retConditionFailFreePoints[V].insert(FreePoint);

                errs() << "  Found condition free (indirect/direct): " << F->getName()
                << " in Function " << CI->getFunction()->getName() << "\n";
            }
        }
    }
    
}

// ========== CFG Construction Functions ========== 

void TaintPass::IdentifyErrorHandlingPaths(Function *F) {
    if (F->isDeclaration()) return;
    
    // Heuristic: If function name contains "release", "free", etc., consider all blocks
    if (F->getName().contains("release") || F->getName().contains("free") ||
        F->getName().contains("remove") || F->getName().contains("destruct") || 
        F->getName().contains("put") || F->getName().contains("exit")) {
        for (auto &BB : *F) {
            ErrorHandlingBlocks.insert(&BB);
        }
        return;
    }

    std::map<Value*, CallInst*> ErrorReturnSources;
    std::set<Value*> TaintedValues;
    std::set<Instruction*> ErrorValidations;
    std::set<BasicBlock*> DirectErrorBBs;
    
    // Step 1: Find error return sources
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                Function *Callee = CI->getCalledFunction();
                bool isErrorReturnCall = false;
                
                if (Callee && Ctx->ErrorReturnFuncs.count(Callee)) {
                    isErrorReturnCall = true;
                } else if (!Callee) {
                    auto Callees = Ctx->Callees.find(CI);
                    if (Callees != Ctx->Callees.end()) {
                        for (Function *PotentialCallee : Callees->second) {
                            if (Ctx->ErrorReturnFuncs.count(PotentialCallee)) {
                                isErrorReturnCall = true;
                                break;
                            }
                        }
                    }
                }
                
                if (isErrorReturnCall && !CI->getType()->isVoidTy()) {
                    ErrorReturnSources[CI] = CI;
                    TaintedValues.insert(CI);
                }
                
                // NPD Source Logic
                if (CurrentMode == MODE_NPD) {
                    bool isSource = false;
                    if (Callee) {
                        if (NRAnalyzer.Result.mayReturnNull(Callee)) isSource = true;
                    } else {
                        if (Ctx->Callees.count(CI)) {
                            for (Function *T : Ctx->Callees[CI]) {
                                if (NRAnalyzer.Result.mayReturnNull(T)) {
                                    isSource = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (isSource) {
                        TaintedValues.insert(CI);
                        ErrorReturnSources[CI] = CI;
                        ErrorHandlingBlocks.insert(&BB);
                        DirectErrorBBs.insert(&BB);
                    }
                }
            }
        }
    }
    
    // Proceed even if sources empty? No, we need sources to find validations.
    // if (ErrorReturnSources.empty()) return;
    
    if (F->getName().contains("__mlx5_ib_add")) {
        errs() << "DEBUG: IdentifyErrorHandlingPaths " << F->getName() << "\n";
        errs() << "  Sources: " << ErrorReturnSources.size() << "\n";
    }
    
    // Step 2: Taint propagation to find error validation points
    if (!ErrorReturnSources.empty()) {
        std::queue<Value*> WorkList;
        for (auto &Source : ErrorReturnSources) {
            WorkList.push(Source.first);
        }
    
        while (!WorkList.empty()) {
            Value *TaintedValue = WorkList.front();
            WorkList.pop();
            
            for (User *U : TaintedValue->users()) {
                if (Instruction *I = dyn_cast<Instruction>(U)) {
                    if (!I->getParent() || I->getParent()->getParent() != F) continue;
                    if (TaintedValues.count(I)) continue;
                    
                    bool NewTaint = false;
                    
                    if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
                        if (LI->getPointerOperand() == TaintedValue) NewTaint = true;
                    } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                        if (SI->getValueOperand() == TaintedValue) {
                            Value *Ptr = SI->getPointerOperand();
                            if (!TaintedValues.count(Ptr)) {
                                TaintedValues.insert(Ptr);
                                WorkList.push(Ptr);
                            }
                        }
                    } else if (BitCastInst *BC = dyn_cast<BitCastInst>(I)) {
                        if (BC->getOperand(0) == TaintedValue) NewTaint = true;
                    } else if (PHINode *PN = dyn_cast<PHINode>(I)) {
                        for (Value *Inc : PN->incoming_values()) {
                            if (Inc == TaintedValue) {
                                NewTaint = true;
                                break;
                            }
                        }
                    } else if (ICmpInst *Cmp = dyn_cast<ICmpInst>(I)) {
                        if (Cmp->getOperand(0) == TaintedValue || Cmp->getOperand(1) == TaintedValue) {
                            ErrorValidations.insert(Cmp);
                            NewTaint = true;
                        }
                    } else if (CallInst *CI = dyn_cast<CallInst>(I)) {
                        Function *Callee = CI->getCalledFunction();
                        if (Callee) {
                            StringRef Name = Callee->getName();
                            if (Name.contains("IS_ERR") || Name.contains("PTR_ERR")) {
                                for (unsigned i = 0; i < CI->arg_size(); i++) {
                                    if (CI->getArgOperand(i) == TaintedValue) {
                                        ErrorValidations.insert(CI);
                                        NewTaint = true;
                                        break;
                                    }
                                }
                            }
                        }
                        for (unsigned i = 0; i < CI->arg_size(); i++) {
                            if (CI->getArgOperand(i) == TaintedValue) {
                                if (!CI->getType()->isVoidTy()) NewTaint = true;
                                break;
                            }
                        }
                    }
                    
                    if (NewTaint) {
                        TaintedValues.insert(I);
                        WorkList.push(I);
                    }
                }
            }
        }
    }
    
    // Step 3: Identify error handling basic blocks based on error validation points
    
    //----new 
    std::set<llvm::BasicBlock*>  BIBB;
    for (Instruction *Validation : ErrorValidations) {
        for (User *U : Validation->users()) {
            if (BranchInst *BI = dyn_cast<BranchInst>(U)) {
                if (BI->isConditional() && BI->getCondition() == Validation) {
                    BasicBlock *TrueBB = BI->getSuccessor(0);
                    BasicBlock *FalseBB = BI->getSuccessor(1);
                    
                    bool errorInTrueBranch = DetermineErrorBranch(Validation);
                    
                    if (errorInTrueBranch) {
                        DirectErrorBBs.insert(TrueBB);
                    } else {
                        DirectErrorBBs.insert(FalseBB);
                    }
                    BIBB.insert(BI->getParent());
                }
            }
        }
    }
    
    // Step 4: Identify Sink Blocks (Return negative)
    std::set<BasicBlock*> SinkBlocks;
    for (auto &BB : *F) {
        if (ReturnInst *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
            Value *RetVal = RI->getReturnValue();
            if (RetVal) {
                if (F->getName().contains("__mlx5_ib_add")) {
                     errs() << "DEBUG: ReturnInst in __mlx5_ib_add: " << *RI << "\n";
                     errs() << "       RetVal: " << *RetVal << " Type: " << *RetVal->getType() << "\n";
                }

                if (ConstantInt *CI = dyn_cast<ConstantInt>(RetVal)) {
                    if (CI->isNegative()) SinkBlocks.insert(&BB);
                } else if (PHINode *PN = dyn_cast<PHINode>(RetVal)) {
                    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
                        Value *IV = PN->getIncomingValue(i);
                        if (ConstantInt *CI = dyn_cast<ConstantInt>(IV)) {
                            if (CI->isNegative()) {
                                SinkBlocks.insert(PN->getIncomingBlock(i));
                            }
                        }
                    }
                } else if (LoadInst *LI = dyn_cast<LoadInst>(RetVal)) {
                    Value *Ptr = LI->getPointerOperand();
                    // Handle simple load from alloca (local variable)
                    if (isa<AllocaInst>(getBasePointer(Ptr))) {
                        for (User *U : Ptr->users()) {
                            if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
                                // Ensure we are storing TO the pointer, not storing the pointer
                                if (SI->getPointerOperand() == Ptr) {
                                    Value *StoredVal = SI->getValueOperand();
                                    if (ConstantInt *CI = dyn_cast<ConstantInt>(StoredVal)) {
                                        if (CI->isNegative()) {
                                            SinkBlocks.insert(SI->getParent());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Step 5: Backward Reachability from Sink Blocks
    std::set<BasicBlock*> BackReachable;
    std::vector<BasicBlock*> BackWorkList;
    for (BasicBlock *BB : SinkBlocks) {
        BackReachable.insert(BB);
        BackWorkList.push_back(BB);
    }
    
    while (!BackWorkList.empty()) {
        BasicBlock *CurrentBB = BackWorkList.back();
        BackWorkList.pop_back();
        
        for (BasicBlock *Pred : predecessors(CurrentBB)) {
            if (BackReachable.insert(Pred).second) {
                BackWorkList.push_back(Pred);
            }
        }
    }

    // Step 6: Forward Reachability from Direct Error Blocks (constrained by BackReachable)
    std::queue<BasicBlock*> BBWorkList;
    std::set<BasicBlock*> Visited;
    
    for (BasicBlock *DirectErrorBB : DirectErrorBBs) {
        bool satisfyConstraint = (CurrentMode == MODE_NPD) ? true : BackReachable.count(DirectErrorBB);
        if (satisfyConstraint) {
            BBWorkList.push(DirectErrorBB);
            Visited.insert(DirectErrorBB);
            ErrorHandlingBlocks.insert(DirectErrorBB);
        }
    }
    
    while (!BBWorkList.empty()) {
        BasicBlock *CurrentBB = BBWorkList.front();
        BBWorkList.pop();
        
        for (BasicBlock *Succ : successors(CurrentBB)) {
            if (Visited.count(Succ)) continue;
            
            // Only add if it can reach error return (Backward constraint)
            // For NPD, we explore forward freely (pruning happens during analysis)
            bool satisfyConstraint = (CurrentMode == MODE_NPD) ? true : BackReachable.count(Succ);
            
            if (satisfyConstraint) {
                BBWorkList.push(Succ);
                Visited.insert(Succ);
                ErrorHandlingBlocks.insert(Succ);
            }
        }
    }
    ErrorHandlingBlocks.insert(BIBB.begin(),BIBB.end());
    
    // Fallback: If no direct error blocks found but we have sink blocks, 
    // assume all backward reachable blocks are relevant (conservative).
    
    if (DirectErrorBBs.empty() && !BackReachable.empty()) {
        for (BasicBlock *BB : BackReachable) {
            ErrorHandlingBlocks.insert(BB);
        }
    }
    
    
    // DEBUG PRINT (Final)
    if (F->getName().contains("__mlx5_ib_add")) {
        errs() << "  DirectBBs: " << DirectErrorBBs.size() << "\n";
        errs() << "  SinkBlocks: " << SinkBlocks.size() << "\n";
        errs() << "  BackReachable: " << BackReachable.size() << "\n";
        errs() << "  ErrorBBs: " << ErrorHandlingBlocks.size() << "\n";
    }
}

bool TaintPass::DetermineErrorBranch(Instruction *Validation) {
    if (ICmpInst *Cmp = dyn_cast<ICmpInst>(Validation)) {
        if (Cmp->getOperand(0)->getType()->isPointerTy() || 
            Cmp->getOperand(1)->getType()->isPointerTy()) {
            if (isa<ConstantPointerNull>(Cmp->getOperand(0)) || 
                isa<ConstantPointerNull>(Cmp->getOperand(1))) {
                return Cmp->getPredicate() == CmpInst::ICMP_EQ;
            }
        } else {
            if (Cmp->getPredicate() == CmpInst::ICMP_SLT) {
                if (ConstantInt *CI = dyn_cast<ConstantInt>(Cmp->getOperand(1))) {
                    if (CI->isZero()) return true;
                }
            } else if (Cmp->getPredicate() == CmpInst::ICMP_NE) {
                if (ConstantInt *CI = dyn_cast<ConstantInt>(Cmp->getOperand(1))) {
                    if (CI->isZero()) return true;
                }
            }
        }
    }
    return true;
}

bool TaintPass::IsLikelyErrorHandlingBlock(BasicBlock *BB) {
    if (BB->getName().contains("err") || BB->getName().contains("fail") || 
        BB->getName().contains("out") || BB->getName().contains("cleanup")) {
        return true;
    }
    
    for (auto &I : *BB) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            Function *Callee = CI->getCalledFunction();
            if (Callee) {
                StringRef Name = Callee->getName();
                if (Name.contains("free") || Name.contains("cleanup") || 
                    Name.contains("destroy") || Name.contains("release")) {
                    return true;
                }
            } else {
                // Check indirect call targets
                auto It = Ctx->Callees.find(CI);
                if (It != Ctx->Callees.end()) {
                    for (Function *Target : It->second) {
                        StringRef Name = Target->getName();
                        if (Name.contains("free") || Name.contains("cleanup") || 
                            Name.contains("destroy") || Name.contains("release")) {
                            if (BB->getParent()->getName() == "__mlx5_ib_add") {
                                errs() << "DEBUG: IsLikely found cleanup target " << Name 
                                       << " for indirect call in " << BB->getName() << "\n";
                            }
                            return true;
                        }
                    }
                } else {
                    if (BB->getParent()->getName() == "__mlx5_ib_add") {
                         errs() << "DEBUG: IsLikely found NO targets for indirect call in " 
                                << BB->getName() << "\n";
                    }
                }
            }
        } else if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
            Value *RetVal = RI->getReturnValue();
            if (RetVal) {
                if (ConstantInt *CI = dyn_cast<ConstantInt>(RetVal)) {
                    if (CI->isNegative()) return true;
                }
                if (isa<ConstantPointerNull>(RetVal)) return true;
            }
        }
    }
    
    unsigned InstCount = 0;
    bool HasReturn = false;
    for (auto &I : *BB) {
        InstCount++;
        if (isa<ReturnInst>(&I)) {
            HasReturn = true;
        }
    }
    
    if (HasReturn && InstCount < 8) {
        return true;
    }
    
    return false;
}



// ========== Extract Field Path from Free Point ========== 

vector<int> TaintPass::ExtractFieldPathFromFreePoint(const FreePointInfo &FreePoint) {
    // ✅ 直接返回FreePoint中存储的路径
    if (!FreePoint.FieldPath.empty()) {
        return FreePoint.FieldPath;
    }
    
    // ✅ 回退：从Value提取（用于非field-aware的情况）
    return extractFieldPathFromValue(FreePoint.FreedPointer);
}

// ========== Field-Sensitive Taint Propagation on CFG ========== 

void TaintPass::PropagateErrorTaintOnCFG(Module *M) {
    errs() << "=== Starting Free-Point-Centric Error Taint Propagation ===\n";
    
    if (CurrentMode == MODE_UAF) {
        IdentifyAllFreePoints(M);
    } else {
        IdentifyNPDSources(M);
    }
    
    for (const FreePointInfo &FreePoint : AllFreePoints) {
        errs() << "Analyzing Free Point: " << FreePoint.FreeType 
               << " in function " << FreePoint.ContainingFunc->getName() << "\n";
        AnalyzeIndividualFreePoint(FreePoint);
    }
    
    PrintFreePointStatistics();
    
    errs() << "=== Free-Point-Centric Error Taint Propagation Complete ===\n";
}

void TaintPass::IdentifyNPDSources(Module *M) {
    errs() << "Identifying NPD Sources (Functions returning NULL)...\n";
    AllFreePoints.clear();
    ErrorHandlingBlocks.clear();
    
    for (Function &F : *M) {
        if (F.isDeclaration()) continue;
        
        for (BasicBlock &BB : F) {
            ErrorHandlingBlocks.insert(&BB);
        }
        
        for (BasicBlock &BB : F) {
            for (Instruction &I : BB) {
                if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                    bool isSource = false;
                    Function *Callee = CI->getCalledFunction();
                    
                    if (Callee) {
                        if (NRAnalyzer.Result.mayReturnNull(Callee)) isSource = true;
                    } else {
                        if (Ctx->Callees.count(CI)) {
                            for (Function *T : Ctx->Callees[CI]) {
                                if (NRAnalyzer.Result.mayReturnNull(T)) {
                                    isSource = true;
                                    break;
                                }
                            }
                        }
                    }
                    
                    if (isSource) {
                        FreePointInfo FreePoint(CI, CI, &F, &BB, CI, "null_source");
                        AllFreePoints.push_back(FreePoint);
                    }
                }
            }
        }
    }
    errs() << "Total NPD sources identified: " << AllFreePoints.size() << "\n";
}

void TaintPass::IdentifyAllFreePoints(Module *M) {
    errs() << "Identifying all free points in error handling CFG...\n";
    
    AllFreePoints.clear();
    
    // Ensure ErrorHandlingBlocks is populated
    if (ErrorHandlingBlocks.empty()) {
        for (Function &F : *M) {
            IdentifyErrorHandlingPaths(&F);
        }
    }
    
    for (BasicBlock *BB : ErrorHandlingBlocks) {
        std::vector<FreePointInfo> NodeFreePoints;
        
        FindDirectFreePoints(BB, NodeFreePoints);
        FindReleaseWrapperFreePoints(BB, NodeFreePoints);
        FindExternalFreePoints(BB, NodeFreePoints);
        
        for (const FreePointInfo &FreePoint : NodeFreePoints) {
            AllFreePoints.push_back(FreePoint);
        }
    }
    //Handle conditional call situations
    //std::map<Value*,std::set<FreePointInfo>> retFreePoint
    for(auto& pair :retConditionFailFreePoints){
        for(const FreePointInfo& refFreePoint:pair.second){
            errs()<<refFreePoint.FreeType<<"\n";
            AllFreePoints.push_back(refFreePoint);
        }  
    }
    errs() << "Total free points identified: " << AllFreePoints.size() << "\n";
}

void TaintPass::FindDirectFreePoints(BasicBlock *BB, std::vector<FreePointInfo> &FreePoints) {
    static std::set<StringRef> MemFreeAPIs = {
        "kfree", "vfree", "free", "kmem_cache_free", "kzfree",
        "dma_free_coherent", "kvfree"
    };
    
    for (auto &I : *BB) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            Function *Callee = CI->getCalledFunction();
            if (Callee) {
                StringRef CalleeName = Callee->getName();
                if (MemFreeAPIs.count(CalleeName) && CI->arg_size() > 0) {
                    Value *FreedPtr = CI->getArgOperand(0);
                    
                    FreePointInfo FreePoint(CI, FreedPtr, BB->getParent(), BB, CI, "direct_free");
                    FreePoints.push_back(FreePoint);
                    
                    errs() << "  Found direct free: " << CalleeName 
                           << " in BB " << BB->getParent()->getName() << "\n";
                }
            }
        }
    }
}

void TaintPass::FindReleaseWrapperFreePoints(BasicBlock *BB, 
                                             std::vector<FreePointInfo> &FreePoints) {
    for (auto &I : *BB) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            // Collect all potential callees (direct + indirect)
            std::vector<Function*> Callees;
            if (Function *DirectCallee = CI->getCalledFunction()) {
                Callees.push_back(DirectCallee);
            } else {
                auto It = Ctx->Callees.find(CI);
                if (It != Ctx->Callees.end()) {
                    for (Function *F : It->second) {
                        Callees.push_back(F);
                    }
                }
            }
            
            for (Function *Callee : Callees) {
                if (!Callee) continue;
                
                // Use RWAnalyzer result
                if (RWAnalyzer.Result.isReleaseWrapper(Callee)) {
                    std::string CalleeName = Callee->getName().str();
                    
                    // ✅ 查找field-aware结果
                    auto funcIt = RWAnalyzer.Result.GlobalReleaseTransitMap.find(CalleeName);
                    if (funcIt != RWAnalyzer.Result.GlobalReleaseTransitMap.end()) {
                        
                        // ✅ 为每个参数的每个ReleaseSummary创建FreePoint
                        for (auto& argEntry : funcIt->second) {
                            int argIdx = argEntry.first;
                            
                            if (argIdx >= (int)CI->arg_size()) continue;
                            
                            Value *BasePtr = CI->getArgOperand(argIdx);
                            
                            for (ReleaseSummary* RS : argEntry.second) {
                                std::string freeType = "field_aware_wrapper[" + 
                                                      RS->getFieldAccessString() + "]";
                                
                                FreePointInfo FreePoint(CI, BasePtr, BB->getParent(), BB, CI, freeType);
                                
                                // ✅ 核心：直接存储字段路径
                                FreePoint.FieldPath = RS->getFieldPath();
                                
                                FreePoints.push_back(FreePoint);
                                
                                errs() << "  Found wrapper free (indirect/direct): " << CalleeName 
                                       << " in BB " << BB->getParent()->getName() << "\n";
                                printInstruction(CI);
                            }
                        }
                    }
                }
            }
        }
    }
}

void TaintPass::FindExternalFreePoints(BasicBlock *BB, std::vector<FreePointInfo> &FreePoints) {
    static std::set<StringRef> MemFreeAPIs = {
        "kfree", "vfree", "free", "kmem_cache_free", "kzfree",
        "dma_free_coherent", "kvfree"
    };
    
    std::set<Function*> Visited;
    
    for (auto &I : *BB) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            Function *Callee = CI->getCalledFunction();
            
            if (Callee && !Callee->isDeclaration() && Visited.insert(Callee).second) {
                for (auto &CalleeBB : *Callee) {
                    for (auto &CalleeI : CalleeBB) {
                        if (CallInst *CalleeCI = dyn_cast<CallInst>(&CalleeI)) {
                            Function *CalleeCallee = CalleeCI->getCalledFunction();
                            if (CalleeCallee) {
                                StringRef Name = CalleeCallee->getName();
                                
                                if (MemFreeAPIs.count(Name) && CalleeCI->arg_size() > 0) {
                                    Value *FreedArg = CalleeCI->getArgOperand(0);
                                    Value *MappedArg = nullptr;
                                    if (Argument *Arg = dyn_cast<Argument>(FreedArg)) {
                                        if (Arg->getParent() == Callee) {
                                            int ArgNo = Arg->getArgNo();
                                            if (ArgNo < (int)CI->arg_size()) {
                                                MappedArg = CI->getArgOperand(ArgNo);
                                            }
                                        }
                                    }
                                    if (MappedArg) {
                                        FreePointInfo FreePoint(CI, MappedArg, BB->getParent(), BB, CI, "external_free");
                                        FreePoints.push_back(FreePoint);
                                    }
                                }
                                
                                if (RWAnalyzer.Result.isReleaseWrapper(CalleeCallee)) {
                                    std::string WrapperName = Name.str();
                                    auto it = RWAnalyzer.Result.GlobalReleaseTransitMap.find(WrapperName);
                                    if (it != RWAnalyzer.Result.GlobalReleaseTransitMap.end()) {
                                        for (auto &entry : it->second) {
                                            int wrapperArgIdx = entry.first;
                                            if (wrapperArgIdx >= (int)CalleeCI->arg_size()) continue;
                                            Value *PassedArg = CalleeCI->getArgOperand(wrapperArgIdx);
                                            if (Argument *Arg = dyn_cast<Argument>(PassedArg)) {
                                                if (Arg->getParent() == Callee) {
                                                    int CalleeArgNo = Arg->getArgNo();
                                                    if (CalleeArgNo < (int)CI->arg_size()) {
                                                        Value *CallerArg = CI->getArgOperand(CalleeArgNo);
                                                        for (ReleaseSummary *RS : entry.second) {
                                                            std::string type = "external_wrapper[" + RS->getFieldAccessString() + "]";
                                                            FreePointInfo FreePoint(CI, CallerArg, BB->getParent(), BB, CI, type);
                                                            FreePoint.FieldPath = RS->getFieldPath();
                                                            FreePoints.push_back(FreePoint);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

void TaintPass::AnalyzeIndividualFreePoint(const FreePointInfo &FreePoint) {
    CurrentFreePointUAFFound = false;
    CurrentFreePoint = &FreePoint;

    vector<int> fieldPath = ExtractFieldPathFromFreePoint(FreePoint);
    
    TaintState initialTaint;
    initialTaint.TaintedValue = FreePoint.FreedPointer;
    initialTaint.FieldPath = fieldPath;
    
    initialTaint.SourceInst = FreePoint.TriggerInst;

    initialTaint.TaintType = FreePoint.FreeType;
    initialTaint.PropagationDepth = 0;
    initialTaint.addPathNode(FreePoint.FreeCall, "Initial taint source");
    
    PropagateFromFreePointWithFieldSensitivity(FreePoint, initialTaint);
}

void TaintPass::PropagateFromFreePointWithFieldSensitivity(
    const FreePointInfo &FreePoint,
    const TaintState &InitialTaint) {
    
    std::queue<std::pair<Instruction*, TaintState>> WorkList;
    std::set<std::pair<Instruction*, TaintState>> Visited;
    
    Instruction *NextInst = FreePoint.TriggerInst->getNextNode();
    
    if (!NextInst) {
        BasicBlock *BB = FreePoint.TriggerInst->getParent();
        for (BasicBlock *Succ : successors(BB)) {
            if (ErrorHandlingBlocks.count(Succ)) {
                WorkList.push({&Succ->front(), InitialTaint});
            }
        }
    } else {
        WorkList.push({NextInst, InitialTaint});
    }
    
    while (!WorkList.empty()) {
        if (CurrentFreePointUAFFound) break;

        auto [CurrentInst, CurrentTaint] = WorkList.front();
        WorkList.pop();
        
        if (Visited.count({CurrentInst, CurrentTaint})) {
            continue;
        }
        Visited.insert({CurrentInst, CurrentTaint});
        
        if (CurrentTaint.PropagationDepth >= MAX_PROPAGATION_DEPTH) {
            continue;
        }
        
        BasicBlock *CurrentBB = CurrentInst->getParent();
        PropagateToSuccessorWithFieldSensitivity(CurrentInst, CurrentBB, CurrentTaint, WorkList);
    }
}

void TaintPass::CheckCallInstWithDerefSummary(
    CallInst *CI, 
    const TaintState &Taint,
    AliasContext *aliasCtx) {
    
    if (!CI) return;
    
    Function *DirectCallee = CI->getCalledFunction();
    
    // Helper lambda for Double Free checks
    auto CheckDoubleFree = [&](Function *F) {
        if (!F) return;
        StringRef CalleeName = F->getName();
        
        static std::set<StringRef> MemFreeAPIs = {
            "kfree", "vfree", "free", "kmem_cache_free", 
            "kzfree", "dma_free_coherent", "kvfree"
        };
        
        // 1. Direct Double Free
        if (MemFreeAPIs.count(CalleeName) && CI->arg_size() > 0) {
            Value *FreedPtr = CI->getArgOperand(0);
            if (IsFieldAccessMatching(FreedPtr, Taint, aliasCtx)) {
                ReportUAFForFreePoint("double-free", CI, Taint);
            }
        }
        
        // 2. Wrapper Double Free
        if (RWAnalyzer.Result.isReleaseWrapper(F)) {
            if (F->getName().contains("mlx5r_umr_resource_cleanup")) {
                errs() << "DEBUG: Checking Wrapper mlx5r_umr_resource_cleanup in " << CI->getFunction()->getName() << "\n";
                if (Taint.TaintedValue) errs() << "  Taint: " << *Taint.TaintedValue << "\n";
                else errs() << "  Taint is NULL\n";
            }
            
            std::string CName = CalleeName.str();
            auto it = RWAnalyzer.Result.GlobalReleaseTransitMap.find(CName);
            if (it != RWAnalyzer.Result.GlobalReleaseTransitMap.end()) {
                for (auto &entry : it->second) {
                    int argIdx = entry.first;
                    if (argIdx >= (int)CI->arg_size()) continue;
                    
                    Value *Arg = CI->getArgOperand(argIdx);
                    if (!Arg->getType()->isPointerTy()) continue;
                    
                    if (CI->getFunction()->getName().contains("__mlx5_ib_add")) {
                         bool alias = IsAliased(getBasePointer(Arg), getBasePointer(Taint.TaintedValue), aliasCtx);
                         if (!alias) {
                             errs() << "DEBUG: IsAliased FAILED in CheckDoubleFree\n";
                             errs() << "  ArgBase: " << *getBasePointer(Arg) << "\n";
                             errs() << "  TaintBase: " << *getBasePointer(Taint.TaintedValue) << "\n";
                         } else {
                             errs() << "DEBUG: IsAliased PASSED\n";
                         }
                    }
                    
                    if (!IsAliased(getBasePointer(Arg), getBasePointer(Taint.TaintedValue), aliasCtx))
                        continue;

                    vector<int> argPath = extractFieldPathFromValue(Arg);
                    vector<int> BasePtrPath = extractFieldPathFromValue(Taint.TaintedValue);
                    BasePtrPath.insert(BasePtrPath.end(),Taint.FieldPath.begin(),Taint.FieldPath.end());

                    for (ReleaseSummary *RS : entry.second) {
                        vector<int> wrapperPath = RS->getFieldPath();
                        vector<int> fullFreedPath = argPath;
                        fullFreedPath.insert(fullFreedPath.end(), wrapperPath.begin(), wrapperPath.end());
                        //Taint.FieldPath should be set to all
                        
                        if (fieldPathsOverlap(fullFreedPath, BasePtrPath)) {
                            ReportUAFForFreePoint("double-free-wrapper", CI, Taint);
                            return; 
                        }
                    }
                }
            }
        }
    };
    
    // Check Direct Call
    if (DirectCallee) {
        CheckDoubleFree(DirectCallee);
        if (!DirectCallee->isDeclaration()) {
            CheckCallWithCallee(CI, DirectCallee, Taint, aliasCtx);
        }
    }
    
    // Check Indirect Call
    if (!DirectCallee || DirectCallee->isDeclaration()) {
        auto CalleeIt = Ctx->Callees.find(CI);
        if (CalleeIt != Ctx->Callees.end()) {
            for (Function *PotentialCallee : CalleeIt->second) {
                CheckDoubleFree(PotentialCallee); // Check indirect target
                if (PotentialCallee && !PotentialCallee->isDeclaration()) {
                    CheckCallWithCallee(CI, PotentialCallee, Taint, aliasCtx);
                }
            }
        } else {
             if (CI->getFunction()->getName().contains("__mlx5_ib_add")) {
                 errs() << "DEBUG: No targets in Ctx->Callees for call: " << *CI << "\n";
             }
        }
    }
    
    // 如果没有 callee 信息，进行保守检查
    if (!DirectCallee && (!Ctx || !Ctx->Callees.count(CI))) {
        for (unsigned i = 0; i < CI->arg_size(); i++) {
            Value *Arg = CI->getArgOperand(i);
            if (Arg->getType()->isPointerTy()) {
                if (IsFieldAccessMatching(Arg, Taint, aliasCtx)) {
                    ReportUAFForFreePoint("call_unknown", CI, Taint);
                    break;
                }
            }
        }
    }
}

void TaintPass::CheckCallWithCallee(
    CallInst *CI,
    Function *Callee,
    const TaintState &Taint,
    AliasContext *aliasCtx) {
    
    if (!CI || !Callee) return;
    
    // 检查每个参数是否与污点匹配
    for (unsigned i = 0; i < CI->arg_size() && i < Callee->arg_size(); i++) {
        Value *Arg = CI->getArgOperand(i);
        
        if (!Arg->getType()->isPointerTy()) continue;
        
        // 检查参数是否与污点匹配
        if (!IsFieldAccessMatching(Arg, Taint, aliasCtx)) {
            continue;
        }
        
        // 参数与污点匹配，检查 callee 是否会解引用这个参数
        std::vector<DereferenceSummary*> derefPaths = 
            DerefAnalyzer.Result.getDerefPaths(Callee, i);
        
        // 提取参数相对于污点的字段路径
        std::vector<int> argPath = extractFieldPathFromValue(Arg);
        std::vector<int> taintPath = extractFieldPathFromValue(Taint.TaintedValue);
        
        // 计算参数相对于污点的偏移路径
        std::vector<int> relativePath = ComputeRelativeFieldPath(taintPath, argPath, {});
        
        if (derefPaths.empty()) {
            // 没有解引用信息
            
            // 检查是否是已知的危险函数
            StringRef CalleeName = Callee->getName();
            if (IsDangerousFunction(CalleeName)) {
                // 危险函数，保守报告
                errs() << "    [DerefCheck] Dangerous function " << CalleeName 
                       << " with no summary, conservative report\n";
                ReportUAFForFreePoint("call_dangerous_no_summary", CI, Taint);
            }
            // 其他函数没有解引用信息，可能不解引用，跳过
            continue;
        }
        
        // 有解引用信息，精确检查
        // errs() << "    [DerefCheck] Checking " << Callee->getName() 
        //        << " arg[" << i << "] with " << derefPaths.size() << " deref paths\n";
        
        for (DereferenceSummary *DS : derefPaths) {
            // 计算完整的解引用路径: relative_path + deref_path
            std::vector<int> fullDerefPath = MergeFieldPaths(relativePath, DS->FieldAccessPath);
            
            // errs() << "      Checking deref path: ";
            // printFieldPath(fullDerefPath);
            // errs() << " against taint path: ";
            // printFieldPath(Taint.FieldPath);
            // errs() << "\n";
            
            // 检查解引用路径是否与污点路径重叠
            if (Taint.FieldPath.empty()) {
                // 整个对象被释放，任何解引用都是 UAF
                std::string useType = "call_deref_" + DS->DerefType;
                if (DS->IsWrite) useType += "_write";
                
                errs() << "      -> UAF detected (entire object freed)\n";
                ReportUAFForFreePoint(useType, CI, Taint);
                return;  // 只报告一次
            }
            
            if (fieldPathsOverlap(fullDerefPath, Taint.FieldPath)) {
                std::string useType = "call_deref_" + DS->DerefType;
                if (DS->IsWrite) useType += "_write";
                
                errs() << "      -> UAF detected (field path overlap)\n";
                ReportUAFForFreePoint(useType, CI, Taint);
                return;  // 只报告一次
            }
        }
        
        // errs() << "      -> No UAF (no overlapping deref paths)\n";
    }
}

// CheckBBWithFieldSensitivity removed (redundant with ProcessInstructionsInRange)

bool TaintPass::IsStoreToFreedMemory(StoreInst *SI, const TaintState &Taint, 
                                     AliasContext *aliasCtx) {
    Value *StorePtr = SI->getPointerOperand();
    Value *StoredVal = SI->getValueOperand();
    
    // ========== 情况1：检查是否是"给指针变量赋值" ========== 
    // 例如：store ptr_type new_val, ptr_type* %ptr_var
    
    // 提取基指针
    Value *storeBase = getBasePointer(StorePtr);
    Value *taintBase = getBasePointer(Taint.TaintedValue);
    
    // 如果 StorePtr 是一个 AllocaInst（栈上的指针变量）
    if (AllocaInst *AI = dyn_cast<AllocaInst>(storeBase)) {
        Type *allocatedType = AI->getAllocatedType();
        
        // ✅ 如果分配的是指针类型，这可能是在给指针变量赋值
        if (allocatedType->isPointerTy()) {
            // 检查被存储的值是否是"新的"指针（不是从污点派生的）
            
            // 1. 如果存储的是常量（包括 NULL, ERR_PTR 等），不是UAF
            // 这视为对指针变量的重新赋值（Sanitization）
            if (isa<Constant>(StoredVal)) {
                errs() << "      Store to pointer variable with constant, not UAF\n";
                return false;
            }
            
            // 2. 如果存储的值不是污点派生的，不是UAF
            if (!IsAliased(StoredVal, Taint.TaintedValue, aliasCtx)) {
                errs() << "      Store to pointer variable with new value, not UAF\n";
                return false;
            }
        }
    }
    
    // ========== 情况2：检查是否需要解引用污染的指针 ========== 
    // 例如：store value, ptr_type %freed_ptr 或 store value, (gep %freed_ptr, idx)
    
    // 检查 StorePtr 是否派生自污染的指针
    // 例如：%1 = getelementptr %freed_ptr, 0, 2
    //       store value, %1
    
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(StorePtr)) {
        Value *gepBase = GEP->getPointerOperand();
        
        // 如果 GEP 的基地址是污染的，这是在访问已释放对象的字段
        if (IsFieldAccessMatching(gepBase, Taint, aliasCtx)) {
            errs() << "      Store through GEP of freed pointer, UAF detected\n";
            return true;
        }
    }
    
    // ========== 情况3：直接匹配检查 ========== 
    // 但要排除"给指针变量赋值"的情况
    
    // 检查 StorePtr 是否指向已释放的内存区域
    if (IsFieldAccessMatching(StorePtr, Taint, aliasCtx)) {
        // 进一步验证：检查指针层级
        Type *storePtrType = StorePtr->getType();
        
        // 如果 StorePtr 是 pointer-to-pointer (T**)，可能只是更新指针变量
        if (storePtrType->isPointerTy()) {
            Type *pointeeType = storePtrType->getPointerElementType();
            if (pointeeType->isPointerTy()) {
                // T** 类型：这是指向指针的指针
                // 需要检查是否真的在访问已释放的内存
                
                // 如果污点路径为空（整个对象被释放），且这是给指针变量赋值
                // 应该允许
                if (Taint.FieldPath.empty()) {
                    errs() << "      Store to pointer variable (T**), allowing\n";
                    return false;
                }
            }
        }
        
        errs() << "      Store matches freed memory, UAF detected\n";
        return true;
    }
    
    return false;
}

bool TaintPass::IsFieldAccessMatching(Value *AccessPtr, const TaintState &Taint, 
                                      AliasContext *aliasCtx) {
    if (!AccessPtr || !Taint.TaintedValue || !aliasCtx) return false;
    
    vector<int> accessPath = extractFieldPathFromValue(AccessPtr);
    Value *accessBase = getBasePointer(AccessPtr);
    Value *taintBase = getBasePointer(Taint.TaintedValue);
    
    if (!accessBase || !taintBase) return false;
    
    if (!IsAliased(accessBase, taintBase, aliasCtx)) {
        return false;
    }
    
    // ✅ 核心修改：空路径表示整个对象被释放
    if (Taint.FieldPath.empty()) {
        // 整个对象被释放，任何访问都匹配
        return true;
    }
    
    // ✅ 使用原有的fieldPathsOverlap函数即可
    bool overlap = fieldPathsOverlap(accessPath, Taint.FieldPath);
    
    return overlap;
}

bool TaintPass::ShouldPrunePath(BasicBlock *From, BasicBlock *To, const TaintState &Taint) {
    if (CurrentMode != MODE_NPD) return false;
    
    Instruction *Term = From->getTerminator();
    if (BranchInst *BI = dyn_cast<BranchInst>(Term)) {
        if (BI->isConditional()) {
            
            if (From->getParent()->getName().contains("huge_pte_alloc")) {
                 StringRef FromName = From->hasName() ? From->getName() : "(unnamed)";
                 StringRef ToName = To->hasName() ? To->getName() : "(unnamed)";
                 errs() << "DEBUG: ShouldPrunePath " << FromName << " -> " << ToName << "\n";
                 errs() << "  Taint: " << *Taint.TaintedValue << "\n";
                 if (ICmpInst *Cmp = dyn_cast<ICmpInst>(BI->getCondition())) {
                     errs() << "  Cond: " << *Cmp << "\n";
                 } else {
                     errs() << "  Cond is NOT ICmp: " << *BI->getCondition() << "\n";
                 }
            }

            if (ICmpInst *Cmp = dyn_cast<ICmpInst>(BI->getCondition())) {
                Value *Op0 = Cmp->getOperand(0);
                Value *Op1 = Cmp->getOperand(1);
                
                Value *Base0 = Op0;
                if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(Op0)) Base0 = PI->getOperand(0);
                
                Value *Base1 = Op1;
                if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(Op1)) Base1 = PI->getOperand(0);
                
                AliasContext *ctx = GetOrBuildFunctionAlias(From->getParent());
                
                bool op0Taint = IsAliased(Base0, Taint.TaintedValue, ctx);
                bool op1Taint = IsAliased(Base1, Taint.TaintedValue, ctx);
                
                bool op0Null = isa<ConstantPointerNull>(Op0) || (isa<ConstantInt>(Op0) && cast<ConstantInt>(Op0)->isZero());
                bool op1Null = isa<ConstantPointerNull>(Op1) || (isa<ConstantInt>(Op1) && cast<ConstantInt>(Op1)->isZero());
                
                if (From->getParent()->getName().contains("huge_pte_alloc")) {
                    errs() << "  Op0Taint: " << op0Taint << " Op1Null: " << op1Null << "\n";
                    errs() << "  Op1Taint: " << op1Taint << " Op0Null: " << op0Null << "\n";
                }
                
                if ((op0Taint && op1Null) || (op1Taint && op0Null)) {
                    if (Cmp->getPredicate() == CmpInst::ICMP_EQ) {
                        // if (ptr == NULL) -> False branch is Safe (ptr != NULL)
                        // Prune False branch
                        if (To == BI->getSuccessor(1)) return true;
                    } 
                    else if (Cmp->getPredicate() == CmpInst::ICMP_NE) {
                        // if (ptr != NULL) -> True branch is Safe
                        // Prune True branch
                        if (To == BI->getSuccessor(0)) return true;
                    }
                }
            }
        }
    }
    return false;
}

bool TaintPass::PointsTo(Value *Ptr, Value *Val, AliasContext *ctx) {
    if (!Ptr || !Val || !ctx) return false;
    AliasNode *NPtr = getNode(Ptr, ctx);
    AliasNode *NVal = getNode(Val, ctx);
    if (!NPtr || !NVal) return false;
    
    if (ctx->ToNodeMap.count(NPtr)) {
        auto &Edges = ctx->ToNodeMap[NPtr];
        if (Edges.count(-1)) {
            AliasNode *Target = Edges[-1];
            return Target == NVal;
        }
    }
    return false;
}

void TaintPass::CheckNPD(Instruction *I, Value *Ptr, const TaintState &Taint, AliasContext *aliasCtx) {
    if (IsAliased(Ptr, Taint.TaintedValue, aliasCtx)) {
        // Ignore "safe reads": loading the tainted pointer itself from memory.
        // This is represented by FieldPath ending with -1 (Points-To).
        bool isSafeRead = (!Taint.FieldPath.empty() && Taint.FieldPath.back() == -1);
        
        if (!isSafeRead) {
            ReportUAFForFreePoint("NPD", I, Taint);
        }
    }
}

void TaintPass::PropagateToSuccessorWithFieldSensitivity(
    Instruction *CurrentInst, 
    BasicBlock *CurrentBB,
    const TaintState &CurrentTaint,
    std::queue<std::pair<Instruction*, TaintState>> &WorkList) {
    
    TaintState newTaint = CurrentTaint;
    AliasContext *aliasCtx = GetOrBuildFunctionAlias(CurrentBB->getParent());
    
    BasicBlock::iterator It(CurrentInst);
    BasicBlock::iterator E = CurrentBB->end();
    Instruction *EndInst = nullptr;
    CallInst *FoundCall = nullptr;
    ReturnInst *FoundRet = nullptr;
    
    for (; It != E; ++It) {
        if (CallInst *CI = dyn_cast<CallInst>(&*It)) {
            FoundCall = CI;
            EndInst = CI;
            break;
        }
        if (ReturnInst *RI = dyn_cast<ReturnInst>(&*It)) {
            FoundRet = RI;
            EndInst = RI;
            break;
        }
    }
    
    Instruction *ProcessEndInst = (EndInst) ? EndInst->getNextNode() : nullptr;
    BasicBlock::iterator EndIt = ProcessEndInst ? ProcessEndInst->getIterator() : CurrentBB->end();
    ProcessInstructionsInRange(CurrentInst, EndIt, newTaint, aliasCtx, *CurrentFreePoint);
    
    if (CurrentFreePointUAFFound) return;
    if (!newTaint.TaintedValue) return;
    
    if (FoundCall) {
        if (FoundCall != newTaint.SourceInst) {
             // Direct Call
             if (Function *F = FoundCall->getCalledFunction()) {
                 PropagateToCallee(FoundCall, F, newTaint, WorkList);
             }
             // Indirect Call
             if (Ctx->Callees.count(FoundCall)) {
                 for (Function *F : Ctx->Callees[FoundCall]) {
                     PropagateToCallee(FoundCall, F, newTaint, WorkList);
                 }
             }
        }
        
        Instruction *Next = FoundCall->getNextNode();
        if (Next) {
            TaintState nextState = newTaint;
            nextState.PropagationDepth++;
            WorkList.push({Next, nextState});
        }
        return;
    }
    
    if (FoundRet) {
        PropagateFromCallee(CurrentBB, newTaint, WorkList);
        return;
    }
    
    newTaint.PropagationDepth++;
    
    Instruction *Term = CurrentBB->getTerminator();
    if (Term) {
        for (BasicBlock *Succ : successors(CurrentBB)) {
            if (ErrorHandlingBlocks.count(Succ)) {
                if (ShouldPrunePath(CurrentBB, Succ, newTaint)) continue;
                WorkList.push({&Succ->front(), newTaint});
            }
        }
    }
}

Instruction* TaintPass::ProcessInstructionsInRange(
    Instruction *Start, 
    BasicBlock::iterator EndIt,
    TaintState &Taint, 
    AliasContext *aliasCtx, 
    const FreePointInfo &FreePoint) {
    
    if (!Start) return nullptr;
    
    BasicBlock *BB = Start->getParent();
    BasicBlock::iterator It(Start);
    
    for (; It != EndIt; ++It) {
        Instruction &I = *It;
        if (CurrentFreePointUAFFound) break;

        // Load
        if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
            Value *LoadPtr = LI->getPointerOperand();
            
            if (CurrentMode == MODE_NPD) {
                CheckNPD(LI, LoadPtr, Taint, aliasCtx);
            } else {
                // Sanitization
                if (Taint.NullPtrs.count(LoadPtr)) continue;

                // UAF Check (Only for Heap Access)
                if (!isa<AllocaInst>(getBasePointer(LoadPtr))) {
                    if (IsFieldAccessMatching(LoadPtr, Taint, aliasCtx)) {
                        ReportUAFForFreePoint("load", LI, Taint);
                    }
                }
            }
            
            // Propagation Logic
            if (Taint.TaintedMem.count(LoadPtr)) {
                Taint.TaintedValue = LI;
                Taint.FieldPath.clear();
                Taint.addPathNode(LI, "Reloaded tainted value");
            } else {
                Value *PtrBase = getBasePointer(LoadPtr);
                Value *TaintBase = getBasePointer(Taint.TaintedValue);
                
                if (IsAliased(PtrBase, TaintBase, aliasCtx)) {
                    std::vector<int> ptrPath = extractFieldPathFromValue(LoadPtr);
                    std::vector<int> taintPath = extractFieldPathFromValue(Taint.TaintedValue);
                    taintPath.insert(taintPath.end(), Taint.FieldPath.begin(), Taint.FieldPath.end());
                    
                    bool isPrefix = true;
                    if (ptrPath.size() > taintPath.size()) isPrefix = false;
                    else {
                        for (size_t k = 0; k < ptrPath.size(); ++k) {
                            if (ptrPath[k] != taintPath[k]) { isPrefix = false; break; }
                        }
                    }
                    
                    if (isPrefix && ptrPath.size() < taintPath.size() && taintPath[ptrPath.size()] == -1) {
                        Taint.TaintedValue = LI;
                        std::vector<int> newPath;
                        for(size_t k = ptrPath.size() + 1; k < taintPath.size(); ++k) newPath.push_back(taintPath[k]);
                        Taint.FieldPath = newPath;
                        Taint.addPathNode(LI, "Loaded tainted value");
                    }
                }
            }
        }
        
        // Store
        else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
            Value *StoredVal = SI->getValueOperand();
            Value *StorePtr = SI->getPointerOperand();
            
            if (CurrentMode == MODE_NPD) {
                CheckNPD(SI, StorePtr, Taint, aliasCtx);
                
                // Explicit Sanitization (Overwrite)
                if (Taint.TaintedValue && 
                    (IsAliased(StorePtr, Taint.TaintedValue, aliasCtx) || 
                     PointsTo(StorePtr, Taint.TaintedValue, aliasCtx))) {
                     
                     // Only sanitize if the StoredVal is NOT null AND NOT the tainted value itself
                     bool isTaintedStore = IsAliased(StoredVal, Taint.TaintedValue, aliasCtx);
                     
                     if (!isTaintedStore && 
                         !isa<ConstantPointerNull>(StoredVal) && 
                         !(isa<ConstantInt>(StoredVal) && cast<ConstantInt>(StoredVal)->isZero())) {
                         
                         Taint.TaintedValue = nullptr; // Cleared
                         return nullptr; 
                     }
                }
            } else {
                // Sanitization Update
                if (isa<ConstantPointerNull>(StoredVal)) {
                    Taint.NullPtrs.insert(StorePtr);
                } else {
                    Taint.NullPtrs.erase(StorePtr);
                }
                
                // Store UAF Check
                if (IsStoreToFreedMemory(SI, Taint, aliasCtx)) {
                    ReportUAFForFreePoint("store", SI, Taint);
                }
            }
            
            // Propagation
            if (IsAliased(StoredVal, Taint.TaintedValue, aliasCtx)) {
                vector<int> ptrPath = extractFieldPathFromValue(StorePtr);
                // Prepend pointer path + deref to existing path
                ptrPath.push_back(-1);
                ptrPath.insert(ptrPath.end(), Taint.FieldPath.begin(), Taint.FieldPath.end());
                
                Taint.FieldPath = ptrPath;
                Taint.TaintedValue = StorePtr;
                Taint.TaintedMem.insert(StorePtr);
                Taint.addPathNode(SI, "Stored taint to memory");
            }
        }
        
        // GEP
        else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I)) {
            Value *Base = GEP->getPointerOperand();
            if (Base == Taint.TaintedValue) {
                if (GEPOperator *GEPO = dyn_cast<GEPOperator>(GEP)) {
                    int idx;
                    if (getGEPLayerIndex(GEPO, idx)) {
                        if (Taint.FieldPath.size() < 10) {
                            Taint.FieldPath.push_back(idx);
                            Taint.TaintedValue = GEP;
                            Taint.addPathNode(GEP, "Field index update");
                        }
                    }
                }
            }
        }
        

        
        // BitCast
        else if (BitCastInst *BC = dyn_cast<BitCastInst>(&I)) {
            if (IsAliased(BC->getOperand(0), Taint.TaintedValue, aliasCtx)) {
                Taint.TaintedValue = BC;
                Taint.addPathNode(BC, "Cast");
            }
        }
        
        // PHI
        else if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
            for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
                if (IsAliased(PHI->getIncomingValue(i), Taint.TaintedValue, aliasCtx)) {
                    Taint.TaintedValue = PHI;
                    Taint.addPathNode(PHI, "Phi merge");
                    break;
                }
            }
        }
        
        // Call
        else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
             if (CurrentMode == MODE_UAF) {
                 CheckCallInstWithDerefSummary(CI, Taint, aliasCtx);
             }
        }
    }
    return nullptr;
}

std::vector<int> TaintPass::ComputeRelativeFieldPath(
    const std::vector<int> &basePath,
    const std::vector<int> &fullPath,
    const std::vector<int> &taintPath) {
    
    // 如果 fullPath 是 basePath 的扩展
    if (fullPath.size() >= basePath.size()) {
        bool isExtension = true;
        for (size_t i = 0; i < basePath.size(); i++) {
            if (basePath[i] != fullPath[i]) {
                isExtension = false;
                break;
            }
        }
        
        if (isExtension) {
            // 提取额外的路径部分
            std::vector<int> extra(fullPath.begin() + basePath.size(), fullPath.end());
            // 合并到taint路径
            return MergeFieldPaths(extra, taintPath);
        }
    }
    
    // 默认返回原路径
    return taintPath;
}

void TaintPass::PropagateToCallee(
    CallInst *CallSite,
    Function *Callee,
    const TaintState &CurrentTaint,
    std::queue<std::pair<Instruction*, TaintState>> &WorkList) {
    
    if (!CallSite || !Callee || Callee->isDeclaration()) return;
    
    Function *Caller = CallSite->getFunction();
    AliasContext *callerCtx = GetOrBuildFunctionAlias(Caller);
    
    errs() << "    Propagating taint to callee " << Callee->getName() << "\n";
    
    for (unsigned i = 0; i < CallSite->arg_size() && i < Callee->arg_size(); i++) {
        Value *ActualArg = CallSite->getArgOperand(i);
        
        Value *actualBase = getBasePointer(ActualArg);
        Value *taintBase = getBasePointer(CurrentTaint.TaintedValue);
        
        if (IsAliased(actualBase, taintBase, callerCtx)) {
            Argument *FormalArg = Callee->getArg(i);
            
            std::vector<int> argFieldPath = extractFieldPathFromValue(ActualArg);
            std::vector<int> taintBasePath = extractFieldPathFromValue(CurrentTaint.TaintedValue);
            
            std::vector<int> relativePath = ComputeRelativeFieldPath(
                taintBasePath, argFieldPath, CurrentTaint.FieldPath
            );
            
            TaintState calleeTaint = CurrentTaint;
            calleeTaint.TaintedValue = FormalArg;
            calleeTaint.FieldPath = relativePath;
            calleeTaint.PropagationDepth = CurrentTaint.PropagationDepth + 1;
            calleeTaint.addPathNode(CallSite, "Passed as argument " + std::to_string(i) + " to Callee");
            
            calleeTaint.CallStack.push_back(CallSite);

            BasicBlock &EntryBB = Callee->getEntryBlock();
            // In virtual slicing, we might not check ErrorHandlingBlocks for callee entry?
            // If we want to restrict to error paths, we should check.
            // But if we want to explore callee for UAF/NPD, we should probably allow entry.
            // Let's check if EntryBB is in set.
            if (ErrorHandlingBlocks.count(&EntryBB)) {
                WorkList.push({&EntryBB.front(), calleeTaint});
                errs() << "      Mapped to formal argument " << i << "\n";
            }
        }
    }
}

void TaintPass::PropagateFromCallee(
    BasicBlock *CalleeExitBB,
    const TaintState &CurrentTaint,
    std::queue<std::pair<Instruction*, TaintState>> &WorkList) {
    
    if (CurrentTaint.CallStack.empty()) return;
    CallInst *CallSite = CurrentTaint.CallStack.back();
    
    Function *Caller = CallSite->getFunction();
    Function *Callee = CalleeExitBB->getParent();
    
    errs() << "    Propagating taint back from callee " << Callee->getName() 
           << " to caller " << Caller->getName() << "\n";
    
    TaintState callerTaint = CurrentTaint;
    callerTaint.CallStack.pop_back();
    Instruction *NextInst = CallSite->getNextNode();
    if (!NextInst) return; // End of block? Handle successor?
    // If NextInst is null, we should push successors of CallSite's block?
    // But CallSite is inside a block. If it is last, NextInst is null.
    // In that case, we should use PropagateToSuccessor logic for terminator?
    // But PropagateToSuccessor handles Terminators. CallSite is not terminator.
    // Unless InvokeInst.
    // If CallInst is last (impossible for well formed BB, needs terminator).
    
    // 1. Return Value
    if (ReturnInst *RI = dyn_cast<ReturnInst>(CalleeExitBB->getTerminator())) {
        Value *RetVal = RI->getReturnValue();
        if (RetVal && CurrentTaint.TaintedValue == RetVal) {
             callerTaint.TaintedValue = CallSite;
             callerTaint.addPathNode(CallSite, "Returned from Callee");
             WorkList.push({NextInst, callerTaint});
             return;
        }
    }
    
    // 2. Argument (Out-param)
    if (Argument *Arg = dyn_cast<Argument>(CurrentTaint.TaintedValue)) {
        if (Arg->getParent() == Callee) {
            int ArgNo = Arg->getArgNo();
            if (ArgNo < (int)CallSite->arg_size()) {
                Value *CallerOp = CallSite->getArgOperand(ArgNo);
                callerTaint.TaintedValue = CallerOp;
                callerTaint.addPathNode(CallSite, "Returned via argument");
                WorkList.push({NextInst, callerTaint});
            }
        }
    }
}

bool TaintPass::IsIndirectCall(CallInst *CI) {
    if (CI->getCalledFunction()) return false;
    return true;
}

void TaintPass::PrintFreePointStatistics() {
    std::map<std::string, int> freeTypeCounts;
    std::map<Function*, int> funcFreeCounts;
    
    for (const FreePointInfo &FP : AllFreePoints) {
        freeTypeCounts[FP.FreeType]++;
        funcFreeCounts[FP.ContainingFunc]++;
    }
    
    errs() << "\n=== Free Point Statistics ===\n";
    errs() << "Total Free Points: " << AllFreePoints.size() << "\n";
    
    errs() << "By Type:\n";
    for (auto &entry : freeTypeCounts) {
        errs() << "  " << entry.first << ": " << entry.second << "\n";
    }
    
    errs() << "Top Functions by Free Count:\n";
    std::vector<std::pair<Function*, int>> sortedFuncs(funcFreeCounts.begin(), funcFreeCounts.end());
    std::sort(sortedFuncs.begin(), sortedFuncs.end(), 
              [](const auto &a, const auto &b) { return a.second > b.second; });
    
    int count = 0;
    for (auto &entry : sortedFuncs) {
        if (count++ >= 10) break;
        errs() << "  " << entry.first->getName() << ": " << entry.second << "\n";
    }
    errs() << "==============================\n\n";
}

// ========== Bug Reporting ========== 

// Helper to find DIType for a Value
static DIType *findDIType(Value *V) {
    if (!V) return nullptr;
    Value *Base = getBasePointer(V);
    
    // Check users for dbg.declare/value
    for (User *U : Base->users()) {
        if (DbgVariableIntrinsic *DVI = dyn_cast<DbgVariableIntrinsic>(U)) {
            if (DILocalVariable *Var = DVI->getVariable()) {
                return Var->getType();
            }
        }
    }
    return nullptr;
}

// Helper to get struct member name from DIType and index
static std::string getStructMemberName(DIType *Ty, int FieldIdx) {
    if (!Ty) return "f" + std::to_string(FieldIdx);
    
    // Unwrap qualifiers
    while (Ty) {
        if (DIDerivedType *DT = dyn_cast<DIDerivedType>(Ty)) {
            switch (DT->getTag()) {
                case dwarf::DW_TAG_pointer_type:
                case dwarf::DW_TAG_typedef:
                case dwarf::DW_TAG_const_type:
                case dwarf::DW_TAG_volatile_type:
                case dwarf::DW_TAG_restrict_type:
                case dwarf::DW_TAG_member: 
                    Ty = DT->getBaseType();
                    continue;
                default: break;
            }
        }
        break;
    }
    
    if (DICompositeType *CT = dyn_cast<DICompositeType>(Ty)) {
        DINodeArray Elements = CT->getElements();
        if (FieldIdx >= 0 && FieldIdx < (int)Elements.size()) {
            if (DIDerivedType *Member = dyn_cast<DIDerivedType>(Elements[FieldIdx])) {
                StringRef Name = Member->getName();
                if (!Name.empty()) return Name.str();
            }
        }
    }
    
    return "f" + std::to_string(FieldIdx);
}

// Helper to format field path nicely, attempting to resolve names
static std::string formatFieldPath(const std::vector<int>& path, Value *ContextVal = nullptr) {
    if (path.empty()) return "(entire object)";
    
    Type *CurrentTy = nullptr;
    Module *M = nullptr;
    
    if (ContextVal) {
        CurrentTy = ContextVal->getType();
        if (Instruction *I = dyn_cast<Instruction>(ContextVal)) M = I->getModule();
        else if (GlobalValue *GV = dyn_cast<GlobalValue>(ContextVal)) M = GV->getParent();
        else if (Argument *A = dyn_cast<Argument>(ContextVal)) M = A->getParent()->getParent();
    }
    
    // Initialize DebugInfoFinder if Module is available
    DebugInfoFinder Finder;
    bool finderInit = false;
    if (M) {
        Finder.processModule(*M);
        finderInit = true;
    }

    // Peel off initial pointer if needed
    if (CurrentTy && CurrentTy->isPointerTy()) {
       
        CurrentTy = CurrentTy->getPointerElementType(); 
        
    }

    std::string s;
    
    for (size_t i = 0; i < path.size(); ++i) {
        int idx = path[i];
        if (i > 0) s += " -> ";
        
        if (idx == -1) { // Dereference
            s += "*";
            if (CurrentTy && CurrentTy->isPointerTy()) {
                CurrentTy = CurrentTy->getPointerElementType();
            } else {
                CurrentTy = nullptr;
            }
        } else if (idx == 99) { // Wildcard
            s += "?";
            CurrentTy = nullptr;
        } else { // Field access
            std::string fieldName = "f" + std::to_string(idx);
            
            if (CurrentTy && CurrentTy->isStructTy()) {
                StructType *STy = cast<StructType>(CurrentTy);
                
                // Try to find name from Debug Info
                if (finderInit && STy->hasName()) {
                    StringRef StructName = STy->getName();
                    if (StructName.startswith("struct.")) StructName = StructName.drop_front(7);
                    
                    DICompositeType *FoundCT = nullptr;
                    // 1. Try exact match
                    for (auto *DITy : Finder.types()) {
                        if (DICompositeType *CT = dyn_cast<DICompositeType>(DITy)) {
                            if (CT->getName() == StructName) {
                                FoundCT = CT;
                                break;
                            }
                        }
                    }
                    
                    // 2. Try removing numeric suffix (e.g. .1234)
                    if (!FoundCT) {
                        size_t dotPos = StructName.rfind('.');
                        if (dotPos != StringRef::npos) {
                            StringRef BaseName = StructName.substr(0, dotPos);
                            for (auto *DITy : Finder.types()) {
                                if (DICompositeType *CT = dyn_cast<DICompositeType>(DITy)) {
                                    if (CT->getName() == BaseName) {
                                        FoundCT = CT;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    
                    if (FoundCT) {
                        fieldName = getStructMemberName(FoundCT, idx);
                    }
                }
                
                // If name resolution failed, append the struct type name for debugging
                if (fieldName.size() > 1 && fieldName[0] == 'f' && isdigit(fieldName[1])) {
                    if (STy->hasName()) {
                        fieldName += "(" + STy->getName().str() + ")";
                    }
                }
                
                // Advance type
                if (idx >= 0 && idx < (int)STy->getNumElements()) {
                    CurrentTy = STy->getElementType(idx);
                } else {
                    CurrentTy = nullptr;
                }
            } else {
                CurrentTy = nullptr;
            }
            s += fieldName;
        }
    }
    return s;
}

void TaintPass::ReportUAFForFreePoint(const std::string &UseType, Instruction *UseInst, 
                                     const TaintState &Taint) {
    if (!CurrentFreePoint) return;
    const FreePointInfo &FreePoint = *CurrentFreePoint;
    
    if (CurrentFreePointUAFFound) return;
    CurrentFreePointUAFFound = true;

    errs() << "\n================================================================================\n";
    errs() << "                       [BUG REPORT] " 
           << (CurrentMode == MODE_NPD ? "Null Pointer Dereference" : "Use-After-Free") 
           << " Detected                     \n";
    errs() << "================================================================================\n";
    
    // 1. WHAT
    errs() << "  Vulnerability Type : " << UseType << "\n";
    
    // 2. CALL CHAIN
    std::vector<std::string> flow;
    std::vector<int> dirs; // -1: Up (Ret), 1: Down (Call)
    
    if (FreePoint.ContainingFunc) {
        flow.push_back(FreePoint.ContainingFunc->getName().str());
    } else {
        flow.push_back("unknown");
    }
    
    for (const auto &Node : Taint.PathHistory) {
        if (!Node.Func) continue;
        std::string fName = Node.Func->getName().str();
        
        if (fName != flow.back()) {
            flow.push_back(fName);
            if (Node.Description.find("Returned") != std::string::npos) {
                dirs.push_back(-1);
            } else {
                dirs.push_back(1); // Call or Pass
            }
        }
    }
    
    int peakIdx = 0;
    for (size_t i = 0; i < dirs.size(); ++i) {
        if (dirs[i] == -1) peakIdx = i + 1;
    }
    if (peakIdx >= (int)flow.size()) peakIdx = flow.size() - 1;

    errs() << "  Call Chain:\n";
    errs() << "    Free: ";
    for (int i = peakIdx; i >= 0; --i) {
        errs() << flow[i];
        if (i > 0) errs() << " -> ";
    }
    errs() << "\n";
    
    errs() << "    Use : ";
    for (size_t i = peakIdx; i < flow.size(); ++i) {
        errs() << flow[i];
        if (i < flow.size() - 1) errs() << " -> ";
    }
    errs() << "\n";

    // 3. LOCATIONS
    errs() << "  Free Location      : ";
    if (FreePoint.FreeCall->getDebugLoc()) {
        errs() << FreePoint.FreeCall->getDebugLoc()->getFilename().str() << ":" << FreePoint.FreeCall->getDebugLoc()->getLine();
    } else {
        errs() << FreePoint.ContainingFunc->getName() << " (no debug info)";
    }
    
    if (Function *F = FreePoint.FreeCall->getCalledFunction()) {
        errs() << " (" << F->getName() << ")";
    } else {
        errs() << " (indirect targets: ";
        auto it = Ctx->Callees.find(FreePoint.FreeCall);
        if (it != Ctx->Callees.end()) {
            bool first = true;
            for (Function *Target : it->second) {
                if (!first) errs() << ", ";
                errs() << Target->getName();
                if (RWAnalyzer.Result.isReleaseWrapper(Target)) errs() << "[WRAPPER]";
                first = false;
            }
        } else {
            errs() << "unresolved";
        }
        errs() << ")";
    }
    errs() << "\n";
    errs() << "  Use Location       : ";
    if (UseInst->getDebugLoc()) {
        errs() << UseInst->getDebugLoc()->getFilename().str() << ":" << UseInst->getDebugLoc()->getLine();
    } else {
        errs() << UseInst->getFunction()->getName() << " (no debug info)";
    }
    errs() << "\n";

    // 4. MEMORY
    std::string freedPathStr = formatFieldPath(FreePoint.FieldPath, FreePoint.FreedPointer);
    std::string accessedPathStr = formatFieldPath(Taint.FieldPath, FreePoint.FreedPointer);
    
    errs() << "--------------------------------------------------------------------------------\n";
    errs() << "  Memory Object Analysis:\n";
    errs() << "    Freed Path    : " << freedPathStr << "\n";
    errs() << "    Accessed Path : " << accessedPathStr << "\n";
    
    // 5. DETAILED TRACE
    errs() << "--------------------------------------------------------------------------------\n";
    errs() << "  Detailed Trace:\n";
    
    int step = 1;
    for (const auto &Node : Taint.PathHistory) {
        errs() << "    [" << step++ << "] ";
        if (Node.Func) errs() << Node.Func->getName() << ": ";
        errs() << Node.Description;
        if (Node.Inst && Node.Inst->getDebugLoc()) {
             errs() << " (" << Node.Inst->getDebugLoc()->getLine() << ")";
        }
        errs() << "\n";
    }
    
    errs() << "================================================================================\n\n";
}

// ========================================== 
// Legacy / Unused Functions (Kept for compatibility if needed)
// ========================================== 

bool TaintPass::doInitialization(Module *M) {
    errs() << "=== Starting Improved Cross-Function Error Handling Analysis ===\n";
    
    // 确保间接调用图已经构建
    if (!Ctx->Callees.empty() || !Ctx->Callers.empty()) {
        errs() << "Using pre-built indirect call graph:\n";
        errs() << "  Total indirect call sites: " << Ctx->Callees.size() << "\n";
        
        int totalTargets = 0;
        for (auto &Entry : Ctx->Callees) {
            totalTargets += Entry.second.size();
        }
        errs() << "  Total potential targets: " << totalTargets << "\n";
    } else {
        errs() << "WARNING: No indirect call graph found!\n";
    }
    
    // Phase 1: 预分析
    RWAnalyzer.run(M);

    if (CurrentMode == MODE_UAF) {
        DerefAnalyzer.run(M);
    }
    NRAnalyzer.run(M);
    
    return false;
}

bool TaintPass::doFinalization(Module *M) {
    // Cleanup is handled by member destructors
    
    RWAnalyzer.Result.clear();

    AllFreePoints.clear();
    ErrorHandlingBlocks.clear();
    DerefAnalyzer.Result.clear();
    
    return false;
}

bool TaintPass::runOnModule(Module *M) {

    for (auto &F : *M) {
        ErrorReturnFuncAnalysis(&F);
    }
    /*
    bool Changed = true;
    while (Changed) {
        Changed = false;
        for (auto &F : *M) {
            if (Ctx->ErrorReturnFuncs.count(&F)) continue;
            if (InterproceduralErrorAnalysis(&F)) {
                Changed = true;
            }
        }
    }
    */

    errs()<<"condition release fucntion";



    for(Function* F:Ctx->ErrorReturnFuncs){
        errs()<< "-----------\n";
        errs() << "Function " << F->getName() << " identified as an interprocedural error-propagating function\n";
        for(Value* V:retFunction[F]){
            if(retFreePoint.count(V)){
                errs() << "Function " << F->getName() <<" has condition release\n";
            }
            if(retConditionReleaseWrapper.count(V)){
                errs() << "Function " << F->getName() <<" is conditionReleaseWraper\n";
            }
        }
        errs()<< "------------\n";
    }
    
    // Phase 2 & 3: 构建CFG (Deprecated)
    // ErrorHandlingBlocks populated on demand or in Propagate
    
    // Phase 5: 污点传播
    PropagateErrorTaintOnCFG(M);
    
    errs() << "=== Cross-Function Error Handling Analysis Complete ===\n";

    return false;
}