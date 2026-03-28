#ifndef _TAINT_H
#define _TAINT_H

#include <llvm/Pass.h>
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Debug.h"
#include <llvm/IR/Module.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <map> 
#include <set>
#include <algorithm>
#include <vector> 
#include <utility>
#include <iostream>
#include <fstream>
#include <bits/stdc++.h>
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"
#include "Analyzer.h"
#include "Common.h"
#include "llvm/Analysis/CallGraph.h"  
#include <vector>
#include "llvm/IR/Dominators.h"
#include "FieldSensitiveAlias.h"
#include "ReleaseWrapper.h"
#include "DereferenceAnalysis.h"
#include "NullReturn.h"

using namespace llvm;

// ========== 保留的原有数据结构 ==========

struct CallStackFrame {
    Function *CallerFunc;         // 调用者函数
    CallInst *CallSite;          // 调用点
    BasicBlock *ContinueBB;      // 调用点所在的基本块
    BasicBlock::iterator ContinueIt; // 调用点之后的指令迭代器
    
    CallStackFrame(Function *F, CallInst *CI) 
        : CallerFunc(F), CallSite(CI), ContinueBB(CI->getParent()) {
        ContinueIt = std::next(CI->getIterator());
    }
};

// 内存释放调用信息
struct FreeCallInfo {
    CallInst *FreeCall;          // 释放调用指令
    Value *FreedPointer;         // 被释放的指针
    Function *ContainingFunc;    // 包含此调用的函数
    BasicBlock *ContainingBB;    // 包含此调用的基本块
    std::vector<CallStackFrame> CallStack; // 到达此释放调用的调用栈
    
    FreeCallInfo(CallInst *CI, Value *Ptr, Function *F, BasicBlock *BB) 
        : FreeCall(CI), FreedPointer(Ptr), ContainingFunc(F), ContainingBB(BB) {}

};

// 危险使用信息
struct DangerousUse {
    Instruction *UseInst;        // 危险使用的指令
    Value *UsedPointer;          // 被使用的指针
    Function *ContainingFunc;    // 包含此使用的函数
    BasicBlock *ContainingBB;    // 包含此使用的基本块
    std::string UseType;         // 使用类型："load", "store", "call", "free"
    
    DangerousUse(Instruction *I, Value *Ptr, Function *F, BasicBlock *BB, const std::string &Type)
        : UseInst(I), UsedPointer(Ptr), ContainingFunc(F), ContainingBB(BB), UseType(Type) {}
};

// ========== CFG相关数据结构 ==========

// 污点信息
struct TaintInfo {
    Value *TaintedValue;
    Instruction *TaintSource;     // Changed to Instruction*
    std::string TaintType;
    
    TaintInfo(Value *val, Instruction *source, const std::string &type) 
        : TaintedValue(val), TaintSource(source), TaintType(type) {}
    
    bool operator<(const TaintInfo &Other) const {
        if (TaintedValue != Other.TaintedValue) 
            return TaintedValue < Other.TaintedValue;
        if (TaintSource != Other.TaintSource)
            return TaintSource < Other.TaintSource;
        return TaintType < Other.TaintType;
    }
    
    bool operator==(const TaintInfo &Other) const {
        return TaintedValue == Other.TaintedValue && 
               TaintSource == Other.TaintSource && 
               TaintType == Other.TaintType;
    }
};

// Free点信息结构
struct FreePointInfo {
    CallInst *FreeCall;
    Value *FreedPointer;
    Function *ContainingFunc;
    BasicBlock *ContainingBB;
    Instruction *TriggerInst; // Changed from CFGNode
    std::string FreeType;
    std::vector<int> FieldPath;
    
    FreePointInfo(CallInst *CI, Value *Ptr, Function *F, BasicBlock *BB,
                  Instruction *Inst, std::string Type)
        : FreeCall(CI), FreedPointer(Ptr), ContainingFunc(F), ContainingBB(BB),
          TriggerInst(Inst), FreeType(Type) {}


    bool operator<(const FreePointInfo& other) const {
        return std::tie(FreeCall, FreedPointer, FreeType) < 
               std::tie(other.FreeCall, other.FreedPointer, other.FreeType);
    }
};

// 域敏感的污点状态
struct TaintPathNode {
    Instruction *Inst;
    Value *Val;
    BasicBlock *BB;
    Function *Func;
    std::string Description;
    
    TaintPathNode(Instruction *I, Value *V, const std::string &Desc) 
        : Inst(I), Val(V), BB(I ? I->getParent() : nullptr), Func(I ? I->getFunction() : nullptr), Description(Desc) {}
};

struct TaintState {
    Value *TaintedValue;
    vector<int> FieldPath;
    Instruction *SourceInst; // Changed from SourceNode
    string TaintType;
    int PropagationDepth;
    
    std::vector<TaintPathNode> PathHistory;
    std::vector<CallInst*> CallStack; // Changed from CFGNode*
    std::set<Value*> NullPtrs;
    std::set<Value*> TaintedMem;
    
    TaintState() : TaintedValue(nullptr), SourceInst(nullptr), PropagationDepth(0) {}
    
    void addPathNode(Instruction *I, const std::string &Desc) {
        if (I) PathHistory.emplace_back(I, TaintedValue, Desc);
    }
    
    void addPathNode(Instruction *I, Value *V, const std::string &Desc) {
        if (I) PathHistory.emplace_back(I, V, Desc);
    }
    
    bool operator<(const TaintState &other) const {
        if (TaintedValue != other.TaintedValue)
            return TaintedValue < other.TaintedValue;
        if (FieldPath != other.FieldPath)
            return FieldPath < other.FieldPath;
        if (CallStack != other.CallStack)
            return CallStack < other.CallStack;
        if (NullPtrs != other.NullPtrs)
            return NullPtrs < other.NullPtrs;
        if (TaintedMem != other.TaintedMem)
            return TaintedMem < other.TaintedMem;
        return SourceInst < other.SourceInst;
    }
    
    bool operator==(const TaintState &other) const {
        return TaintedValue == other.TaintedValue &&
               FieldPath == other.FieldPath &&
               CallStack == other.CallStack &&
               SourceInst == other.SourceInst &&
               NullPtrs == other.NullPtrs &&
               TaintedMem == other.TaintedMem;
    }
    
    bool covers(const TaintState &other) const {
        if (TaintedValue != other.TaintedValue)
            return false;
        if (FieldPath.size() > other.FieldPath.size())
            return false;
        for (size_t i = 0; i < FieldPath.size(); i++) {
            if (FieldPath[i] != other.FieldPath[i])
                return false;
        }
        return true;
    }
};

struct ConditionReleaseWrapper{
    Function* F;
    std::vector<int> FiledPath;
    CallInst *ReleaseCall;
    int argIdx;
    std::string path;
    ConditionReleaseWrapper(Function* F_,std::vector<int>& FiledPath_,CallInst *ReleaseCall_,int argIdx_)
        :F(F_)
        ,FiledPath(FiledPath_)
        ,ReleaseCall(ReleaseCall_)
        ,argIdx(argIdx_)
    {
        if (FiledPath.empty()){
            path="";
        }else{
            std::ostringstream oss;
            for (size_t i = 0; i < FiledPath.size(); ++i) {
                int val = FiledPath[i];
                if (val == -1) {
                    oss << '*';
                } else if (val == 99) {
                    oss << '?';
                } else {
                    oss << val;
                }
                if (i != FiledPath.size() - 1) {
                    oss << '|';
                }
            }
            path=oss.str();
        }
    }
    bool operator<(const ConditionReleaseWrapper& other) const {
        return std::tie(F, ReleaseCall, argIdx, path) < 
               std::tie(other.F, other.ReleaseCall, other.argIdx, other.path);
    }
};

class TaintPass : public IterativeModulePass {
private:
    std::set<Function* > ConditionReleaseWrappers;
    std::map<Value*,std::set<ConditionReleaseWrapper>> retConditionReleaseWrapper;
    std::map<Value*,std::set<FreePointInfo>> retFreePoint; //int return err:
    std::map<Function*,set<Value*>> retFunction;
    std::map<Value*,std::set<FreePointInfo>> retConditionFailFreePoints;


    static constexpr int MAX_PROPAGATION_DEPTH = 15;
    
    std::set<BasicBlock*> ErrorHandlingBlocks; // Virtual Slice
    bool CurrentFreePointUAFFound = false;
    std::vector<FreePointInfo> AllFreePoints;
    
    // Analyzers
    ReleaseWrapperAnalyzer RWAnalyzer;
    DereferenceAnalyzer DerefAnalyzer;
    PotentialNullReturnAnalyzer NRAnalyzer;
    const FreePointInfo *CurrentFreePoint = nullptr;
    
    AliasContext* GetOrBuildFunctionAlias(Function *F);
    bool IsAliased(Value *V1, Value *V2, AliasContext *aliasCtx);

    bool IsFirstErrorBlockInFunction(BasicBlock *BB, Function *F);
    bool IsUnconditionalBranch(BasicBlock *BB);
    bool IsIndirectCall(CallInst *CI);
    bool FunctionHasErrorBlocks(Function *F);
    
    size_t getInstSourceInfo(CallInst* CI);
    
    void CheckCallInstWithDerefSummary(CallInst *CI,
                                       const TaintState &Taint,
                                       AliasContext *aliasCtx);
    void CheckCallWithCallee(CallInst *CI, Function *Callee,
                            const TaintState &Taint,
                            AliasContext *aliasCtx);
    
    void FindReleaseWrapperSources(BasicBlock *BB, 
                                   std::vector<TaintInfo> &ExternalTaints,
                                   AliasContext *aliasCtx);
    bool IsStoreToFreedMemory(StoreInst *SI, const TaintState &Taint, AliasContext *aliasCtx);

    std::vector<int> MergeFieldPaths(const std::vector<int> &prefix, 
                                            const std::vector<int> &suffix);
    
    void ErrorReturnFuncAnalysis(Function *F);
    void IdentifyErrorReturnVariables(Function *TargetFunc, std::set<Value*> &ErrorReturnVars);
    bool InterproceduralErrorAnalysis(Function *F);
    
    void IdentifyErrorHandlingPaths(Function *F);
    
    bool DetermineErrorBranch(Instruction *Validation);
    bool IsLikelyErrorHandlingBlock(BasicBlock *BB);
    bool IsErrorHandlingEntryBlock(BasicBlock *BB);
    bool IsErrorHandlingExitBlock(BasicBlock *BB);
    
    void PropagateErrorTaintOnCFG(Module *M);
    
    void IdentifyAllFreePoints(Module *M);
    void FindDirectFreePoints(BasicBlock *BB, std::vector<FreePointInfo> &FreePoints);
    void FindReleaseWrapperFreePoints(BasicBlock *BB, std::vector<FreePointInfo> &FreePoints);
    void FindExternalFreePoints(BasicBlock *BB, std::vector<FreePointInfo> &FreePoints);
    
    void AnalyzeIndividualFreePoint(const FreePointInfo &FreePoint);
    vector<int> ExtractFieldPathFromFreePoint(const FreePointInfo &FreePoint);
    void PropagateFromFreePointWithFieldSensitivity(const FreePointInfo &FreePoint, const TaintState &InitialTaint);
    
    bool IsFieldAccessMatching(Value *AccessPtr, const TaintState &Taint, AliasContext *aliasCtx);
    
    // Updated Propagation Signatures
    // We propagate from an Instruction PC (usually start of block or after call)
    // to the end of the block or next call.
    void PropagateToSuccessorWithFieldSensitivity(
        Instruction *CurrentInst, 
        BasicBlock *CurrentBB,
        const TaintState &CurrentTaint,
        std::queue<std::pair<Instruction*, TaintState>> &WorkList);
    
    // Process instructions from Start (inclusive) to End (exclusive)
    Instruction* ProcessInstructionsInRange(
        Instruction *Start, 
        BasicBlock::iterator EndIt,
        TaintState &Taint, 
        AliasContext *aliasCtx, 
        const FreePointInfo &FreePoint);
    
    void PropagateToCallee(CallInst *CallSite, 
                          Function *Callee,
                          const TaintState &CurrentTaint,
                          std::queue<std::pair<Instruction*, TaintState>> &WorkList);
    
    void PropagateFromCallee(BasicBlock *CalleeExitBB, 
                            const TaintState &CurrentTaint,
                            std::queue<std::pair<Instruction*, TaintState>> &WorkList);
    
    void ReportUAFForFreePoint(const std::string &UseType, Instruction *UseInst, 
                              const TaintState &Taint);
    
    // Helpers
    bool isErrorHandlingBlock(BasicBlock *BB);
    void BuildCallStackToCaller(Function *CurrentFunc, std::vector<CallStackFrame> &CallStack);
    std::string getSourceLocation(Instruction *I);
    void ComputeReachableBlocks(BasicBlock *StartBB, std::set<BasicBlock*> &ReachableBlocks);
    std::vector<int> ComputeRelativeFieldPath(
    const std::vector<int> &basePath,
    const std::vector<int> &fullPath,
    const std::vector<int> &taintPath);
    
    bool IsDangerousFunction(StringRef FuncName);
    int TraceArgToCallerParam(Value *arg, Function *F, AliasContext *ctx);
    
    Value* isFromERR(Value* TaintedValue,set<Value*>& ErrorCodeVarsFromERR);
    void ConditionErrorReturnAnalysis(std::map<Value*,std::set<Function*>> ErrorReturnFunction);
    bool ConditionReleaseWrapperAnalysis(Value* V,std::vector<FreePointInfo> NodeFreePoints);
    void checkValueComesFromArg(Function* F,Value* FreedPointer,std::map<int, std::string>& arg_access_map);
    void getFieldPath(std::string& PathHash,std::vector<int>& FieldPath);
    void FindConditionReleaseWrapperFreePoints(Value *V, std::vector<FreePointInfo> &FreePoints);
    void IdentifyErrReturnRelease(CallInst* CI,bool isFindConditionRelease=true);
public:
    enum AnalysisMode { MODE_UAF, MODE_NPD };
    AnalysisMode CurrentMode = MODE_UAF; 

    
    TaintPass(GlobalContext *Ctx_) 
        : IterativeModulePass(Ctx_, "Taint"), 
          RWAnalyzer(Ctx_), 
          DerefAnalyzer(Ctx_),
          NRAnalyzer(Ctx_) {
            errs()<<"TainPass ok";
        } 
            
          
private:
    void IdentifyNPDSources(Module *M);
    void CheckNPD(Instruction *I, Value *Ptr, const TaintState &Taint, AliasContext *aliasCtx);
    bool ShouldPrunePath(BasicBlock *From, BasicBlock *To, const TaintState &Taint);
    bool PointsTo(Value *Ptr, Value *Val, AliasContext *ctx);
    
    virtual bool doInitialization(Module *M);
    virtual bool doFinalization(llvm::Module *);
    virtual bool runOnModule(llvm::Module *M);
    
    uint64_t getPointerSize(Type *PT, const DataLayout &DL);
    
    ReleaseWrapperAnalysisResult& getReleaseWrapperResult() { return RWAnalyzer.Result; }
    
    void PrintFreePointStatistics();
    void VerifyFreePointConsistency();
};
#endif
