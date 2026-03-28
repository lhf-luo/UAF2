#include "FieldSensitiveAlias.h"
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/InstIterator.h>

using namespace llvm;

// Helper for generic logging if not defined
#ifndef OP
#define OP llvm::errs()
#endif

// ============================================================================ 
// Core InstHandler Logic (From kfsChecker)
// ============================================================================ 

void HandleOperator(Value* v, AliasContext *aliasCtx){

    GEPOperator *GEPO = dyn_cast<GEPOperator>(v);
    if(GEPO){
        HandleGEP(GEPO, aliasCtx);
        HandleOperator(GEPO->getOperand(0), aliasCtx);
    }

    BitCastOperator *CastO = dyn_cast<BitCastOperator>(v);
    if(CastO){
        HandleMove(CastO, CastO->getOperand(0), aliasCtx);
        HandleOperator(CastO->getOperand(0), aliasCtx);
    }

    PtrToIntOperator *PTIO = dyn_cast<PtrToIntOperator>(v);
    if(PTIO){
        HandleMove(PTIO, PTIO->getOperand(0), aliasCtx);
        HandleOperator(PTIO->getOperand(0), aliasCtx);
    }
}

void HandleInst(Instruction* I, AliasContext *aliasCtx, GlobalContext *Ctx, bool handle_const){

    //First filter instructions that do not need to consider
    //e.g., llvm.XXX
    if(isUselessInst(I, Ctx))
        return;

    // Handle GEP and Cast operator
    // Arguments of call are also caught here
    int opnum = I->getNumOperands();
    for(int i = 0; i < I->getNumOperands(); i++){
        Value* op = I->getOperand(i);
        HandleOperator(op, aliasCtx);
    }

    //Handle target instruction
    AllocaInst* ALI = dyn_cast<AllocaInst>(I);
    if(ALI){
        HandleAlloc(ALI, aliasCtx);
        return;
    }

    StoreInst *STI = dyn_cast<StoreInst>(I);
    if(STI){
        HandleStore(STI, aliasCtx, handle_const);
        return;
    }

    LoadInst* LI = dyn_cast<LoadInst>(I);
    if(LI){
        HandleLoad(LI, aliasCtx);
        return;
    }

    GEPOperator *GEP = dyn_cast<GEPOperator>(I);
    if(GEP){
        HandleGEP(GEP, aliasCtx);
        return;
    }

    BitCastInst *BCI = dyn_cast<BitCastInst>(I);
    ZExtInst *ZEXI = dyn_cast<ZExtInst>(I);
    SExtInst *SEXI = dyn_cast<SExtInst>(I);
    TruncInst *TRUI = dyn_cast<TruncInst>(I);
    IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(I);
    PtrToIntInst *PTII = dyn_cast<PtrToIntInst>(I);
    if(BCI || ZEXI || SEXI || TRUI || ITPI || PTII){
        auto op = I->getOperand(0);
        HandleMove(I, op, aliasCtx);
        return;
    }

    PHINode *PHI = dyn_cast<PHINode>(I);
    if(PHI){
        for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i){
            Value *IV = PHI->getIncomingValue(i);
            HandleMove(I, IV, aliasCtx);
        }
        return;
    }

    SelectInst *SLI = dyn_cast<SelectInst>(I);
    if(SLI){
        auto TV = SLI->getTrueValue();
        auto FV = SLI->getFalseValue();
        HandleMove(I, TV, aliasCtx);
        HandleMove(I, FV, aliasCtx);
        return;
    }

    CallInst *CAI = dyn_cast<CallInst>(I);
    if(CAI){
        HandleCai(CAI, aliasCtx, Ctx);
        return;
    }

    ReturnInst *RI = dyn_cast<ReturnInst>(I);
    if(RI){
        Value* return_v = RI->getReturnValue();
        if(return_v == NULL)
            return;
        
        if(isa<ConstantData>(return_v))
            return;
            
        HandleMove(I, return_v, aliasCtx);
    }
}

void HandleAlloc(AllocaInst* ALI, AliasContext *aliasCtx){
    
    if(getNode(ALI, aliasCtx) == NULL){
        AliasNode* node = new AliasNode();
        node->insert(ALI);
        aliasCtx->NodeMap[ALI] = node;
    }
}

// v1 = *v2
void HandleLoad(LoadInst* LI, AliasContext *aliasCtx){
    
    AliasNode* node1 = getNode(LI, aliasCtx);
    if(node1 == NULL){
        node1 = new AliasNode();
        node1->insert(LI);
        aliasCtx->NodeMap[LI] = node1;
    }

    Value* op = LI->getOperand(0);
    AliasNode* node2 = getNode(op, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(op);
        aliasCtx->NodeMap[op] = node2;
    }

    //node2 has pointed to some nodes
    if(aliasCtx->ToNodeMap.count(node2)){

        auto node2_toNodeMap = aliasCtx->ToNodeMap[node2];
        if(node2_toNodeMap.count(-1)){
            mergeNode(node1 ,node2_toNodeMap[-1], aliasCtx);
            goto end;
        }
    }
    //For load, this usually does not happen
    if(aliasCtx->FromNodeMap.count(node1)){

        auto node1_fromNodeMap = aliasCtx->FromNodeMap[node1];
        if(node1_fromNodeMap.count(-1)){
            mergeNode(node1_fromNodeMap[-1], node2, aliasCtx);
            goto end;
        }
    }

    aliasCtx->ToNodeMap[node2][-1] = node1;
    aliasCtx->FromNodeMap[node1][-1] = node2;

end:
    return;
}

// *v2 = v1
void HandleStore(StoreInst* STI, AliasContext *aliasCtx, bool handle_const){
    
    //store vop to pop
    Value* vop = STI->getValueOperand(); //v1
    Value* pop = STI->getPointerOperand(); //v2
    HandleStore(vop, pop, aliasCtx, handle_const);
}

//store vop to pop
void HandleStore(Value* vop, Value* pop, AliasContext *aliasCtx, bool handle_const){

    if(handle_const){
        if(isa<ConstantData>(vop)){
            return;
        }

        if(ConstantExpr *CE = dyn_cast<ConstantExpr>(vop)){
            return;
        }
    }

    AliasNode* node1 = getNode(vop, aliasCtx);
    if(node1 == NULL){
        node1 = new AliasNode();
        node1->insert(vop);
        aliasCtx->NodeMap[vop] = node1;
    }

    AliasNode* node2 = getNode(pop, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(pop);
        aliasCtx->NodeMap[pop] = node2;
    }

    //Under test
    if(checkNodeConnectivity(node1, node2, aliasCtx)){
        return;
    }

    //node2 has pointed to some nodes
    if(aliasCtx->ToNodeMap.count(node2)){
        auto node2_toNodeMap = aliasCtx->ToNodeMap[node2];
        if(node2_toNodeMap.count(-1)){
            mergeNode(node1 ,node2_toNodeMap[-1], aliasCtx);
            goto end;
        }
    }

    if(aliasCtx->FromNodeMap.count(node1)){

        auto node1_fromNodeMap = aliasCtx->FromNodeMap[node1];
        if(node1_fromNodeMap.count(-1)){
            mergeNode(node1_fromNodeMap[-1], node2, aliasCtx);
            goto end;
        }
    }

    aliasCtx->ToNodeMap[node2][-1] = node1;
    aliasCtx->FromNodeMap[node1][-1] = node2;

end:
    return;
}

// v1 = &v2->f
void HandleGEP(GEPOperator* GEP, AliasContext *aliasCtx){

    int idx = 0;
    Value* v2;
    Value* v1;

    bool flag1 = false;
    bool flag2 = false;
    idx = getContainerOfIndex(GEP, v2, v1);
    if(idx >= 0){
        flag1 = true;
    }else if(getGEPLayerIndex(GEP, idx)){
        flag2 = true;
        v2 = GEP->getPointerOperand();
        v1 = GEP;
    }

    if(flag1 || flag2){
        AliasNode* node2 = getNode(v2, aliasCtx);
        if(node2 == NULL){
            node2 = new AliasNode();
            node2->insert(v2);
            aliasCtx->NodeMap[v2] = node2;
        }

        AliasNode* node1 = getNode(v1, aliasCtx);
        if(node1 == NULL){
            node1 = new AliasNode();
            node1->insert(v1);
            aliasCtx->NodeMap[v1] = node1;
        }

        //node2 has pointed to some nodes
        if(aliasCtx->ToNodeMap.count(node2)){
            auto node2_toNodeMap = aliasCtx->ToNodeMap[node2];
            if(node2_toNodeMap.count(idx)){
                mergeNode(node1 ,node2_toNodeMap[idx], aliasCtx);
                goto end;
            }
        }

        aliasCtx->ToNodeMap[node2][idx] = node1;
        aliasCtx->FromNodeMap[node1][idx] = node2;

    }else{
        // Treat as wildcard field access (99) instead of merge
        // This handles i8* arithmetic and failed container_of without collapsing nodes
        int idx = 99;
        v2 = GEP->getPointerOperand();
        v1 = GEP;

        AliasNode* node2 = getNode(v2, aliasCtx);
        if(node2 == NULL){
            node2 = new AliasNode();
            node2->insert(v2);
            aliasCtx->NodeMap[v2] = node2;
        }

        AliasNode* node1 = getNode(v1, aliasCtx);
        if(node1 == NULL){
            node1 = new AliasNode();
            node1->insert(v1);
            aliasCtx->NodeMap[v1] = node1;
        }

        if(aliasCtx->ToNodeMap.count(node2)){
            auto node2_toNodeMap = aliasCtx->ToNodeMap[node2];
            if(node2_toNodeMap.count(idx)){
                mergeNode(node1 ,node2_toNodeMap[idx], aliasCtx);
                goto end;
            }
        }

        aliasCtx->ToNodeMap[node2][idx] = node1;
        aliasCtx->FromNodeMap[node1][idx] = node2;
    }   

end:
    return;
}

// v1 = v2
void HandleMove(Value* v1, Value* v2, AliasContext *aliasCtx){

    AliasNode* node2 = getNode(v2, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(v2);
        aliasCtx->NodeMap[v2] = node2;
    }


    AliasNode* node1 = getNode(v1, aliasCtx);
    if(node1 == NULL){
        node2->insert(v1);
        aliasCtx->NodeMap[v1] = node2;
        return;
    }

    if(node1 == node2)
        return;
    
    if(checkNodeConnectivity(node1, node2, aliasCtx)){
        return;
    }

    mergeNode(node1, node2, aliasCtx);
}

void HandleCai(CallInst* CAI, AliasContext *aliasCtx, GlobalContext *Ctx){

    

    if(getNode(CAI, aliasCtx) == NULL){

        AliasNode* node = new AliasNode();

        node->insert(CAI);

        aliasCtx->NodeMap[CAI] = node;

    }



    for (User::op_iterator OI = CAI->op_begin(), OE = CAI->op_end(); OI != OE; ++OI) {

        if(getNode(*OI, aliasCtx) == NULL){

            AliasNode* node = new AliasNode();

            node->insert(*OI);

            aliasCtx->NodeMap[*OI] = node;

        }

    }



        // Call advanced HandleFuncCall for better precision



        // int arg_id = -1;



        // for(Value* arg : CAI->args()){



        //     ++arg_id;



        //     // Use default depth 0, will be incremented in recursive calls if we passed it through



        //     // But here HandleCai is a base handler. We can't easily pass depth from HandleInst.



        //     // We rely on the internal depth check of HandleFuncCall's entry point if we were to expose it, 



        //     // but currently we only changed the signature.



        //     // Wait, HandleCai calls the entry point.



        //     HandleFuncCall(CAI, arg_id, aliasCtx, Ctx, 0);



        // }

}



void HandleReturn(Function* F, CallInst* cai, AliasContext *aliasCtx){



    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {

        ReturnInst *RI = dyn_cast<ReturnInst>(&*i);

        if(RI){

            Value* return_v = RI->getReturnValue();

            if(return_v){

                HandleMove(return_v, cai, aliasCtx);

            }

        }

    }

}



static void HandleFuncCall(CallInst* CAI, int arg_id, AliasContext *aliasCtx, GlobalContext *Ctx, set<Function*> &handled_funcs, int depth){

    

    if (depth > 5) return; // Recursion limit



    FuncSet Callees = Ctx->Callees[CAI];



    // Now only handle one callee to avoid explosion, and check if it has been handled

    if(Callees.empty() || Callees.size() > 1)

        return;



    if(CAI->arg_size() <= arg_id)

        return;



    for(Function* F : Callees){

        if(handled_funcs.count(F)) {

            continue;

        }

        handled_funcs.insert(F);



        if (arg_id >= F->arg_size()) continue;



        AliasContext LocalAliasCtx;

        Value* arg = F->getArg(arg_id);

        Value* retVal = NULL;



        // Analyze the callee function

        for(Instruction& I : instructions(F)) {

            HandleInst(&I, &LocalAliasCtx, Ctx);

            AliasNode *n_arg = getNode(arg, &LocalAliasCtx);

            if(!n_arg) { continue; }



            if (CallInst *ICAI = dyn_cast<CallInst>(&I)) {

                int iarg_id = -1;

                for(Value* icai_arg : ICAI->args()){

                    ++iarg_id;

                    if(n_arg->count(icai_arg)){

                        HandleFuncCall(ICAI, iarg_id, &LocalAliasCtx, Ctx, handled_funcs, depth + 1);

                    }

                }

            }



            if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {

                retVal = RI->getReturnValue();

            }

        }



        // Propagate the alias info back to caller
        int other_arg_id;
        AliasNode *n_arg = getNode(arg, &LocalAliasCtx);
        if(!n_arg) { continue; }

        for(other_arg_id = 0; other_arg_id < F->arg_size(); other_arg_id++){
            if (other_arg_id == arg_id) { continue; }

            Value* other_arg = F->getArg(other_arg_id);
            AliasNode *n_other_arg = getNode(other_arg, &LocalAliasCtx);
            if(!n_other_arg) { continue; }

            string access_hash;
            if(getAliasNodeAccessArr(&LocalAliasCtx, n_other_arg, n_arg,  access_hash)){
                Value* cai_arg = CAI->getArgOperand(arg_id);
                AliasNode* target_node = getNode(cai_arg, aliasCtx);
                if(!target_node){ continue; }

                while(!access_hash.empty()) {
                    int fieldId = access_hash.back() - '0';
                    access_hash.pop_back();

                    // according to access_hash, get to the target node
                    if(!aliasCtx->FromNodeMap.count(target_node) ||
                       !aliasCtx->FromNodeMap[target_node].count(fieldId)) {
                        // create a new node
                        AliasNode* from_node = new AliasNode();
                        aliasCtx->FromNodeMap[target_node][fieldId] = from_node;
                        aliasCtx->ToNodeMap[from_node][fieldId] = target_node;
                        target_node = from_node;
                    }else{
                        target_node = aliasCtx->FromNodeMap[target_node][fieldId];
                    }
                }

                Value* cai_other_arg = CAI->getArgOperand(other_arg_id);
                AliasNode* n_cai_other_arg = getNode(cai_other_arg, aliasCtx);
                if(n_cai_other_arg == NULL){
                    n_cai_other_arg = new AliasNode();
                    n_cai_other_arg->insert(cai_other_arg);
                    aliasCtx->NodeMap[cai_other_arg] = n_cai_other_arg;
                }
                mergeNode(target_node, n_cai_other_arg, aliasCtx);
                break;
            }
        }

        // Handle return value
        if(other_arg_id == F->arg_size()){
            AliasNode *n_retVal = getNode(retVal, &LocalAliasCtx);
            if(!n_retVal) { continue; }

            string access_hash;
            if(getAliasNodeAccessArr(&LocalAliasCtx, n_retVal, n_arg,  access_hash)){
                Value* cai_arg = CAI->getArgOperand(arg_id);
                AliasNode* target_node = getNode(cai_arg, aliasCtx);
                if(!target_node){ continue; }

                while(!access_hash.empty()) {
                    int fieldId = access_hash.back() - '0';
                    access_hash.pop_back();

                    // according to access_hash, get to the target node
                    if(!aliasCtx->FromNodeMap.count(target_node) ||
                       !aliasCtx->FromNodeMap[target_node].count(fieldId)) {
                        // create a new node
                        AliasNode* from_node = new AliasNode();
                        aliasCtx->FromNodeMap[target_node][fieldId] = from_node;
                        aliasCtx->ToNodeMap[from_node][fieldId] = target_node;
                        target_node = from_node;
                    }else{
                        target_node = aliasCtx->FromNodeMap[target_node][fieldId];
                    }
                }
                Value* cai_retVal = CAI;
                AliasNode* n_cai_retVal = getNode(cai_retVal, aliasCtx);
                if(n_cai_retVal == NULL){
                    n_cai_retVal = new AliasNode();
                    n_cai_retVal->insert(cai_retVal);
                    aliasCtx->NodeMap[cai_retVal] = n_cai_retVal;
                }
                mergeNode(target_node, n_cai_retVal, aliasCtx);
            }
        }
    }
}

void HandleFuncCall(CallInst* CAI, int arg_id, AliasContext *aliasCtx, GlobalContext *Ctx, int depth){
    set<Function*> handled_funcs;
    HandleFuncCall(CAI, arg_id, aliasCtx, Ctx, handled_funcs, depth);
}

// ============================================================================ 
// Tools Logic (From kfsChecker)
// ============================================================================ 

void mergeNode(AliasNode* n1, AliasNode* n2, AliasContext *aliasCtx){

    if(n1 == n2)    
        return;
    
    for(auto it = n1->aliasclass.begin(); it != n1->aliasclass.end(); it++){
        Value* v = *it;
        n2->insert(v);
        aliasCtx->NodeMap[v] = n2;
    }
    n1->aliasclass.clear();

    //Then change edges
    //Check n1 points to which node
    //All point-to nodes should be merged
    if(aliasCtx->ToNodeMap.count(n1)){
        auto n1_toNodeMap = aliasCtx->ToNodeMap[n1];
        //Both n1 and n2 have point to nodes
        if(aliasCtx->ToNodeMap.count(n2)){
            auto n2_toNodeMap = aliasCtx->ToNodeMap[n2];
            for(auto n1_pair : n1_toNodeMap){
                int n1_edge = n1_pair.first;
                AliasNode* n1_toNode= n1_pair.second;
                //merge the same edge : n1_edge
                if(n2_toNodeMap.count(n1_edge)){
                    AliasNode* n2_toNode = n2_toNodeMap[n1_edge];
                    if(n1_toNode != n2_toNode){
                        aliasCtx->ToNodeMap[n1].erase(n1_edge);
                        aliasCtx->ToNodeMap[n2].erase(n1_edge);
                        aliasCtx->FromNodeMap[n1_toNode].erase(n1_edge);
                        aliasCtx->FromNodeMap[n2_toNode].erase(n1_edge);
                        mergeNode(n1_toNode, n2_toNode, aliasCtx);
                        aliasCtx->ToNodeMap[n2][n1_edge] = n2_toNode;
                        aliasCtx->FromNodeMap[n2_toNode][n1_edge] = n2;
                    }
                }
                //n1 has, but n2 has no such edge, merge the edge
                else{
                    aliasCtx->ToNodeMap[n1].erase(n1_edge);
                    aliasCtx->ToNodeMap[n2][n1_edge] = n1_toNode;
                    aliasCtx->FromNodeMap[n1_toNode][n1_edge] = n2;
                }
            }
        }
        //n2 has no pointed node
        else{
            aliasCtx->ToNodeMap.erase(n1);
            aliasCtx->ToNodeMap[n2] = n1_toNodeMap;
            for(auto n: n1_toNodeMap){
                aliasCtx->FromNodeMap[n.second][n.first] = n2;
            }
        }
    }

    //Check which node points to n1
    if(aliasCtx->FromNodeMap.count(n1)){
        auto n1_fromNodeMap = aliasCtx->FromNodeMap[n1];
        //Both n1 and n2 have previous(from) nodes
        if(aliasCtx->FromNodeMap.count(n2)){
            auto n2_fromNodeMap = aliasCtx->FromNodeMap[n2];
            for(auto n1_pair : n1_fromNodeMap){
                int n1_edge = n1_pair.first;
                AliasNode* n1_fromNode = n1_pair.second;
                if(n1_edge == -1){
                    //merge the same edge : * edge
                    if(n2_fromNodeMap.count(n1_edge)) { 
                        AliasNode* n2_fromNode = n2_fromNodeMap[n1_edge];
                        if(n1_fromNode != n2_fromNode){
                            aliasCtx->FromNodeMap[n1].erase(n1_edge);
                            aliasCtx->FromNodeMap[n2].erase(n1_edge);
                            aliasCtx->ToNodeMap[n1_fromNode].erase(n1_edge);
                            aliasCtx->ToNodeMap[n2_fromNode].erase(n1_edge);
                            mergeNode(n1_fromNode, n2_fromNode, aliasCtx);
                            aliasCtx->FromNodeMap[n2][n1_edge] = n2_fromNode;
                            aliasCtx->ToNodeMap[n2_fromNode][n1_edge] = n2;
                        }
                    }
                    //n1 has, but n2 has no such edge, merge the edge
                    else{
                        aliasCtx->FromNodeMap[n1].erase(n1_edge);
                        aliasCtx->FromNodeMap[n2][n1_edge] = n1_fromNode;
                        aliasCtx->ToNodeMap[n1_fromNode][n1_edge] = n2;
                    }
                }
                //The previous edge is not *, just add them to the graph
                else{
                    aliasCtx->FromNodeMap[n1].erase(n1_edge);
                    aliasCtx->FromNodeMap[n2][n1_edge] = n1_fromNode;
                    aliasCtx->ToNodeMap[n1_fromNode][n1_edge] = n2;
                }
            }
        }
        //n2 has no pre node
        else{
            aliasCtx->FromNodeMap.erase(n1);
            aliasCtx->FromNodeMap[n2] = n1_fromNodeMap;
            for(auto m: n1_fromNodeMap)
                aliasCtx->ToNodeMap[m.second][m.first] = n2;
        }
    }
}

//Filter instructions we do not need to analysis
//Return true if current inst does not need analysis
bool isUselessInst(Instruction* I, GlobalContext *Ctx){

    //Filter debug functions
    CallInst *CAI = dyn_cast<CallInst>(I);
    if(CAI){
        StringRef FName = getCalledFuncName(CAI);
        if(Ctx->DebugFuncs.count(FName.str())){
            return true;
        }
    }

    return false;
}

AliasNode* getNode(Value *V, AliasContext *aliasCtx){
    if (!V) return NULL;

    //Constant value is always regarded as different value
    //Note: this check will influence global values!
    ConstantData *Ct = dyn_cast<ConstantData>(V);
    if(Ct){
        return NULL;
    }

    //Use a map to speed up query
    if(aliasCtx->NodeMap.count(V))
        return aliasCtx->NodeMap[V];

    return NULL;
}

bool checkNodeConnectivity(AliasNode* node1, AliasNode* node2, AliasContext *aliasCtx){

    if(!node1 || !node2)
        return false;

    list<AliasNode *>LN;
    LN.push_back(node1);
    set<AliasNode *> PN; //Global value set to avoid loop
    PN.clear();

    while (!LN.empty()) {
        AliasNode *CN = LN.front();
        LN.pop_front();

        if (PN.find(CN) != PN.end()){
            continue;
        }
        PN.insert(CN);

        if(CN == node2)
            return true;

        if(aliasCtx->ToNodeMap.count(CN)){
            for(auto n : aliasCtx->ToNodeMap[CN]){
                if(n.first == -1)
                    LN.push_back(n.second);
            }
        }

        if(aliasCtx->FromNodeMap.count(CN)){
            for(auto m : aliasCtx->FromNodeMap[CN]){
                if(m.first == -1){
                    LN.push_back(m.second);
                }
                
            }
        }
    }

    return false;
}

bool checkValidStructName(Type *Ty){

    if(Ty->isStructTy()){
        StructType* STy = dyn_cast<StructType>(Ty);
        if(STy->isLiteral()){
            return false;
        }
        else{
            return true;
        }
    }
    else{
        return false;
    }
}

Type *getLayerTwoType(Type* baseTy, vector<int> ids){

    StructType *sty = dyn_cast<StructType>(baseTy);
    if(!sty)
        return NULL;
    
    for(auto it = ids.begin(); it!=ids.end(); it++){
        int idx = *it;

        Type* subTy = sty->getElementType(idx);
        StructType *substy = dyn_cast<StructType>(subTy);
        if(!substy)
            return NULL;
        
        sty = substy;
    }

    return sty;
}

//Return true if we successfully find the layered type
bool getGEPLayerIndex(GEPOperator *GEP, int &Index) {

    Type *PTy = GEP->getPointerOperand()->getType();
    if(!PTy->isPointerTy())
        return false;

    Type *Ty = PTy->getPointerElementType();

    Type* BTy;
    int Idx;

    //Expect the PointerOperand is an identified struct
    if (Ty->isStructTy() && GEP->hasAllConstantIndices()) {
        BTy = Ty;
        User::op_iterator ie = GEP->idx_end();
        ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
        Idx = ConstI->getSExtValue(); //Idx is the last indice
        if(Idx < 0)
            return false;
        
        if(!checkValidStructName(Ty))
            return false;

        unsigned indice_num = GEP->getNumIndices();

        //Filter GEP that has invalid indice
        ConstantInt *ConstI_first = dyn_cast<ConstantInt>(GEP->idx_begin()->get());
        int Idx_first = ConstI_first->getSExtValue();
        if(Idx_first != 0 && indice_num>=2){
            if(Ty->isStructTy()){
                return false;
            }
        }
        
        if(indice_num < 2)
            return false;

        Index = Idx;

        return true;
    }
    else if(Ty->isStructTy() || Ty->isArrayTy()){
        Index = 99;
        return true;
    }

    return false;
    
}

//merge S2 into S1
void valueSetMerge(set<Value*> &S1, set<Value*> &S2){
    for(auto v : S2)
        S1.insert(v);
}

void getClusterNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx){

    if(startNode == NULL)
        return;
    
    nodeSet.insert(startNode);

    list<AliasNode *>LN;
    LN.push_back(startNode);
    set<AliasNode *> PN; //Global value set to avoid loop
    PN.clear();

    while (!LN.empty()) {
        AliasNode *CN = LN.front();
        LN.pop_front();

        if (PN.find(CN) != PN.end()){
            continue;
        }
        PN.insert(CN);

        if(aliasCtx->ToNodeMap.count(CN)){
            for(auto m : aliasCtx->ToNodeMap[CN]){
                LN.push_back(m.second);
                nodeSet.insert(m.second);
            }
        }

        if(aliasCtx->FromNodeMap.count(CN)){
            for(auto m : aliasCtx->FromNodeMap[CN]){
                LN.push_back(m.second);
                nodeSet.insert(m.second);
            }
        }
    }
}

void getClusterValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx){

    if(v == NULL)
        return;

    AliasNode *n = getNode(v, aliasCtx);
    if(!n){
        return;
    }

    //Get the cluster value to enable inter-procedural analysis
    set<AliasNode*> targetNodeSet;
    targetNodeSet.clear();
    getClusterNodes(n, targetNodeSet, aliasCtx);
    
    valueSet.clear();
    for(auto it = targetNodeSet.begin(); it != targetNodeSet.end(); it++){
        AliasNode *n = *it;
        valueSetMerge(valueSet, n->aliasclass);
    }
}

void getPreviousNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx){

    if(startNode == NULL)
        return;
    
    nodeSet.insert(startNode);

    list<AliasNode *>LN;
    LN.push_back(startNode);
    set<AliasNode *> PN; //Global value set to avoid loop
    PN.clear();

    while (!LN.empty()) {
        AliasNode *CN = LN.front();
        LN.pop_front();

        if (PN.find(CN) != PN.end()){
            continue;
        }
        PN.insert(CN);

        if(aliasCtx->FromNodeMap.count(CN)){
            for(auto m : aliasCtx->FromNodeMap[CN]){
                LN.push_back(m.second);
                nodeSet.insert(m.second);
            }
        }
    }
}

void getPreviousValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx){

    if(v == NULL)
        return;

    AliasNode *n = getNode(v, aliasCtx);
    if(!n){
        return;
    }

    //Get the cluster value to enable inter-procedural analysis
    set<AliasNode*> previousNodeSet;
    previousNodeSet.clear();
    getPreviousNodes(n, previousNodeSet, aliasCtx);

    valueSet.clear();
    for(auto it = previousNodeSet.begin(); it != previousNodeSet.end(); it++){
        AliasNode *n = *it;
        valueSetMerge(valueSet, n->aliasclass);
    }

}

void getAfterNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx){

    if(startNode == NULL)
        return;
    
    list<AliasNode *>LN;
    LN.push_back(startNode);
    set<AliasNode *> PN; //Global value set to avoid loop
    PN.clear();

    while (!LN.empty()) {
        AliasNode *CN = LN.front();
        LN.pop_front();

        if (PN.find(CN) != PN.end()){
            continue;
        }
        PN.insert(CN);

        if(aliasCtx->ToNodeMap.count(CN)){
            for(auto n : aliasCtx->ToNodeMap[CN]){
                LN.push_back(n.second);
                nodeSet.insert(n.second);
            }
        }
    }
}

void getAfterValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx){

    if(v == NULL)
        return;

    AliasNode *n = getNode(v, aliasCtx);
    if(!n){
        return;
    }

    //Get the cluster value to enable inter-procedural analysis
    set<AliasNode*> afterNodeSet;
    afterNodeSet.clear();
    getAfterNodes(n, afterNodeSet, aliasCtx);

    valueSet.clear();
    for(auto it = afterNodeSet.begin(); it != afterNodeSet.end(); it++){
        AliasNode *n = *it;
        valueSetMerge(valueSet, n->aliasclass);
    }

}

void getPreFieldAccessNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx){

    if(startNode == NULL)
        return;
    
    list<AliasNode *>LN;
    LN.push_back(startNode);
    set<AliasNode *> PN; //Global value set to avoid loop
    PN.clear();

    while (!LN.empty()) {
        AliasNode *CN = LN.front();
        LN.pop_front();

        if (PN.find(CN) != PN.end()){
            continue;
        }
        PN.insert(CN);

        if(aliasCtx->FromNodeMap.count(CN)){
            for(auto m : aliasCtx->FromNodeMap[CN]){
                LN.push_back(m.second);
                if(m.first != -1){
                    nodeSet.insert(m.second);
                }
            }
        }
    }
}

void getPreFieldAccessValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx){

    if(v == NULL)
        return;

    AliasNode *n = getNode(v, aliasCtx);
    if(!n){
        return;
    }

    //Get the cluster value to enable inter-procedural analysis
    set<AliasNode*> previousNodeSet;
    previousNodeSet.clear();
    getPreFieldAccessNodes(n, previousNodeSet, aliasCtx);

    valueSet.clear();
    for(auto it = previousNodeSet.begin(); it != previousNodeSet.end(); it++){
        AliasNode *n = *it;
        valueSetMerge(valueSet, n->aliasclass);
    }

}

int getContainerOfIndex(GEPOperator *GEP, Value *&OuterV, Value *&InnerV){
    if(!GEP)
        return -1;

    unsigned indice_num = GEP->getNumIndices();
    if(indice_num != 1){
        return -1;
    }

    Type *PTy = GEP->getPointerOperand()->getType();
    if(!PTy->isPointerTy())
        return -1;

    Type *Ty = GEP->getSourceElementType();
    int Idx;
    if(Ty->isIntegerTy(8) && GEP->hasAllConstantIndices()){
        User::op_iterator ie = GEP->idx_end();
        ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
        Idx = ConstI->getSExtValue(); //Idx is the last indice
        if(Idx > 0){
            return -1;
        }

        GetElementPtrInst *GEPInst;
        if(isa<GetElementPtrInst>(GEP)){
            GEPInst = dyn_cast<GetElementPtrInst>(GEP);
        }else{
            return -1;
        }
        Module *M = GEPInst->getModule();
        DataLayout DL = M->getDataLayout();
        
        Instruction* pre_1 = GEPInst->getPrevNonDebugInstruction();
        if(!pre_1 || !isa<LoadInst>(pre_1)){
            return -1;
        }

        Instruction* pre_2 = pre_1->getPrevNonDebugInstruction();
        if(!pre_2 || !isa<StoreInst>(pre_2)){
            return -1;
        }

        Instruction* pre_BCI;
        Instruction* pre_3 = pre_2->getPrevNonDebugInstruction();
        if(!pre_3 || !isa<BitCastInst>(pre_3)){
            return -1;
        }
        pre_BCI = dyn_cast<BitCastInst>(pre_3);
        Value *ToV = pre_BCI;
        Value *FromV = pre_BCI->getOperand(0);
        Type *ToTy = ToV->getType();
        Type *FromTy = FromV->getType();
        if(!ToTy->isPointerTy()){
            return -1;
        }
        ToTy = ToTy->getPointerElementType();
        if(!ToTy->isIntegerTy(8)){
            return -1;
        }
        if(!FromTy->isPointerTy()){
            return -1;
        }
        FromTy = FromTy->getPointerElementType();
        if(!FromTy->isStructTy()){
            return -1;
        }
        if(!checkValidStructName(FromTy)){
            return -1;
        }
        InnerV = FromV;
        StructType *InnerTy = dyn_cast<StructType>(FromTy);

        Instruction* next_BCI;
        Instruction* next_1 = GEPInst->getNextNonDebugInstruction();
        if(!next_1 || !isa<BitCastInst>(next_1)){
            return -1;
        }
        next_BCI = dyn_cast<BitCastInst>(next_1);
        Value *next_ToV = next_BCI;
        Value *next_FromV = next_BCI->getOperand(0);
        Type *next_ToTy = next_ToV->getType();
        Type *next_FromTy = next_FromV->getType();
        if(!next_ToTy->isPointerTy()){
            return -1;   
        }
        next_ToTy = next_ToTy->getPointerElementType();
        if(!next_ToTy->isStructTy()){
            return -1;
        }
        if(!checkValidStructName(next_ToTy)){
            return -1;
        }
        if(!next_FromTy->isPointerTy()){
            return -1;
        }
        next_FromTy = next_FromTy->getPointerElementType();
        if(!next_FromTy->isIntegerTy(8)){
            return -1;
        }
        OuterV = next_FromV;
        StructType *OuterTy = dyn_cast<StructType>(next_ToTy);

        Instruction* next_2 = next_BCI->getNextNonDebugInstruction();
        if(!next_2 || !isa<StoreInst>(next_2)){
            return -1;
        }
        Instruction* next_3 = next_2->getNextNonDebugInstruction();
        if(!next_3 || !isa<LoadInst>(next_3)){
            return -1;
        }
        Instruction* next_4 = next_3->getNextNonDebugInstruction();
        if(!next_4 || !isa<StoreInst>(next_4)){
            return -1;
        }

        for(unsigned i = 0; i < OuterTy->getNumElements(); i++){
            Type *subTy = OuterTy->getElementType(i);
            if(subTy == InnerTy){
                int offset = DL.getStructLayout(OuterTy)->getElementOffset(i);
                if (offset + Idx == 0) { 
                    return i;
                }
            }
        }
    }
    return -1;
}

static bool get_field_access_arr(AliasContext*aCtx, AliasNode *start, AliasNode *end, 
    vector<char> &field_access_arr, set<AliasNode*> &analyzed_set){

    if(start == end){
        return true;
    }

    if(analyzed_set.count(start))
        return false;
    
    analyzed_set.insert(start);

    if(aCtx->ToNodeMap.count(start)){
        for(auto m : aCtx->ToNodeMap[start]){
            field_access_arr.push_back(m.first + '0');
            
            bool ret = get_field_access_arr(aCtx, m.second, end, field_access_arr, analyzed_set);
            if(ret)
                return true;

            field_access_arr.pop_back();
        }
    }

    return false;
}

bool getAliasNodeAccessArr(AliasContext*aCtx, AliasNode *start, 
    AliasNode *end, string &access_hash){

    if(start == end){
        return true;
    }

    vector<char> field_access_arr;
    set<AliasNode*> analyzed_set;
    if(get_field_access_arr(aCtx, start, end, field_access_arr, analyzed_set)){
        access_hash = "";
        for(auto i : field_access_arr){
            access_hash += i;
        }
        return true;
    }
    return false;
}

static set<char> get_unique_symbols(const string &str) {
    set<char> unique_symbols;
    for (char c : str) {
        if (c != '|'){ 
            unique_symbols.insert(c);
        }
    }
    return unique_symbols;
}

void normalizeAccessHash(string &access_hash) {
    // Disabled to prevent corruption of integer field paths
    return;
}

// This function assums that an argument only can be one field of a struct
void getContainerOfArgs(Function *F, unsigned arg_id, map<string, Value*> &container_map, AliasContext* LocalAliasCtx){ 
    if(!F || arg_id >= F->arg_size()) { return; }

    Argument *arg = &*(F->arg_begin() + arg_id);
    Type *arg_type = arg->getType();
    
    if(arg_type->isPointerTy()){
        AliasNode *n_arg = getNode(arg, LocalAliasCtx);
        if(!n_arg) { return; }

        for (Instruction& I : instructions(F)) {
            GEPOperator *GEP = dyn_cast<GEPOperator>(&I);
            if(!GEP) { continue; }

            Value *OuterV = nullptr;
            Value *InnerV = nullptr;
            int index = -1;
            if((index = getContainerOfIndex(GEP, OuterV, InnerV)) >= 0){
                // Found the container
                AliasNode *n_inner = getNode(InnerV, LocalAliasCtx);
                if(!n_inner) { continue; }

                string access_hash = "";
                char idx = index + '0'; //
                if(getAliasNodeAccessArr(LocalAliasCtx, n_arg, n_inner, access_hash)){
                    
                    if(access_hash!=""){
                        container_map[access_hash + "|" + idx] = OuterV;
                    }
                    else{
                        container_map[std::string(1,idx)] = OuterV;
                    }
                    
                }
            }
        }
    }
}

void getValsContainerOf(Function *F, Value* val, map<string, Value*> &container_map, AliasContext* LocalAliasCtx){
    if(!F || !val) { return; }

    Type *val_type = val->getType();
    
    if(val_type->isPointerTy()){
        AliasNode *n_val = getNode(val, LocalAliasCtx);
        if(!n_val) { return; }

        for (Instruction& I : instructions(F)) {
            GEPOperator *GEP = dyn_cast<GEPOperator>(&I);
            if(!GEP) { continue; }

            Value *OuterV = nullptr;
            Value *InnerV = nullptr;
            int index = -1;
            if((index = getContainerOfIndex(GEP, OuterV, InnerV)) >= 0){
                // Found the container
                AliasNode *n_outer = getNode(OuterV, LocalAliasCtx);
                if(!n_outer) { continue; }

                string access_hash = "";
                char idx = index + '0';
                if(getAliasNodeAccessArr(LocalAliasCtx, n_val, n_outer, access_hash)){
                    container_map[access_hash + idx] = InnerV;
                }
            }
        }
    }
}

void showGraph(AliasContext *aliasCtx){
    
    if(!aliasCtx)
        return;
    
    set<AliasNode*> Nodeset;
    for(auto m : aliasCtx->NodeMap){
        AliasNode* n = m.second;
        Nodeset.insert(n);
    }

    for(AliasNode* n : Nodeset){
        OP<<"node: "<<n<<"\n";
        if(aliasCtx->FromNodeMap.count(n)){
            for(auto pre_n : aliasCtx->FromNodeMap[n]){
                OP<<"previdous nodes: "<<pre_n.second<<" (" << pre_n.first<<")\n";
            }
        }
        if(aliasCtx->ToNodeMap.count(n)){
            for(auto to_n : aliasCtx->ToNodeMap[n])
                OP<<"to nodes: "<<to_n.second<<" (" << to_n.first<<")\n";
        }
        OP<<"node content: \n";
        n->print_set();
        OP<<"\n";
    }
    OP<<"\n";
}

// ============================================================================ 
// Legacy Helpers (Preserved/Backported from eh_misuse)
// ============================================================================ 

StringRef getCalledFuncName(CallInst *CI) {
    Value* V = CI->getCalledOperand();
    assert(V);
    if (InlineAsm *IA = dyn_cast<InlineAsm>(V))
        return StringRef(IA->getAsmString());
    User *UV = dyn_cast<User>(V);
    if (UV && UV->getNumOperands() > 0) {
        Value *VUV = UV->getOperand(0);
        return VUV->getName();
    }
    return V->getName();
}

std::string stripFuncNameSuffix(std::string funcName) {
    size_t dotPos = funcName.find('.');
    if (dotPos != std::string::npos) {
        return funcName.substr(0, dotPos);
    }
    return funcName;
}

AliasNode* PBgetNode(Value *V, AliasContext *aliasCtx){
    ConstantData *Ct = dyn_cast<ConstantData>(V);
    if(Ct){
        return NULL;
    }
    if(aliasCtx->PBNodeMap.count(V))
        return aliasCtx->PBNodeMap[V];
    return NULL;
}

void analyzeFunction(Function* F, AliasContext *aliasCtx, GlobalContext *Ctx, bool handle_const){
    if(!F)
        return;
    
    if(aliasCtx->AnalyzedFuncSet.count(F))
        return;
    
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        Instruction *iInst = dyn_cast<Instruction>(&*i);
        HandleInst(iInst, aliasCtx, Ctx, handle_const);
    }
    
    aliasCtx->AnalyzedFuncSet.insert(F);
}

vector<int> extractFieldPathFromValue(Value *V) {
    vector<int> path;
    Value *current = V;
    
    int maxDepth = 5;
    int depth = 0;
    
    while (depth < maxDepth) {
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(current)) {
            if (GEPOperator *GEPO = dyn_cast<GEPOperator>(GEP)) {
                int idx;
                if (getGEPLayerIndex(GEPO, idx)) {
                    path.insert(path.begin(), idx);  
                }
            }
            current = GEP->getPointerOperand();
        } 
        else if (BitCastInst *BC = dyn_cast<BitCastInst>(current)) {
            current = BC->getOperand(0);
        }
        else if (LoadInst *LI = dyn_cast<LoadInst>(current)) {
            path.insert(path.begin(), -1);
            current = LI->getPointerOperand();
        }
        else {
            break;
        }
        
        depth++;
    }
    
    return path;
}

Value* getBasePointer(Value *V) {
    while (true) {
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
            V = GEP->getPointerOperand();
        } else if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
            V = BC->getOperand(0);
        } else if (CastInst *CI = dyn_cast<CastInst>(V)) {
            V = CI->getOperand(0);
        } else if(LoadInst *LI = dyn_cast<LoadInst>(V)){
            V=LI->getPointerOperand();
        }
        else {
            return V;
        }
    }
}

void printFieldPath(const vector<int> &path) {
    OP << "[";
    for (size_t i = 0; i < path.size(); i++) {
        if (path[i] == -1) {
            OP << "*";
        } else if (path[i] == 99) {
            OP << "?";
        } else {
            OP << path[i];
        }
        
        if (i < path.size() - 1) {
            OP << ", ";
        }
    }
    OP << "]";
}

bool isFieldPathPrefix(const vector<int> &prefix, const vector<int> &full) {
    if (prefix.size() > full.size()) return false;
    
    for (size_t i = 0; i < prefix.size(); i++) {
        if (prefix[i] != full[i] && prefix[i] != 99 && full[i] != 99) return false;
    }
    return true;
}

bool fieldPathsOverlap(const vector<int> &path1, const vector<int> &path2) {
    size_t minLen = min(path1.size(), path2.size());
    
    for (size_t i = 0; i < minLen; i++) {
        if (path1[i] == 99 || path2[i] == 99) {
            return true;
        }
        if (path1[i] != path2[i]) {
            return false;
        }
    }
    
    return true;
}

bool getFieldAccessPath(AliasContext* aCtx, AliasNode *start, AliasNode *end, 
                                  std::vector<int> &field_access_arr, 
                                  std::set<AliasNode*> &analyzed_set) {
    if (start == end) {
        return true;
    }
    
    if (analyzed_set.count(start)) {
        return false;
    }
    analyzed_set.insert(start);
    
    if (aCtx->ToNodeMap.count(start)) {
        for (auto& edge : aCtx->ToNodeMap[start]) {
            int field_idx = edge.first;
            AliasNode* next_node = edge.second;
            
            if (field_idx == -1) {
                field_access_arr.push_back(-1);
                
                bool ret = getFieldAccessPath(aCtx, next_node, end, field_access_arr, analyzed_set);
                if (ret) {
                    return true;
                }
                
                field_access_arr.pop_back();
            } 
            else if (field_idx >= 0 && field_idx < 99) {
                field_access_arr.push_back(field_idx);
                
                bool ret = getFieldAccessPath(aCtx, next_node, end, field_access_arr, analyzed_set);
                if (ret) {
                    return true;
                }
                
                field_access_arr.pop_back();
            }
            else if (field_idx == 99) {
                field_access_arr.push_back(99);
                
                bool ret = getFieldAccessPath(aCtx, next_node, end, field_access_arr, analyzed_set);
                if (ret) {
                    return true;
                }
                
                field_access_arr.pop_back();
            }
        }
    }
    
    return false;
}