#ifndef FIELD_SENSITIVE_ALIAS_H
#define FIELD_SENSITIVE_ALIAS_H

#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>  
#include <llvm/IR/InstrTypes.h> 
#include <llvm/IR/BasicBlock.h> 
#include <llvm/IR/Operator.h>
#include <llvm/IR/Constants.h>
#include <map> 
#include <set>
#include <vector> 
#include <iostream>
#include <list>

#include "Analyzer.h"
#include "Common.h"

using namespace llvm;
using namespace std;

// ========== FieldSensitiveAlias Data Structures (From kfsChecker) ========== 

typedef struct AliasNode {
    set<Value*> aliasclass;

    AliasNode(){
        aliasclass.clear();
    }

    int count(Value* V){
        return aliasclass.count(V);
    }

    void insert(Value* V){
        aliasclass.insert(V);
    }

    bool empty(){
        return aliasclass.empty();
    }

    void erase(Value* V){
        if(aliasclass.count(V) == 0)
            return;
        
        aliasclass.erase(V);
    }

    void print_set(){
        for(auto it = aliasclass.begin(); it != aliasclass.end(); it++){
            Value *v = *it;

            //Func definition is too long, just print its name
            if(Function *F = dyn_cast<Function>(v)){
                errs() << "func: " << F->getName() << "\n"; 
                continue;
            }
            errs()<<*v<<"\n";
        }
    }

} AliasNode;

typedef struct AliasEdge {
    
    AliasNode *fromNode;
    AliasNode *toNode;
    
    int type; 

    AliasEdge(){
        fromNode = NULL;
        toNode = NULL;
        type = -2; // -1: pointer dereference, 0~99999: field index
    }
    
} AliasEdge;

typedef struct AliasContext {

    map<Value*, AliasNode*> NodeMap; //Record one value belongs to which alias node
    map<Value*, AliasNode*> PBNodeMap;

    //Note: for * edge, there should be only one node

    //One node points to which node
    map<AliasNode*, map<int,AliasNode*>> ToNodeMap; 
    map<AliasNode*, map<int,AliasNode*>> PBToNodeMap;

    //One node is pointed by which node
    map<AliasNode*, map<int,AliasNode*>> FromNodeMap; 
    map<AliasNode*, map<int,AliasNode*>> PBFromNodeMap; 


    set<Function*> AnalyzedFuncSet;

    AliasContext(){
    }

    AliasContext(AliasContext *C){
        NodeMap = C->NodeMap;
        PBNodeMap = C->PBNodeMap;
        ToNodeMap = C->ToNodeMap;
        PBToNodeMap = C->PBToNodeMap;
        FromNodeMap = C->FromNodeMap;
        PBFromNodeMap = C->PBFromNodeMap;
    }

    ~AliasContext(){
        set<AliasNode*> nodeSet;
        for(auto it = NodeMap.begin(); it != NodeMap.end(); it++){
            nodeSet.insert(it->second);
        }

        for(AliasNode* n : nodeSet){
            delete n;
        }
    }

} AliasContext;

// ========== Function Declarations ========== 

//InstHandler (Core Logic)
void HandleInst(Instruction* I, AliasContext *aliasCtx, GlobalContext *Ctx, bool handle_const = true);
void HandleLoad(LoadInst* LI, AliasContext *aliasCtx);
void HandleStore(StoreInst* STI, AliasContext *aliasCtx, bool handle_const = true);
void HandleStore(Value* vop, Value* pop, AliasContext *aliasCtx, bool handle_const = true);
void HandleGEP(GEPOperator* GEP, AliasContext *aliasCtx);
void HandleAlloc(AllocaInst* ALI, AliasContext *aliasCtx);
void HandleCai(CallInst* CAI, AliasContext *aliasCtx, GlobalContext *Ctx);
void HandleMove(Value* v1, Value* v2, AliasContext *aliasCtx);
void HandleReturn(Function* F, CallInst* cai, AliasContext *aliasCtx);
void HandleOperator(Value* v, AliasContext *aliasCtx);
void HandleFuncCall(CallInst* CAI, int arg_id, AliasContext *aliasCtx, GlobalContext *Ctx, int depth = 0);


//Tools (From kfsChecker)
AliasNode* getNode(Value *V, AliasContext *aliasCtx);
bool isUselessInst(Instruction* I, GlobalContext *Ctx);
void mergeNode(AliasNode* n1, AliasNode* n2, AliasContext *aliasCtx);
bool checkNodeConnectivity(AliasNode* node1, AliasNode* node2, AliasContext *aliasCtx);
bool getGEPLayerIndex(GEPOperator *GEP, int &Index);
void getClusterValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx);
void getClusterNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx);
void valueSetMerge(set<Value*> &S1, set<Value*> &S2);
void getPreviousNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx);
void getPreviousValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx);
void getAfterNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx);
void getAfterValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx);
void getPreFieldAccessNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasContext *aliasCtx);
void getPreFieldAccessValues(Value* v, set<Value*> &valueSet, AliasContext *aliasCtx);
int getContainerOfIndex(GEPOperator *GEP, Value *&OuterV, Value *&InnerV);

//AliasAnalysis Helpers
bool getAliasNodeAccessArr(AliasContext*aCtx, AliasNode *start, 
    AliasNode *end, string &access_hash);
void normalizeAccessHash(string &access_hash);
void getContainerOfArgs(Function *F, unsigned arg_id, map<string, Value*> &container_map, AliasContext* LocalAliasCtx);
void getValsContainerOf(Function *F, Value* val, map<string, Value*> &container_map, AliasContext* LocalAliasCtx);
void analyzeFunction(Function* F, AliasContext *aliasCtx, GlobalContext *Ctx, bool handle_const = true);


//Debug
void showGraph(AliasContext *aliasCtx);

// ========== Legacy Helpers (Preserved for eh_misuse compatibility) ========== 
StringRef getCalledFuncName(CallInst *CI);
std::string stripFuncNameSuffix(std::string funcName);
AliasNode* PBgetNode(Value *V, AliasContext *aliasCtx);
bool checkValidStructName(Type *Ty);
Type *getLayerTwoType(Type* baseTy, vector<int> ids);
vector<int> extractFieldPathFromValue(Value *V);
Value* getBasePointer(Value *V);
bool fieldPathsOverlap(const vector<int> &path1, const vector<int> &path2);
void printFieldPath(const vector<int> &path);
bool isFieldPathPrefix(const vector<int> &prefix, const vector<int> &full);
bool getFieldAccessPath(AliasContext* aCtx, AliasNode *start, AliasNode *end, 
                                  std::vector<int> &field_access_arr, 
                                  std::set<AliasNode*> &analyzed_set);


#endif