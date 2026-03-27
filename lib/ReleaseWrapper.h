#ifndef _RELEASE_WRAPPER_H
#define _RELEASE_WRAPPER_H

#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>
#include <map>
#include <set>
#include <vector>
#include <iostream>
#include <list>
#include <string>
#include <sstream>

#include "Common.h"
#include "FieldSensitiveAlias.h"
#include "Analyzer.h" // Includes struct ReleaseSummary forward decl

using namespace llvm;

// Define ReleaseSummary here
struct ReleaseSummary {
    CallInst *ReleaseCall;
    int FuncArgId;
    std::string PathHash; // "0|1" style
    bool IsNullified;
    bool IsErrorPath;
    bool is_refcount_release; // kfsChecker specific
    
    // Cache for vector representation used by TaintPass
    mutable std::vector<int> _FieldAccessPathCache;
    mutable bool _CacheValid = false;
    
    ReleaseSummary(CallInst *RC, int argId, std::string path, bool nullified, bool errorPath = false)
        : ReleaseCall(RC), FuncArgId(argId), PathHash(path), IsNullified(nullified), 
          IsErrorPath(errorPath), is_refcount_release(false) {}
          
    std::string getFieldAccessString() const {
        return PathHash;
    }
    
    // Helper to get vector<int> path from string hash
    const std::vector<int>& getFieldPath() const {
        if (_CacheValid) return _FieldAccessPathCache;
        
        _FieldAccessPathCache.clear();
        if (PathHash.empty()) {
            _CacheValid = true;
            return _FieldAccessPathCache;
        }
        
        std::stringstream ss(PathHash);
        std::string segment;
        while (std::getline(ss, segment, '|')) { 
            if (segment == "*") {
                _FieldAccessPathCache.push_back(-1);
            } else if (segment == "?") {
                _FieldAccessPathCache.push_back(99);
            } else {
                _FieldAccessPathCache.push_back(std::stoi(segment));
            }
            
        }
        _CacheValid = true;
        return _FieldAccessPathCache;
    }
    
    // Compatibility property for Taint.cc accessing FieldAccessPath directly
    // We can't use a property with logic in C++, so Taint.cc needs update to call getFieldPath()
    // OR we just populate a public vector member.
    // Let's populate a public vector member to minimize Taint.cc changes if possible, 
    // but Taint.cc accesses it as RS->FieldAccessPath.
    // So let's just rename the getter or update Taint.cc.
    // Updating Taint.cc is cleaner.
};

// Container for analysis results
class ReleaseWrapperAnalysisResult {
public:
    std::set<Function*> ReleaseWrapperFuncs;
    std::map<CallInst*, std::set<int>> GlobalFreeCallMap;
    
    std::map<std::string, std::map<int, std::vector<ReleaseSummary*>>> GlobalReleaseTransitMap;
    
    // Moved maps here
    std::map<std::string, std::map<CallInst*, std::set<int>>> GlobalAnalyzedReleaseFuncMap;
    std::map<std::string, std::set<CallInst*>> GlobalAnalyzedAllocFuncMap;
    
    bool isReleaseWrapper(Function *F) const {
        return ReleaseWrapperFuncs.count(F) > 0;
    }
    
    std::set<int> getFreeArgIndices(CallInst *CI) const {
        auto it = GlobalFreeCallMap.find(CI);
        if (it != GlobalFreeCallMap.end()) {
            return it->second;
        }
        return std::set<int>();
    }
    
    void clear() {
        ReleaseWrapperFuncs.clear();
        GlobalFreeCallMap.clear();
        GlobalAnalyzedReleaseFuncMap.clear();
        GlobalAnalyzedAllocFuncMap.clear();
        
        for (auto& funcEntry : GlobalReleaseTransitMap) {
            for (auto& argEntry : funcEntry.second) {
                for (ReleaseSummary* rs : argEntry.second) {
                    delete rs;
                }
            }
        }
        GlobalReleaseTransitMap.clear();
    }
};

class ReleaseWrapperAnalyzer {
public:
    GlobalContext *Ctx;
    ReleaseWrapperAnalysisResult Result;
    
    std::map<Function*, AliasContext*> FunctionAliasCache;

    ReleaseWrapperAnalyzer(GlobalContext *Ctx_) 
    : Ctx(Ctx_) {}
    ~ReleaseWrapperAnalyzer() {
        for (auto &Entry : FunctionAliasCache) {
            delete Entry.second;
        }
    }

    void run(Module *M);
    
    AliasContext* GetOrBuildFunctionAlias(Function *F);

private:
    void identifyReleaseFuncs(Function *F);
    void identifyAllocFuncs(Function *F);
    
    void identifyReleaseRange(Function *F, CallInst* free_cai, unsigned free_id, std::vector<std::string> downstream_paths);
    void identifyAllocRange(Function *F, CallInst* alloc_cai);
    
    void checkFreedValueComesFromArg(CallInst* free_cai, unsigned arg_id, 
                                     std::map<int, std::string>& arg_access_map, 
                                     AliasContext* LocalAliasCtx = nullptr,
                                     std::set<Value*>* alloc_values = nullptr);
                                     
    bool checkIfOverwrite(CallInst* free_cai, unsigned free_id, GlobalContext* Ctx, AliasContext* LocalAliasCtx = nullptr);
    bool checkExisitAlloc(Function* F);
    bool checkSingleLineCall(Function* F);
    bool checkExisitRefcountRelease(Function* F);
    bool checkAllocValueReturnToCaller(CallInst* CI);
    
    void getContainerOfArgs(Function *F, unsigned arg_id, std::map<std::string, Value*> &container_map, AliasContext* LocalAliasCtx);
    bool getAliasNodeAccessArr(AliasContext* aCtx, AliasNode *start, AliasNode *end, std::string &access_hash);
    void normalizeAccessHash(std::string &access_hash);
    
    void getFollowingPaths(Instruction *start, std::map<Instruction *, std::vector<BasicBlock *>> &paths_map, bool forward, GlobalContext *Ctx);
};

#endif
