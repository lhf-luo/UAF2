#ifndef _DEREFERENCE_ANALYSIS_H
#define _DEREFERENCE_ANALYSIS_H

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

#include "Common.h"
#include "FieldSensitiveAlias.h"
#include "Analyzer.h"

using namespace llvm;

struct DereferenceSummary {
    std::string FunctionName;
    int ArgIndex;                      // 参数索引
    std::vector<int> FieldAccessPath;  // 被解引用的字段路径
    std::string DerefType;             // 解引用类型: "load", "store", "call", "memcpy" 等
    bool IsWrite;                      // 是否是写操作
    
    DereferenceSummary(const std::string &fname, int argIdx, 
                       const std::vector<int> &path, 
                       const std::string &type,
                       bool isWrite = false)
        : FunctionName(fname), ArgIndex(argIdx), 
          FieldAccessPath(path), DerefType(type), IsWrite(isWrite) {}
    
    std::string getFieldAccessString() const {
        if (FieldAccessPath.empty()) return "direct";
        
        std::string result;
        for (size_t i = 0; i < FieldAccessPath.size(); i++) {
            int idx = FieldAccessPath[i];
            if (idx == -1) result += "*";
            else if (idx == 99) result += "?";
            else result += std::to_string(idx);
            
            if (i < FieldAccessPath.size() - 1) result += ".";
        }
        return result;
    }
};

class DereferenceAnalysisResult {
public:
    std::map<std::string, std::map<int, std::vector<DereferenceSummary*>>> GlobalDerefMap;
    std::set<Function*> AnalyzedFuncs;
    std::set<std::string> DeduplicationKeys;
    
    bool hasDerefInfo(Function *F) const {
        if (!F) return false;
        return GlobalDerefMap.count(F->getName().str()) > 0;
    }
    
    std::vector<DereferenceSummary*> getDerefPaths(Function *F, int argIdx) const {
        if (!F) return {};
        auto funcIt = GlobalDerefMap.find(F->getName().str());
        if (funcIt == GlobalDerefMap.end()) return {};
        auto argIt = funcIt->second.find(argIdx);
        if (argIt == funcIt->second.end()) return {};
        return argIt->second;
    }
    
    std::map<int, std::vector<DereferenceSummary*>>* getAllDerefPaths(Function *F) {
        if (!F) return nullptr;
        auto funcIt = GlobalDerefMap.find(F->getName().str());
        if (funcIt == GlobalDerefMap.end()) return nullptr;
        return &funcIt->second;
    }
    
    std::string makeDeduplicationKey(const std::string &fname, int argIdx,
                                     const std::vector<int> &path,
                                     const std::string &derefType) {
        std::string key = fname + "_arg" + std::to_string(argIdx) + "_[";
        for (int idx : path) {
            key += std::to_string(idx) + ",";
        }
        key += "]_" + derefType;
        return key;
    }
    
    bool addDerefSummary(DereferenceSummary *DS) {
        std::string key = makeDeduplicationKey(
            DS->FunctionName, DS->ArgIndex, 
            DS->FieldAccessPath, DS->DerefType
        );
        
        if (DeduplicationKeys.count(key)) {
            delete DS;
            return false;
        }
        
        DeduplicationKeys.insert(key);
        GlobalDerefMap[DS->FunctionName][DS->ArgIndex].push_back(DS);
        return true;
    }
    
    void clear() {
        for (auto &funcEntry : GlobalDerefMap) {
            for (auto &argEntry : funcEntry.second) {
                for (auto *DS : argEntry.second) {
                    delete DS;
                }
            }
        }
        GlobalDerefMap.clear();
        AnalyzedFuncs.clear();
        DeduplicationKeys.clear();
    }
    
    void printStatistics() const {
        errs() << "\n=== Dereference Analysis Statistics ===\n";
        errs() << "Total functions analyzed: " << AnalyzedFuncs.size() << "\n";
        errs() << "Functions with deref info: " << GlobalDerefMap.size() << "\n";
        int totalSummaries = 0;
        for (const auto &funcEntry : GlobalDerefMap) {
            for (const auto &argEntry : funcEntry.second) {
                totalSummaries += argEntry.second.size();
            }
        }
        errs() << "Total deref summaries: " << totalSummaries << "\n";
        errs() << "========================================\n\n";
    }
};

class DereferenceAnalyzer {
public:
    DereferenceAnalysisResult Result;
    GlobalContext *Ctx;
    std::set<StringRef> DangerousFuncs;
    std::map<Function*, AliasContext*> FunctionAliasCache;

    DereferenceAnalyzer(GlobalContext *Ctx_) : Ctx(Ctx_) {
        DangerousFuncs = {
            "memcpy", "strcpy", "strlen", "sprintf", "printf", "fprintf",
            "memset", "memmove", "strcat", "strcmp", "strncmp", "sscanf"
        };
    }
    
    ~DereferenceAnalyzer() {
        for (auto &Entry : FunctionAliasCache) {
            delete Entry.second;
        }
    }

    void run(Module *M);
    bool IsDangerousFunction(StringRef FuncName);

private:
    void analyzeFunctionDereferences(Function *F);
    
    void identifyDereferenceRange(Function *F, int argIdx, 
                                 const std::vector<int> &path, 
                                 const std::string &derefType,
                                 bool isWrite,
                                 int depth = 0);

    void checkAndRecordDeref(Function *F, Value *Ptr, 
                            const std::string &derefType,
                            bool isWrite,
                            AliasContext *aliasCtx);
                            
    bool propagateDerefToCaller(Function *Caller, CallInst *CI, Function *Callee);
    
    // Alias analysis helpers adapted from ReleaseWrapper
    void getContainerOfArgs(Function *F, unsigned arg_id, std::map<std::string, Value*> &container_map, AliasContext* LocalAliasCtx);
    bool getAliasNodeAccessArr(AliasContext* aCtx, AliasNode *start, AliasNode *end, std::string &access_hash);
    void normalizeAccessHash(std::string &access_hash);
    
    std::vector<int> parseAccessHash(const std::string &hash);
    std::vector<int> MergeFieldPaths(const std::vector<int> &prefix, const std::vector<int> &suffix);
    
    // Internal helper for creating/caching alias context
    AliasContext* GetOrBuildFunctionAlias(Function *F);
    
    // Recursion tracking
    std::set<std::tuple<Function*, int, std::vector<int>>> RecursionSet;
};

#endif
