#ifndef _ANALYZER_GLOBAL_H
#define _ANALYZER_GLOBAL_H

#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include "llvm/Support/CommandLine.h"
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include "Common.h"

// Forward declaration
struct ReleaseSummary;

// 
// typedefs
//
typedef std::vector< std::pair<llvm::Module*, llvm::StringRef> > ModuleList;
// Mapping module to its file name.
typedef std::unordered_map<llvm::Module*, llvm::StringRef> ModuleNameMap;
// The set of all functions.
typedef llvm::SmallPtrSet<llvm::Function*, 8> FuncSet;
// The set of strings.
typedef std::set<std::string> StrSet;
// The pair of an array and its size
typedef std::pair<std::string*, int> ArrayPair;
// The set of string pairs.
typedef std::set<std::pair<std::string, std::string>> StrPairSet;
// Mapping from function name to function.
typedef std::unordered_map<std::string, llvm::Function*> NameFuncMap;
typedef llvm::SmallPtrSet<llvm::CallInst*, 8> CallInstSet;
typedef DenseMap<Function*, CallInstSet> CallerMap;
typedef DenseMap<CallInst *, FuncSet> CalleeMap;
typedef std::pair<std::string, AllocaInst*> TyRepkeypair;

// 表示一个错误处理路径段
struct ErrorHandlingPath {
    Function *Func;
    BasicBlock *EntryBB;  // 路径入口基本块
    std::vector<BasicBlock*> PathBlocks;  // 路径上的基本块序列
    std::set<CallInst*> CallSites;        // 路径上的函数调用点
    bool IsFromErrorReturn;               // 是否来自错误返回
    
    ErrorHandlingPath(Function *F, BasicBlock *Entry) 
        : Func(F), EntryBB(Entry), IsFromErrorReturn(false) {}
};

// 全局错误处理CFG
struct GlobalErrorHandlingCFG {
    // 每个函数的错误处理路径
    std::map<Function*, std::vector<ErrorHandlingPath*>> FunctionPaths;
    
    // 跨函数连接：调用点到目标函数的错误处理路径
    std::map<CallInst*, std::vector<ErrorHandlingPath*>> CallToTargetPaths;
    
    // 反向映射：从被调用函数的路径回到调用点
    std::map<ErrorHandlingPath*, std::set<CallInst*>> PathToCallers;
    
    // 所有error handling基本块（用于快速查询）
    std::set<BasicBlock*> AllErrorHandlingBlocks;
    
    ~GlobalErrorHandlingCFG() {
        for (auto &Entry : FunctionPaths) {
            for (auto *Path : Entry.second) {
                delete Path;
            }
        }
    }
};

struct GlobalContext {

	GlobalContext() {
		// Initialize statistucs.
		NumFunctions = 0;
		NumFirstLayerTypeCalls = 0;
		NumSecondLayerTypeCalls = 0;
		NumIndirectCallTargets = 0;
		NoTargetCalls = 0; 		// Number of indirect calls which have no target
		ZerotTargetCalls = 0;		// [1,2) 2^0 ~ 2^1
		OnetTargetCalls = 0;		// [2,4) 2^1 ~
		TwotTargetCalls = 0;		// [4,8) 2^2 ~
		ThreetTargetCalls = 0;		// [8,16) 2^3 ~
		FourtTargetCalls = 0;		// [16,32) 2^4 ~
		FivetTargetCalls = 0;		// [32,64) 2^5 ~
		SixtTargetCalls = 0;		// [64,128) 2^6 ~
		SeventTargetCalls = 0;		// [128,256) 2^7 ~
		EighttTargetCalls = 0;		// [256,...) 2^8 ~
	}

	// Statistics 
	unsigned NumFunctions;
	unsigned NumFirstLayerTypeCalls;
	unsigned NumSecondLayerTypeCalls;
	unsigned NumIndirectCallTargets;
	unsigned NoTargetCalls;
	unsigned ZerotTargetCalls;
	unsigned OnetTargetCalls;
	unsigned TwotTargetCalls;
	unsigned ThreetTargetCalls;
	unsigned FourtTargetCalls;
	unsigned FivetTargetCalls;
	unsigned SixtTargetCalls;
	unsigned SeventTargetCalls;
	unsigned EighttTargetCalls;
	unsigned NumThreeLayerType;
	

	// Map global function GUID (uint64_t) to its actual function with body.
	map<uint64_t, Function*> GlobalFuncMap;

	// Functions whose addresses are taken.
	FuncSet AddressTakenFuncs;

	// Map a callsite to all potential callee functions.
	CalleeMap Callees;

	// Map a function to all potential caller instructions.
	CallerMap Callers;

	// Unified functions -- no redundant inline functions
	DenseMap<size_t, Function *>UnifiedFuncMap;
	set<Function *>UnifiedFuncSet;

	// Map function signature to functions
	DenseMap<size_t, FuncSet>sigFuncsMap;

	// Indirect call instructions.
	std::vector<CallInst *>IndirectCallInsts;

	// Modules.
	ModuleList Modules;
	ModuleNameMap ModuleMaps;
	std::set<std::string> InvolvedModules;

	set<CallInst *> CallSet;
	
	FuncSet TargetFuncs;
	FuncSet CalleeFuncSet;
	
	FuncSet ErrorReturnFuncs;
	set<pair<Function *, Function*>> ErrorReturnToTarget;

	// Error handling basic block
	std::set<BasicBlock* > ErrorHandleBBs;

	GlobalErrorHandlingCFG GlobalEHCFG;

	set<string> DebugFuncs;
	map<string, tuple<int8_t, int8_t, int8_t>> CopyFuncs;

    // KfsChecker Additions
    std::set<std::string> AllocFuncs;
    std::set<std::string> RefcountDecFuncs;
    std::map<std::string, std::vector<CallInst*>> GlobalAllocTransitMap;
    std::set<std::string> FreeSensitiveFuncs; 
    std::map<std::string, int> FreeArgMap;    
    std::set<std::string> SingleLineCallAllocFuncs;
    // ReleaseSummary will be defined in ReleaseWrapper.h, using void* here to break dependency cycle or we need to restructure headers
    // Actually, we can move ReleaseSummary definition to a common header or just forward declare if possible.
    // For now, let's keep it simple and assume ReleaseWrapper.h is included where needed, 
    // but here we need to store the map.
    // To avoid circular deps, I will use a forward declaration and pointer in map value if possible, 
    // or include ReleaseWrapper.h but that might cause issues if Analyzer.h is included there.
    // Better approach: Define ReleaseSummary in a separate struct or keep it in ReleaseWrapper.h and 
    // Analyzer.h doesn't need to know about GlobalReleaseTransitMap if it's managed by the pass.
    // BUT kfsChecker puts GlobalReleaseTransitMap in GlobalContext.
    // So we need to support it.
    
    // We will use a template or void* hack, or better, move ReleaseSummary definition here.
    // Let's defer adding GlobalReleaseTransitMap to GlobalContext for a moment and see if we can keep it in ReleaseWrapperPass.
    // kfsChecker uses Ctx->GlobalReleaseTransitMap.
    
    // Let's add the map using a forward declared struct pointer.
    std::map<std::string, std::map<int, std::vector<ReleaseSummary*>>> GlobalReleaseTransitMap;

	struct ErrorCFGEdge {
		Function *Source;     // Error-returning function
		Function *Target;     // Function that propagates the error
		CallInst *CallSite;   // The call instruction connecting them
		
		ErrorCFGEdge(Function *S, Function *T, CallInst *CI) 
			: Source(S), Target(T), CallSite(CI) {}
		
		// For using in std::set
		bool operator<(const ErrorCFGEdge &Other) const {
			if (Source != Other.Source)
				return Source < Other.Source;
			if (Target != Other.Target)
				return Target < Other.Target;
			return CallSite < Other.CallSite;
		}
	};
	
	// The CFG as a collection of edges
	std::set<ErrorCFGEdge> ErrorPropagationCFG;
	
	// Helper methods for the CFG
	void addErrorPropagationEdge(Function *Source, Function *Target, CallInst *CallSite) {
		ErrorPropagationCFG.insert(ErrorCFGEdge(Source, Target, CallSite));
	}
	
	// Get all error sources for a function
	std::vector<Function*> getErrorSources(Function *Target) {
		std::vector<Function*> Sources;
		for (const auto &Edge : ErrorPropagationCFG) {
			if (Edge.Target == Target) {
				Sources.push_back(Edge.Source);
			}
		}
		return Sources;
	}
	
	// Get all functions that might receive errors from this function
	std::vector<Function*> getErrorTargets(Function *Source) {
		std::vector<Function*> Targets;
		for (const auto &Edge : ErrorPropagationCFG) {
			if (Edge.Source == Source) {
				Targets.push_back(Edge.Target);
			}
		}
		return Targets;
	}
};

class IterativeModulePass : public ModulePass{
	static char PassID;
protected:
	GlobalContext *Ctx;
	const char * ID;
public:
	IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
		: ModulePass(PassID), Ctx(Ctx_), ID(ID_) {
			errs()<<"debug iterive ";
		 }

	// Run on each module before iterative pass.
	virtual bool doInitialization(Module *M)
		{ return true; }

	// Run on each module after iterative pass.
	virtual bool doFinalization(llvm::Module *M)
		{ return true; }

	// Iterative pass.
	virtual bool runOnModule(llvm::Module *M)
		{ return false; }
	
	bool runOnModule(llvm::Module &M)
		{ return false; }

	virtual void run(ModuleList &modules);
};

//char IterativeModulePass::PassID;

#endif