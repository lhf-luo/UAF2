#include "DereferenceAnalysis.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include <sstream>

using namespace llvm;

void DereferenceAnalyzer::run(Module *M) {
    errs() << "=== Starting Dereference Summary Analysis (Recursive) ===\n";
    Result.clear();
    
    // Pass 1: Local Analysis - Identify functions that directly dereference arguments
    // This acts as the "seeding" phase.
    errs() << "\n[Phase 1] Analyzing direct dereferences...\n";
    
    for (auto &F : *M) {
        if (F.isDeclaration()) continue;
        analyzeFunctionDereferences(&F);
    }
    
    Result.printStatistics();
    errs() << "=== Dereference Summary Analysis Complete ===\n\n";
}

void DereferenceAnalyzer::analyzeFunctionDereferences(Function *F) {
    if (!F || F->isDeclaration()) return;
    
    bool hasPtrArg = false;
    for (auto &Arg : F->args()) {
        if (Arg.getType()->isPointerTy()) { hasPtrArg = true; break; }
    }
    if (!hasPtrArg) return;

    AliasContext *aliasCtx = GetOrBuildFunctionAlias(F);
    
    // Scan instructions for Loads and Stores
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
                checkAndRecordDeref(F, LI->getPointerOperand(), "load", false, aliasCtx);
            }
            else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
                // Ignore storing TO null or FROM constant if relevant, but here we care about the pointer
                checkAndRecordDeref(F, SI->getPointerOperand(), "store", true, aliasCtx);
            }
            else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                // Handle intrinsics/dangerous functions locally
                Function *Callee = CI->getCalledFunction();
                if (Callee) {
                    StringRef Name = Callee->getName();
                    if (IsDangerousFunction(Name)) {
                        for (unsigned i = 0; i < CI->arg_size(); i++) {
                            if (CI->getArgOperand(i)->getType()->isPointerTy()) {
                                checkAndRecordDeref(F, CI->getArgOperand(i), Name.str(), false, aliasCtx);
                            }
                        }
                    }
                }
            }
        }
    }
    
    Result.AnalyzedFuncs.insert(F);
}

void DereferenceAnalyzer::checkAndRecordDeref(Function *F, Value *Ptr, 
                                            const std::string &derefType,
                                            bool isWrite,
                                            AliasContext *aliasCtx) {
    if (!Ptr) return;
    
    AliasNode *ptrNode = getNode(Ptr, aliasCtx);
    if (!ptrNode) return;
    
    // Check if any argument aliases with Ptr
    int argIdx = -1;
    for (auto &Arg : F->args()) {
        argIdx++;
        if (!Arg.getType()->isPointerTy()) continue;
        
        AliasNode *argNode = getNode(&Arg, aliasCtx);
        if (!argNode) continue;
        
        std::string access_hash;
        
        // 1. Check direct reachability
        if (getAliasNodeAccessArr(aliasCtx, argNode, ptrNode, access_hash)) {
            std::vector<int> path = parseAccessHash(access_hash);
            // Trigger Recursive Propagation
            identifyDereferenceRange(F, argIdx, path, derefType, isWrite);
            continue; 
        }
        
        // 2. Check container_of (struct field) reachability
        std::map<std::string, Value*> container_map;
        getContainerOfArgs(F, argIdx, container_map, aliasCtx);
        
        for (auto& pair : container_map) {
            std::string prefix = pair.first;
            if(prefix!=""){
                prefix+="|";
            }
            Value *innerBase = pair.second;
            AliasNode *innerNode = getNode(innerBase, aliasCtx);
            
            if (innerNode && getAliasNodeAccessArr(aliasCtx, innerNode, ptrNode, access_hash)) {
                std::string combined = prefix + access_hash;
                if (!combined .empty() && combined.back() == '|') {
                    combined.pop_back();
                }
                std::vector<int> path = parseAccessHash(combined);
                // Trigger Recursive Propagation
                identifyDereferenceRange(F, argIdx, path, derefType, isWrite);
                break; 
            }
        }
    }
}

// Recursive function similar to ReleaseWrapper's identifyReleaseRange
// Helper to widen paths for convergence
static std::vector<int> widenPath(const std::vector<int>& path) {
    if (path.size() <= 5) return path;
    
    // If path is too long, truncate and add wildcard '99'
    // This abstracts deep recursion into "some deep field"
    std::vector<int> widened;
    for (size_t i = 0; i < 5; i++) {
        widened.push_back(path[i]);
    }
    widened.push_back(99); // 99 represents wildcard/any
    return widened;
}

void DereferenceAnalyzer::identifyDereferenceRange(Function *F, int argIdx, 
                                 const std::vector<int> &path, 
                                 const std::string &derefType,
                                 bool isWrite,
                                 int depth) {
    
    // Depth Limit
    if (depth > 20) return;
    
    // Check Recursion to prevent infinite loops
    auto state = std::make_tuple(F, argIdx, path);
    if (RecursionSet.count(state)) return;
    RecursionSet.insert(state);

    // 1. Check Deduplication
    std::string fname = F->getName().str();
    DereferenceSummary *DS = new DereferenceSummary(fname, argIdx, path, derefType, isWrite);    
    if (!Result.addDerefSummary(DS)) {
        // Summary already exists
        return; 
    }
    
    // 2. Propagate to Callers
    if (!Ctx->Callers.count(F)) return;
    
    for (CallInst *CI : Ctx->Callers[F]) {
        Function *Caller = CI->getFunction();
        if (!Caller || Caller->isDeclaration()) continue;
        
        if (argIdx >= (int)CI->arg_size()) continue;
        Value *ActualArg = CI->getArgOperand(argIdx);
        
        AliasContext *CallerCtx = GetOrBuildFunctionAlias(Caller);
        AliasNode *actualNode = getNode(ActualArg, CallerCtx);
        if (!actualNode) continue;
        
        int callerArgIdx = -1;
        for (auto &Arg : Caller->args()) {
            callerArgIdx++;
            if (!Arg.getType()->isPointerTy()) continue;
            
            AliasNode *callerArgNode = getNode(&Arg, CallerCtx);
            if (!callerArgNode) continue;
            
            std::string access_hash;
            
            auto TriggerCaller = [&](std::string callerPathStr) {
                std::vector<int> callerPath = parseAccessHash(callerPathStr);
                std::vector<int> combined = MergeFieldPaths(callerPath, path);
                
                // Widen path to ensure convergence
                std::vector<int> widened = widenPath(combined);
                
                identifyDereferenceRange(Caller, callerArgIdx, widened, 
                                        derefType, isWrite, depth + 1);
            };
            
            // 1. Direct
            if (getAliasNodeAccessArr(CallerCtx, callerArgNode, actualNode, access_hash)) {
                TriggerCaller(access_hash);
                continue;
            }
            
            // 2. Container
            std::map<std::string, Value*> container_map;
            getContainerOfArgs(Caller, callerArgIdx, container_map, CallerCtx);
            for (auto& pair : container_map) {
                std::string prefix = pair.first;
                AliasNode *innerNode = getNode(pair.second, CallerCtx);
                if (innerNode && getAliasNodeAccessArr(CallerCtx, innerNode, actualNode, access_hash)) {
                    TriggerCaller(prefix + access_hash);
                    break;
                }
            }
        }
    }
}

// Unused legacy method
bool DereferenceAnalyzer::propagateDerefToCaller(Function *Caller, CallInst *CI, Function *Callee) {
    return false;
}

// ====================================================================
// Alias Analysis Helpers (Ported/Shared with ReleaseWrapper)
// ====================================================================

static bool get_field_access_arr_helper(AliasContext* aCtx, AliasNode *start, AliasNode *end, 
    std::vector<int> &field_access_arr, std::set<AliasNode*> &analyzed_set){

    if(start == end) return true;
    if(analyzed_set.count(start)) return false;
    analyzed_set.insert(start);

    if(aCtx->ToNodeMap.count(start)){
        for(auto m : aCtx->ToNodeMap[start]){
            field_access_arr.push_back(m.first); 
            
            bool ret = get_field_access_arr_helper(aCtx, m.second, end, field_access_arr, analyzed_set);
            if(ret) return true;

            field_access_arr.pop_back();
        }
    }
    return false;
}

bool DereferenceAnalyzer::getAliasNodeAccessArr(AliasContext* aCtx, AliasNode *start, 
    AliasNode *end, std::string &access_hash){

    if(start == end) return true;

    std::vector<int> field_access_arr;
    std::set<AliasNode*> analyzed_set;
    if(get_field_access_arr_helper(aCtx, start, end, field_access_arr, analyzed_set)){
        access_hash = "";
        for(int idx : field_access_arr){
            if (idx == -1) { 
                access_hash += "*|";
            } else {
                access_hash += std::to_string(idx) + "|";
            }
        }
        if (!access_hash.empty()) access_hash.pop_back();
        return true;
    }
    return false;
}

static std::set<char> get_unique_symbols(const std::string &str) {
    std::set<char> unique_symbols;
    for (char c : str) {
        if (c != '|' && c != '-'){ 
            unique_symbols.insert(c);
        }
    }
    return unique_symbols;
}

void DereferenceAnalyzer::normalizeAccessHash(std::string &access_hash) {
    // Disabled to prevent corruption of integer field paths
    return;
}

// Use global getContainerOfIndex from FieldSensitiveAlias.h
extern int getContainerOfIndex(GEPOperator *GEP, Value *&OuterV, Value *&InnerV);

void DereferenceAnalyzer::getContainerOfArgs(Function *F, unsigned arg_id, std::map<std::string, Value*> &container_map, AliasContext* LocalAliasCtx){
    if(!F || arg_id >= F->arg_size()) return;

    Argument *arg = F->getArg(arg_id);
    if(!arg->getType()->isPointerTy()) return;
    
    AliasNode *n_arg = getNode(arg, LocalAliasCtx);
    if(!n_arg) return;

    for (Instruction& I : instructions(F)) {
        GEPOperator *GEP = dyn_cast<GEPOperator>(&I);
        if(!GEP) continue;

        Value *OuterV = nullptr;
        Value *InnerV = nullptr;
        int index = -1;
        if((index = getContainerOfIndex(GEP, OuterV, InnerV)) >= 0){
            AliasNode *n_inner = getNode(InnerV, LocalAliasCtx);
            if(!n_inner) continue;

            std::string access_hash = "";
            if(getAliasNodeAccessArr(LocalAliasCtx, n_arg, n_inner, access_hash)){
                    if(access_hash!=""){
                        container_map[access_hash + "|" + std::to_string(index)] = OuterV;
                    }
                    else{
                        container_map[std::to_string(index)] = OuterV;
                    }
                
            }
        }
    }
}

AliasContext* DereferenceAnalyzer::GetOrBuildFunctionAlias(Function *F) {
    if (!F || F->isDeclaration()) return nullptr;
    auto it = FunctionAliasCache.find(F);
    if (it != FunctionAliasCache.end()) return it->second;
    AliasContext *ctx = new AliasContext();
    analyzeFunction(F, ctx, Ctx, true);
    FunctionAliasCache[F] = ctx;
    return ctx;
}

std::vector<int> DereferenceAnalyzer::parseAccessHash(const std::string &hash) {
    std::vector<int> path;
    if (hash.empty()) return path;
    
    std::string temp = hash;
    // Handle normalization if not done
    normalizeAccessHash(temp);
    
    std::stringstream ss(temp);
    std::string segment;
    while (std::getline(ss, segment, '|')) {
        if (segment == "*") path.push_back(-1);
        else { 
            try{
                path.push_back(std::stoi(segment));
            }catch (const std::exception& eee){
                errs()<<eee.what();
            }
        }
    }
    return path;
}

std::vector<int> DereferenceAnalyzer::MergeFieldPaths(const std::vector<int> &prefix, const std::vector<int> &suffix) {
    std::vector<int> result = prefix;
    result.insert(result.end(), suffix.begin(), suffix.end());
    // Basic normalization: remove redundant derefs? 
    // ReleaseWrapper doesn't do deep normalization of vector, just string hash.
    // We keep it simple.
    return result;
}

bool DereferenceAnalyzer::IsDangerousFunction(StringRef FuncName) {
    for (StringRef Dangerous : DangerousFuncs) {
        if (FuncName.contains(Dangerous)) return true;
    }
    return false;
}