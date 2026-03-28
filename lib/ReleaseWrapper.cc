#include "ReleaseWrapper.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include <llvm/IR/InlineAsm.h>
#include <sstream>

using namespace llvm;

// Helper function to get line number
int getInstLineNo(Instruction *I) {
    if (MDNode *N = I->getMetadata("dbg")) {
        DILocation *Loc = dyn_cast<DILocation>(N);
        return Loc->getLine();
    }
    return -1;
}

// ====================================================================
// ReleaseWrapperAnalyzer Implementation
// ====================================================================

void ReleaseWrapperAnalyzer::run(Module *M) {
    errs() << "=== Starting Release Wrapper Analysis (KfsChecker Implementation) ===\n";
    
    Result.clear();
    
    if (Ctx->FreeArgMap.empty() && Ctx->FreeSensitiveFuncs.empty()) {
        Ctx->FreeArgMap["kfree"] = 0;
        Ctx->FreeArgMap["vfree"] = 0;
        Ctx->FreeArgMap["free"] = 0;
        Ctx->FreeArgMap["kvfree"] = 0;
        Ctx->FreeArgMap["kmem_cache_free"] = 1;
        // Manual override for complex/inline wrappers that might be missed
        Ctx->FreeArgMap["ib_destroy_qp"] = 0;
        Ctx->FreeArgMap["ib_destroy_qp_user"] = 0;
        Ctx->FreeArgMap["ib_free_cq"] = 0;
        Ctx->FreeArgMap["ib_dealloc_pd"] = 0;
    }

    // Initialize AllocFuncs if empty
    if (Ctx->AllocFuncs.empty()) {
        Ctx->AllocFuncs.insert("kmalloc");
        Ctx->AllocFuncs.insert("kzalloc");
        Ctx->AllocFuncs.insert("kcalloc");
        Ctx->AllocFuncs.insert("vmalloc");
        Ctx->AllocFuncs.insert("kvmalloc");
        Ctx->AllocFuncs.insert("kvzalloc");
        Ctx->AllocFuncs.insert("kmalloc_node");
        Ctx->AllocFuncs.insert("kzalloc_node");
        Ctx->AllocFuncs.insert("__kmalloc");
        Ctx->AllocFuncs.insert("kmem_cache_alloc");
    }
    
    // Identify Alloc Functions (First!)
    for (auto &F : *M) {
        if (F.isDeclaration()) continue;
        identifyAllocFuncs(&F);
    }

    // Identify Release Functions (Second, using Alloc info)
    for (auto &F : *M) {
        if (F.isDeclaration()) continue;
        identifyReleaseFuncs(&F);
    }
    
    errs() << "=== Release Wrapper Analysis Complete ===\n";
    errs() << "Total release wrappers identified: " << Result.ReleaseWrapperFuncs.size() << "\n";
}

bool ReleaseWrapperAnalyzer::checkExisitAlloc(Function* F){
    for (Instruction& I : instructions(F)) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            string cai_name = getCalledFuncName(CI).str();
            if(Ctx->AllocFuncs.count(cai_name) || Ctx->GlobalAllocTransitMap.count(cai_name)){
                return true;
            }
        }
    }
    return false;
}

bool ReleaseWrapperAnalyzer::checkSingleLineCall(Function* F){
    int call_num = 0;
    int pre_line = -1;
    for (Instruction& I : instructions(F)) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            if(Ctx->DebugFuncs.count(getCalledFuncName(CI).str()))
                continue;

            int cur_line = getInstLineNo(&I);
            if(cur_line != pre_line){
                call_num++;
                pre_line = cur_line;
            } else {
                continue;
            }
            if(call_num > 1){
                return false;
            }
        }
    }
    if(call_num == 1){
        return true;
    }
    return false;
}

bool ReleaseWrapperAnalyzer::checkIfOverwrite(CallInst* free_cai, unsigned free_id, GlobalContext* Ctx, AliasContext* LocalAliasCtx) {
    if(!free_cai) return false;

    Function *F = free_cai->getFunction();
    AliasContext aliasCtx;
    if (LocalAliasCtx == NULL) {
        LocalAliasCtx = &aliasCtx;
        analyzeFunction(F, LocalAliasCtx, Ctx, true);
    }
    Value* free_v = free_cai->getArgOperand(free_id);
    AliasNode *n_free = getNode(free_v, LocalAliasCtx);
    
    if (!n_free || !LocalAliasCtx->FromNodeMap.count(n_free) || !LocalAliasCtx->FromNodeMap[n_free].count(-1)) {
        return false;
    }
    
    AliasNode* n_free_ptr = LocalAliasCtx->FromNodeMap[n_free][-1];
    std::set<AliasNode*> n_free_ptr_set;
    if(n_free_ptr) n_free_ptr_set.insert(n_free_ptr);

    if (n_free_ptr_set.empty()) return false;
    
    set<BasicBlock*> visited;
    list<BasicBlock*> worklist;
    BasicBlock* startBB = free_cai->getParent();
    worklist.push_back(startBB);
    visited.insert(startBB);
    bool found = false;
    
    while(!worklist.empty()){
        BasicBlock* currentBB = worklist.front();
        worklist.pop_front();

        for(Instruction& I : *currentBB) {
            if(CallInst* CI = dyn_cast<CallInst>(&I)){
                if(CI == free_cai){
                    found = true;
                }
            }else if(StoreInst* SI = dyn_cast<StoreInst>(&I)){
                if(!found && currentBB == startBB) {continue;}
                
                Value* store_ptr = SI->getPointerOperand();
                AliasNode* n_store = getNode(store_ptr, LocalAliasCtx);
                if (n_store) {
                    for(auto n_free_ptr : n_free_ptr_set) {
                        if (n_free_ptr == n_store) return true;
                    }
                }
            }
        }

        for(BasicBlock* succ : successors(currentBB)){
            if(succ && visited.find(succ) == visited.end()){
                visited.insert(succ);
                worklist.push_back(succ);
            }
        }
    }
    return false;
}

bool ReleaseWrapperAnalyzer::checkExisitRefcountRelease(Function* F){
    for (Instruction& I : instructions(F)) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            string cai_name = getCalledFuncName(CI).str();
            if(Ctx->RefcountDecFuncs.count(cai_name)){
                return true;
            }
        }
    }
    return false;
}

void ReleaseWrapperAnalyzer::getFollowingPaths(Instruction *start, std::map<Instruction *, std::vector<BasicBlock *>> &paths_map, bool forward, GlobalContext *Ctx) {
    BasicBlock *BB = start->getParent();
    std::vector<BasicBlock*> &paths = paths_map[start];
    std::set<BasicBlock*> visited;
    std::list<BasicBlock*> queue;
    queue.push_back(BB);
    visited.insert(BB);
    
    while(!queue.empty()){
        BasicBlock *curr = queue.front();
        queue.pop_front();
        paths.push_back(curr);
        for (BasicBlock *succ : successors(curr)) {
            if (visited.find(succ) == visited.end()) {
                visited.insert(succ);
                queue.push_back(succ);
            }
        }
    }
}

void ReleaseWrapperAnalyzer::checkFreedValueComesFromArg(CallInst* free_cai, unsigned arg_id,
    std::map<int, std::string>& arg_access_map, AliasContext* LocalAliasCtx, std::set<Value*>* alloc_values) {

    if(!free_cai || arg_id >= free_cai->arg_size()) return;
    
    Value* freed_v = free_cai->getArgOperand(arg_id);
    Function *F = free_cai->getFunction();

    AliasContext aliasCtx;
    set<Value*> local_alloc_values;
    
    if(!LocalAliasCtx) {
        LocalAliasCtx = &aliasCtx;
        alloc_values = &local_alloc_values;
        
        // Flow-sensitive analysis to find allocs reaching this free
        Instruction* firstInst = &*(F->getEntryBlock().begin());
        std::map<Instruction *, std::vector<BasicBlock *>> paths_map;
        getFollowingPaths(firstInst, paths_map, false, Ctx);

        std::set<BasicBlock*> visited;
        bool found = false;
        for (auto& paths_pair : paths_map) {
            for (BasicBlock* BB : paths_pair.second) {
                if(visited.count(BB)) continue;
                visited.insert(BB);
                
                for (Instruction& I : *BB) {
                    HandleInst(&I, LocalAliasCtx, Ctx);
                    if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                        if (CI == free_cai) {
                            found = true;
                            break;
                        } else {
                            string cai_name = getCalledFuncName(CI).str();
                            if(Ctx->DebugFuncs.count(cai_name)) continue;
                            if(Ctx->AllocFuncs.count(cai_name) || Ctx->GlobalAllocTransitMap.count(cai_name)){
                                alloc_values->insert(CI);
                            }
                        }
                    }
                }
                if(found) break;
            }
            if(found) break;
        }
    }

    AliasNode *n_freed_v = getNode(freed_v, LocalAliasCtx);
    if(!n_freed_v) return;
    
    for(Value* alloc_v : *alloc_values){
        if(n_freed_v->count(alloc_v)) return;
    }

    int arg_idx = -1;
    for(auto it = F->arg_begin(); it != F->arg_end();it++){
        arg_idx++;
        Argument *arg = &*it;
        if(!arg->getType()->isPointerTy()) continue;
        
        AliasNode *n_arg = getNode(arg, LocalAliasCtx);
        if(!n_arg) continue;

        string access_hash;
        if(getAliasNodeAccessArr(LocalAliasCtx, n_arg, n_freed_v, access_hash)){
            arg_access_map[arg_idx] = access_hash;
            continue;  
        }

        std::map<std::string, Value*> container_map;
        getContainerOfArgs(F, arg_idx, container_map, LocalAliasCtx);
        for (auto& container_pair : container_map){
            string pre_hash = container_pair.first;
            Value *arg_container = container_pair.second;

            AliasNode* n_arg_container = getNode(arg_container, LocalAliasCtx);
            if(!n_arg_container) continue;

            string access_hash_inner;
            if(getAliasNodeAccessArr(LocalAliasCtx, n_arg_container, n_freed_v, access_hash_inner)){
                access_hash_inner = pre_hash + access_hash_inner;
                arg_access_map[arg_idx] = access_hash_inner;
                continue;  
            }
        }
    }
}

bool ReleaseWrapperAnalyzer::checkAllocValueReturnToCaller(CallInst* CI){
    if(!CI) return false;
    Function *F = CI->getFunction();
    AliasContext LocalAliasCtx;
    analyzeFunction(F, &LocalAliasCtx, Ctx, true);

    AliasNode *n_cai = getNode(CI, &LocalAliasCtx);
    if (!n_cai) return false;
    
    for (Instruction& I : instructions(F)) {
        if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
            if (Value* retVal = RI->getReturnValue()) {
                if(n_cai->count(retVal)) return true;
            }
        }
    }
    return false;
}

void ReleaseWrapperAnalyzer::identifyReleaseRange(Function *F, CallInst* free_cai, unsigned free_id, std::vector<std::string> downstream_paths) {
    // Strict Check: The free call must post-dominate the function entry.
    // This ensures we only identify wrappers that *guaranteed* free the argument.
    // This filters out conditional frees (e.g. error handling in init functions).
    // Exception: If the function returns void, we relax this check because
    // cleanup functions often have 'if (!arg) return;' which breaks post-dominance,
    // but void return strongly implies it's a cleanup function (side-effect only).
    if (!F->getReturnType()->isVoidTy()) {
        PostDominatorTree PDT;
        PDT.recalculate(*F);
        if (!PDT.dominates(free_cai->getParent(), &F->getEntryBlock())) {
            return;
        }
    }

    if(F->getName().contains("mlx5r_umr_resource_cleanup")){
        errs()<<"DEBUG";
    }

    string fname = F->getName().str();
    if(Ctx->FreeArgMap.count(fname) || Ctx->FreeSensitiveFuncs.count(fname)) return;

    /*
    if (Result.GlobalAnalyzedReleaseFuncMap.count(fname) &&
        Result.GlobalAnalyzedReleaseFuncMap[fname].count(free_cai) &&
        Result.GlobalAnalyzedReleaseFuncMap[fname][free_cai].count(free_id)
    ) { return; }
      */
    Result.GlobalAnalyzedReleaseFuncMap[fname][free_cai].insert(free_id);
    
    bool is_error_path_free = false;
    std::map<int, string> arg_access_map;
    
    checkFreedValueComesFromArg(free_cai, free_id, arg_access_map);
    
    if(arg_access_map.empty()) { 
        AliasContext LocalAliasCtx;
        
        // Pass nullptr for LocalAliasCtx and alloc_values to trigger internal flow-sensitive analysis
        checkFreedValueComesFromArg(free_cai, free_id, arg_access_map, nullptr, nullptr);
        
        if(arg_access_map.empty()) return;
        is_error_path_free = true;
    }

    bool is_overwrite = checkIfOverwrite(free_cai, free_id, Ctx);
    std::vector<std::string> next_downstream_paths;

    for (const auto& pair : arg_access_map) {
        string local_path = pair.second;
        normalizeAccessHash(local_path);
        
        for (const string& down_path : downstream_paths) {
            string combined_path = local_path + down_path;
            
            ReleaseSummary *RS = new ReleaseSummary(free_cai, free_id, combined_path, is_overwrite, is_error_path_free);
            Result.GlobalReleaseTransitMap[fname][pair.first].push_back(RS);
            Result.ReleaseWrapperFuncs.insert(F);
            if(checkExisitRefcountRelease(F)) { 
                RS->is_refcount_release = true;
            }
            errs() << "  Identified Wrapper: " << fname << " frees arg[" << pair.first << "] path: " << combined_path << "\n";
            
            next_downstream_paths.push_back(combined_path);
        }
    }


    if (Ctx->Callers.count(F)) {
        const CallInstSet &callers = Ctx->Callers[F];
        for(CallInst* caller_inst : callers){
            if (getCalledFuncName(caller_inst) != fname) continue; 

            unsigned argNum = caller_inst->arg_size();
            if(F->arg_size() != argNum) continue;

            for (const auto& pair : arg_access_map) {
                // Prepare downstream paths for this specific argument
                // We need to filter next_downstream_paths to only those derived from pair.first?
                // Actually, next_downstream_paths contains ALL paths generated for ALL args.
                // We should only pass the paths relevant to 'pair.first' (the arg index passed to caller).
                
                // Re-calculate paths for this specific arg
                std::vector<std::string> paths_for_caller;
                string local_path = pair.second;
                normalizeAccessHash(local_path);
                
                for (const string& down_path : downstream_paths) {
                    string combined_path = local_path + down_path;
                    
                    paths_for_caller.push_back(combined_path);
                }
                
                if (!paths_for_caller.empty())
                    identifyReleaseRange(caller_inst->getFunction(), caller_inst, pair.first, paths_for_caller);
            }
        }
    }
}

void ReleaseWrapperAnalyzer::identifyReleaseFuncs(Function *F){
    if(!F) return;

    for (Instruction& I : instructions(F)) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            string cai_name = getCalledFuncName(CI).str();
            cai_name = stripFuncNameSuffix(cai_name); // Handle .suffix
            string fname = F->getName().str();
            int free_id = 0;
            
            if(Ctx->FreeArgMap.count(cai_name) && !Ctx->FreeSensitiveFuncs.count(fname)) {
                free_id = Ctx->FreeArgMap[cai_name];
            }else if(Ctx->FreeSensitiveFuncs.count(cai_name)) {
                free_id = 0;  
            }else {
                continue;
            }   
            // Base case: downstream path is empty
            std::vector<std::string> base_paths = {""};
            identifyReleaseRange(F, CI, free_id, base_paths);
        }
    }
}

void ReleaseWrapperAnalyzer::identifyAllocRange(Function *F, CallInst* alloc_cai) {
    string fname = F->getName().str();
    if(Ctx->AllocFuncs.count(fname)) return;

    if (Result.GlobalAnalyzedAllocFuncMap.count(fname) &&
        Result.GlobalAnalyzedAllocFuncMap[fname].count(alloc_cai)
    ) { return; }
    Result.GlobalAnalyzedAllocFuncMap[fname].insert(alloc_cai);

    if(!checkAllocValueReturnToCaller(alloc_cai)) return;

    Ctx->GlobalAllocTransitMap[fname].push_back(alloc_cai);

    if(checkSingleLineCall(F)){
        Ctx->SingleLineCallAllocFuncs.insert(fname);
    }

    if (Ctx->Callers.count(F)) {
        const CallInstSet &callers = Ctx->Callers[F];
        for(CallInst* caller_inst : callers){
            if (getCalledFuncName(caller_inst) != fname) continue;

            unsigned argNum = caller_inst->arg_size();
            if(F->arg_size() != argNum) continue;

            identifyAllocRange(caller_inst->getFunction(), caller_inst);
        }
    }
}

void ReleaseWrapperAnalyzer::identifyAllocFuncs(Function *F){
    if(!F) return;

    for (Instruction& I : instructions(F)) {
        if (CallInst *CI = dyn_cast<CallInst>(&I)) {
            string cai_name = getCalledFuncName(CI).str();
            if(Ctx->AllocFuncs.count(cai_name)) {
                identifyAllocRange(F, CI);
            }
        }
    }
}

// ====================================================================
// Alias Analysis Helpers
// ====================================================================

static bool get_field_access_arr(AliasContext* aCtx, AliasNode *start, AliasNode *end, 
    vector<int> &field_access_arr, set<AliasNode*> &analyzed_set){

    if(start == end) return true;
    if(analyzed_set.count(start)) return false;
    analyzed_set.insert(start);

    if(aCtx->ToNodeMap.count(start)){
        for(auto m : aCtx->ToNodeMap[start]){
            field_access_arr.push_back(m.first);
            
            bool ret = get_field_access_arr(aCtx, m.second, end, field_access_arr, analyzed_set);
            if(ret) return true;

            field_access_arr.pop_back();
        }
    }
    return false;
}

bool ReleaseWrapperAnalyzer::getAliasNodeAccessArr(AliasContext* aCtx, AliasNode *start, 
    AliasNode *end, string &access_hash){

    if(start == end) return true;

    vector<int> field_access_arr;
    set<AliasNode*> analyzed_set;
    if(get_field_access_arr(aCtx, start, end, field_access_arr, analyzed_set)){
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

static set<char> get_unique_symbols(const string &str) {
    set<char> unique_symbols;
    for (char c : str) {
        if (c != '|' && c != '-'){
            unique_symbols.insert(c);
        }
    }
    return unique_symbols;
}

void ReleaseWrapperAnalyzer::normalizeAccessHash(string &access_hash) {
    // Disabled to prevent corruption of integer field paths
    return;
}

void ReleaseWrapperAnalyzer::getContainerOfArgs(Function *F, unsigned arg_id, std::map<std::string, Value*> &container_map, AliasContext* LocalAliasCtx){
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

            string access_hash = "";
            if(getAliasNodeAccessArr(LocalAliasCtx, n_arg, n_inner, access_hash)){
                container_map[access_hash + "|" + std::to_string(index)] = OuterV;
            }
        }
    }
}

AliasContext* ReleaseWrapperAnalyzer::GetOrBuildFunctionAlias(Function *F) {
    if (!F || F->isDeclaration()) return nullptr;
    auto it = FunctionAliasCache.find(F);
    if (it != FunctionAliasCache.end()) return it->second;
    AliasContext *ctx = new AliasContext();
    analyzeFunction(F, ctx, Ctx, true);
    FunctionAliasCache[F] = ctx;
    return ctx;
}