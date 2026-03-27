#ifndef ALLOC_WRAPPER_H
#define ALLOC_WRAPPER_H

#include "Common.h"
#include <set>
#include <map>
#include <string>

struct GlobalContext;

struct AllocWrapperAnalysisResult {
    // Set of functions identified as Allocation Wrappers
    std::set<std::string> AllocWrappers;
    
    // Check if a function is an allocator
    bool isAllocWrapper(const Function *F) const {
        if (!F) return false;
        return AllocWrappers.count(F->getName().str());
    }
    
    void clear() {
        AllocWrappers.clear();
    }
};

class AllocWrapperAnalyzer {
public:
    AllocWrapperAnalysisResult Result;
    GlobalContext *Ctx;
    
    // Base allocators
    std::set<StringRef> BaseAllocators;

    AllocWrapperAnalyzer(GlobalContext *Ctx_) : Ctx(Ctx_) {
        // Initialize base allocators
        BaseAllocators = {
            "kmalloc", "kzalloc", "vmalloc", "kcalloc", "kvmalloc",
            "devm_kzalloc", "devm_kmalloc", "dma_alloc_coherent",
            "alloc_pages", "__alloc_pages_nodemask", "kmem_cache_alloc",
            "kmem_cache_zalloc", "kvzalloc", "vzalloc", "kvcalloc",
            "kmalloc_array", "kcalloc_node", "kmalloc_node",
            "__kmalloc", "__vmalloc", "__devm_alloc_pages"
        };
    }

    void run(Module *M);

private:
    bool analyzeFunction(Function *F);
    bool isAllocationSource(Value *V);
};

#endif
