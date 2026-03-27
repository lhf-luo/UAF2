#include "NullReturn.h"
#include "Analyzer.h"
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>

using namespace llvm;

void PotentialNullReturnAnalyzer::run(Module *M) {
    bool changed = true;
    
    // Seed: Known external functions that return NULL (Allocators)
    std::set<StringRef> BaseNullReturners = {
        "kmalloc", "kzalloc", "vmalloc", "kcalloc", "kvmalloc",
        "devm_kzalloc", "devm_kmalloc", "dma_alloc_coherent",
        "alloc_pages", "__alloc_pages_nodemask",
        "kmalloc_array", "kcalloc_node", "kmalloc_node",
        "__kmalloc", "__vmalloc", "__devm_alloc_pages",
        "ioremap", "ioremap_nocache",
        "cpufreq_cpu_get_raw"
    };
    
    for (auto Name : BaseNullReturners) {
        Result.NullReturnFunctions.insert(Name.str());
    }

    // Iterative analysis
    while (changed) {
        changed = false;
        for (Function &F : *M) {
            if (F.isDeclaration()) continue;
            if (Result.mayReturnNull(&F)) continue;
            
            // Only analyze pointer-returning functions
            if (!F.getReturnType()->isPointerTy()) continue;

            if (analyzeFunction(&F)) {
                Result.NullReturnFunctions.insert(F.getName().str());
                changed = true;
                // errs() << "Identified Null-Return Function: " << F.getName() << "\n";
            }
        }
    }
}

bool PotentialNullReturnAnalyzer::analyzeFunction(Function *F) {
    for (BasicBlock &BB : *F) {
        if (ReturnInst *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
            Value *RetVal = RI->getReturnValue();
            if (!RetVal) continue;
            
            std::set<Value*> Visited;
            if (isNullSource(RetVal, Visited)) {
                return true;
            }
        }
    }
    return false;
}

bool PotentialNullReturnAnalyzer::isNullSource(Value *V, std::set<Value*> &Visited) {
    if (!V) return false;
    if (Visited.count(V)) return false;
    Visited.insert(V);
    
    // 1. Direct NULL
    if (isa<ConstantPointerNull>(V)) return true;
    
    // 2. PHI
    if (PHINode *PN = dyn_cast<PHINode>(V)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
            if (isNullSource(PN->getIncomingValue(i), Visited)) return true;
        }
    }
    
    // 3. Select
    else if (SelectInst *SI = dyn_cast<SelectInst>(V)) {
        if (isNullSource(SI->getTrueValue(), Visited)) return true;
        if (isNullSource(SI->getFalseValue(), Visited)) return true;
    }
    
    // 4. Call (Propagate)
    else if (CallInst *CI = dyn_cast<CallInst>(V)) {
        Function *Callee = CI->getCalledFunction();
        if (Callee) {
            if (Result.mayReturnNull(Callee)) return true;
        } else {
            // Indirect
            if (Ctx && Ctx->Callees.count(CI)) {
                for (Function *Target : Ctx->Callees[CI]) {
                    if (Result.mayReturnNull(Target)) return true;
                }
            }
        }
    }
    
    // 5. Casts
    else if (CastInst *CI = dyn_cast<CastInst>(V)) {
        return isNullSource(CI->getOperand(0), Visited);
    }

    return false;
}
