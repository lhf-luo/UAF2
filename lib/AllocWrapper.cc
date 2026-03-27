#include "AllocWrapper.h"
#include "Analyzer.h"
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>

using namespace llvm;

void AllocWrapperAnalyzer::run(Module *M) {
    bool changed = true;
    
    // Iteratively identify wrappers
    while (changed) {
        changed = false;
        for (Function &F : *M) {
            if (F.isDeclaration()) continue;
            if (Result.isAllocWrapper(&F)) continue;
            
            if (analyzeFunction(&F)) {
                Result.AllocWrappers.insert(F.getName().str());
                changed = true;
                errs() << "Identified Alloc Wrapper: " << F.getName() << "\n";
            }
        }
    }
}

bool AllocWrapperAnalyzer::analyzeFunction(Function *F) {
    // Check if return value comes from an allocator
    // We scan all return instructions. If ANY return path returns an allocation result,
    // we consider it a wrapper (it propagates the allocation).
    
    for (BasicBlock &BB : *F) {
        if (ReturnInst *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
            Value *RetVal = RI->getReturnValue();
            // Handle void returns or simple constants
            if (!RetVal || isa<Constant>(RetVal)) continue; 
            
            // Allow returning NULL as part of wrapper (handled in isAllocationSource via Select/Phi?)
            // No, we want to find if it returns a NEW allocation.
            // If it returns NULL, it doesn't prove it's an allocator.
            
            if (isAllocationSource(RetVal)) {
                return true;
            }
        }
    }
    return false;
}

bool AllocWrapperAnalyzer::isAllocationSource(Value *V) {
    if (!V) return false;
    
    // Avoid cycles?
    // Since we iterate functions in run(), we use current state of Result.
    // Inside a function, we trace Use-Def.
    // If we have a loop in Use-Def (e.g. PHI), we need to be careful.
    // We can use a visited set for local trace.
    static std::set<Value*> Visited;
    if (Visited.count(V)) return false;
    Visited.insert(V);
    
    bool isAlloc = false;

    // Handle PHI
    if (PHINode *PN = dyn_cast<PHINode>(V)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
            if (isAllocationSource(PN->getIncomingValue(i))) {
                isAlloc = true;
                break;
            }
        }
    }
    
    // Handle Casts
    else if (CastInst *CI = dyn_cast<CastInst>(V)) {
        isAlloc = isAllocationSource(CI->getOperand(0));
    }
    
    // Handle Call
    else if (CallInst *CI = dyn_cast<CallInst>(V)) {
        Function *Callee = CI->getCalledFunction();
        if (Callee) {
            StringRef Name = Callee->getName();
            if (BaseAllocators.count(Name)) isAlloc = true;
            else if (Result.AllocWrappers.count(Name.str())) isAlloc = true;
        } else {
            // Indirect
            if (Ctx && Ctx->Callees.count(CI)) {
                for (Function *Target : Ctx->Callees[CI]) {
                    StringRef Name = Target->getName();
                    if (BaseAllocators.count(Name)) { isAlloc = true; break; }
                    if (Result.AllocWrappers.count(Name.str())) { isAlloc = true; break; }
                }
            }
        }
    }
    
    // Handle Select
    else if (SelectInst *SI = dyn_cast<SelectInst>(V)) {
        isAlloc = isAllocationSource(SI->getTrueValue()) || isAllocationSource(SI->getFalseValue());
    }
    
    Visited.erase(V);
    return isAlloc;
}
