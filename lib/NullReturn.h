#ifndef NULL_RETURN_H
#define NULL_RETURN_H

#include "Common.h"
#include <set>
#include <string>

struct GlobalContext;

struct NullReturnAnalysisResult {
    // Set of functions identified as potentially returning NULL
    std::set<std::string> NullReturnFunctions;
    
    bool mayReturnNull(const Function *F) const {
        if (!F) return false;
        return NullReturnFunctions.count(F->getName().str());
    }
    
    void clear() {
        NullReturnFunctions.clear();
    }
};

class PotentialNullReturnAnalyzer {
public:
    NullReturnAnalysisResult Result;
    GlobalContext *Ctx;

    PotentialNullReturnAnalyzer(GlobalContext *Ctx_) : Ctx(Ctx_) {}

    void run(Module *M);

private:
    bool analyzeFunction(Function *F);
    bool isNullSource(Value *V, std::set<Value*> &Visited);
};

#endif
