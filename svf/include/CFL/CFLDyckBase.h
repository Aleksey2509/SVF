
#ifndef INCLUDE_CFL_Dyck_Base_H_
#define INCLUDE_CFL_Dyck_Base_H_

#include "CFL/CFGrammar.h"
#include "Graphs/CFLGraph.h"
#include "LAGraphX.h"
#include "Util/SVFUtil.h"
#include "cfl_idr.h"
#include <cstdlib>
namespace SVF
{

class CFLDyckBase
{
public:
    CFLDyckBase(CFLGraph* graph, CFGrammar* grammar)
        : graph_(graph), grammar_(grammar)
    {
    }
    virtual void setup(
        const std::unordered_map<int, int>& SVFToLAGraphNodes,
        const std::unordered_map<int, int>& LAGraphToSVFNodes) = 0;
    virtual void solve() = 0;
    virtual bool isAccessible(int srcId, int dstId) = 0;

    virtual ~CFLDyckBase() = default;

protected:
    static void checkResult(GrB_Info result, const char* operation,
                            const char* message = nullptr)
    {
        if (result == GrB_SUCCESS)
            return;
        SVFUtil::errs() << "CFL filter operation '" << operation
                        << "' failed with status " << result;
        if (message != nullptr && message[0] != '\0')
            SVFUtil::errs() << ": " << message;
        SVFUtil::errs() << '\n';
        std::abort();
    }

    CFLGraph* graph_;
    CFGrammar* grammar_;
};

} // namespace SVF

#endif
