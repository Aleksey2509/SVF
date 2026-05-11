
#ifndef INCLUDE_CFL_Dyck_Base_H_
#define INCLUDE_CFL_Dyck_Base_H_

#include "CFL/CFGrammar.h"
#include "Graphs/CFLGraph.h"
#include "LAGraphX.h"
#include "cfl_idr.h"
namespace SVF
{

class CFLDyckBase
{
public:
    CFLDyckBase(CFLGraph* graph, CFGrammar* grammar)
        : graph_(graph), grammar_(grammar)
    {
    }
    virtual void setup(const std::unordered_map<int, int>& SVFToLAGraphNodes,
                       const std::unordered_map<int, int>& LAGraphToSVFNodes) = 0;
    virtual void solve() = 0;
    virtual bool isAccessible(int srcId, int dstId) = 0;

protected:
    CFLGraph* graph_;
    CFGrammar* grammar_;
};

} // namespace SVF

#endif
