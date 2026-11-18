// Call-site IDs are part of identity in graph-wide and node-local edge sets.
#include "Graphs/ConsG.h"
#include <iostream>
#include <limits>

int main()
{
    auto* pag = SVF::SVFIR::getPAG();
    // This fixture does not build the LLVM call graph.
    pag->setCallGraph(nullptr);
    {
        SVF::ConstraintGraph graph(pag);
        graph.addConstraintNode(new SVF::ConstraintNode(1000000), 1000000);
        graph.addConstraintNode(new SVF::ConstraintNode(1000001), 1000001);
        auto* src = graph.getConstraintNode(1000000);
        auto* dst = graph.getConstraintNode(1000001);
        auto initialSize = graph.getDirectCGEdges().size();
        for (auto caller : {SVF::NodeID(0), SVF::NodeID(1), SVF::NodeID(2),
                            std::numeric_limits<SVF::NodeID>::max()})
        {
            auto* call =
                graph.addCallCGEdge(src->getId(), dst->getId(), caller);
            auto* ret = graph.addRetCGEdge(src->getId(), dst->getId(), caller);
            if (call == nullptr || ret == nullptr ||
                call->getCallerID() != caller || ret->getCallerID() != caller ||
                call->getEdgeKind() != SVF::ConstraintEdge::Call ||
                ret->getEdgeKind() != SVF::ConstraintEdge::Ret)
                return 1;
            if (graph.getEdge(src, dst, SVF::ConstraintEdge::Call, caller) !=
                    call ||
                graph.getEdge(src, dst, SVF::ConstraintEdge::Ret, caller) !=
                    ret)
                return 1;
            if (graph.addCallCGEdge(src->getId(), dst->getId(), caller) !=
                    nullptr ||
                graph.addRetCGEdge(src->getId(), dst->getId(), caller) !=
                    nullptr)
                return 1;
        }
        if (graph.getDirectCGEdges().size() != initialSize + 8 ||
            src->getDirectOutEdges().size() != 8 ||
            dst->getDirectInEdges().size() != 8 ||
            src->getOutEdges().size() != 8 || dst->getInEdges().size() != 8)
            return 1;
        if (graph.hasEdge(src, dst, SVF::ConstraintEdge::Call, 3) ||
            graph.hasEdge(src, dst, SVF::ConstraintEdge::Ret, 3) ||
            graph.getEdge(dst, src, SVF::ConstraintEdge::Call, 1) != nullptr)
            return 1;
        if (!graph.hasEdge(src, dst, SVF::ConstraintEdge::Call) ||
            !graph.hasEdge(src, dst, SVF::ConstraintEdge::Ret))
            return 1;
    }
    SVF::SVFIR::releaseSVFIR();
    std::cout << "Call/return edge identity checks passed\n";
    return 0;
}
