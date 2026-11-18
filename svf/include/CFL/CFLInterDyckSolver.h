
#ifndef INCLUDE_CFL_InterleavedDyckSolver_H_
#define INCLUDE_CFL_InterleavedDyckSolver_H_

#include "CFL/CFGrammar.h"
#include "CFL/CFLDyckBase.h"
#include "Graphs/CFLGraph.h"
#include "cfl_idr.h"

namespace SVF
{

class CFLInterDyckSolver : public CFLDyckBase
{
public:
    CFLInterDyckSolver(CFLGraph* graph, CFGrammar* grammar)
        : CFLDyckBase(graph, grammar), NormalMatrix{nullptr, nullptr},
          Output{nullptr, nullptr}
    {
        callKind_ = grammar_->strToKind("call");
        retKind_ = grammar_->strToKind("ret");
        gepKind_ = grammar_->strToKind("gep");
        gepBarKind_ = grammar_->strToKind("gepbar");
        bracketKinds = {callKind_, retKind_, gepKind_, gepBarKind_};

        for (auto&& [termStr, termId] : grammar_->getTerminals())
        {
            if (termStr == "call" || termStr == "ret" || termStr == "gep" ||
                termStr == "gepbar" || termStr == "epsilon")
                continue;

            assert(termStr == "load" || termStr == "loadbar" ||
                   termStr == "store" || termStr == "storebar" ||
                   termStr == "addr" || termStr == "addrbar" ||
                   termStr == "copy" || termStr == "copybar" ||
                   termStr == "vgep" || termStr == "vgepbar");

            copyKinds_.insert(termId);
        }
    }

    enum class TermKind : uint8_t
    {
        Normal,
        OpenBracket,
        CloseBracket,
        OpenParenthesis,
        CloseParenthesis,
    };

    // Check for reverse call edges case
    bool isRegularEdge(const CFLEdge* edge)
    {
        auto edgeKind = edge->getEdgeKindWithMask();
        return edgeKind != callKind_ && edgeKind != retKind_ &&
               edgeKind != gepKind_ && edgeKind != gepBarKind_;
    }

    void setMaxInds()
    {
        auto& kindToAttr = grammar_->getKindToAttrsMap();

        if (kindToAttr.count(callKind_))
        {
            auto& calls = kindToAttr.at(callKind_);
            assert(!calls.empty());
            callMaxFunInd = std::max<size_t>(
                *std::max_element(calls.begin(), calls.end()) + 1,
                callMaxFunInd);
        }
        if (kindToAttr.count(retKind_))
        {
            auto& rets = kindToAttr.at(retKind_);
            assert(!rets.empty());
            callMaxFunInd = std::max<size_t>(
                *std::max_element(rets.begin(), rets.end()) + 1, callMaxFunInd);
        }

        if (kindToAttr.count(gepKind_))
        {
            auto& geps = kindToAttr.at(gepKind_);
            assert(!geps.empty());
            gepMaxInd = *std::max_element(geps.begin(), geps.end()) + 1;
        }
    }

    void convertResults(GrB_Matrix matrix)
    {
        GrB_Index nonZeroElems = 0;

        checkResult(GrB_Matrix_nvals(&nonZeroElems, matrix),
                    "GrB_Matrix_nvals");
        std::vector<GrB_Index> rowIndices(nonZeroElems);
        std::vector<GrB_Index> colIndices(nonZeroElems);
        auto vals = std::make_unique<bool[]>(nonZeroElems);
        checkResult(GrB_Matrix_extractTuples_BOOL(rowIndices.data(),
                                                  colIndices.data(), vals.get(),
                                                  &nonZeroElems, matrix),
                    "GrB_Matrix_extractTuples_BOOL");

        for (size_t i = 0; i < nonZeroElems; ++i)
        {
            if (!vals[i])
                continue;

            auto src = LAGraphToSVFNodes[rowIndices[i]];
            auto dst = LAGraphToSVFNodes[colIndices[i]];
            // std::cout << "Got " << rowIndices[i] << " and " << colIndices[i]
            //           << "; originally " << src << " and " << dst << "\n";
            accessibleVertices[src].insert(dst);
            accessibleVertices[dst].insert(src);
        }
        // for (auto& [key, acc] : accessibleVertices)
        // {
        //     std::cout << "For " << key << "\n";
        //     for (auto dst : acc)
        //     {
        //         std::cout << dst << " ";
        //     }
        //     std::cout << "\n";
        // }
    }

    bool isAccessible(int srcId, int dstId) override
    {
        if (srcId == dstId)
            return true;
        if (accessibleVertices.count(srcId) == 0)
            return false;

        return accessibleVertices[srcId].count(dstId) != 0;
    }

    void reset()
    {
        TermToMatrix.clear();
        Output.reset();
        NormalMatrix.reset();
        accessibleVertices.clear();
    }

    void setup(
        const std::unordered_map<int, int>& RefSVFToLAGraphNodes,
        const std::unordered_map<int, int>& RefLAGraphToSVFNodes) override
    {
        SVFToLAGraphNodes = RefSVFToLAGraphNodes;
        LAGraphToSVFNodes = RefLAGraphToSVFNodes;
        reset();
        setMaxInds();
        auto nodeNum = LAGraphToSVFNodes.size();
        NormalMatrix = GrBMatrixOwner{&NormalMatrixHolder, GrB_Matrix_free};
        checkResult(
            GrB_Matrix_new(NormalMatrix.get(), GrB_BOOL, nodeNum, nodeNum),
            "GrB_Matrix_new");

        parenToVec = {
            {TermKind::OpenBracket, std::vector<GrB_Matrix>(callMaxFunInd)},
            {TermKind::CloseBracket, std::vector<GrB_Matrix>(callMaxFunInd)},
            {TermKind::OpenParenthesis, std::vector<GrB_Matrix>(gepMaxInd)},
            {TermKind::CloseParenthesis, std::vector<GrB_Matrix>(gepMaxInd)},
        };

        for (unsigned i = 0; i < callMaxFunInd; ++i)
        {
            std::unordered_set brackets{TermKind::OpenBracket,
                                        TermKind::CloseBracket};
            for (auto bracketKind : brackets)
            {
                TermToMatrix[bracketKind].push_back(GrBMatrixOwner{
                    &parenToVec[bracketKind][i], GrB_Matrix_free});
                GrB_Matrix* curTermMatrix = TermToMatrix[bracketKind][i].get();
                checkResult(
                    GrB_Matrix_new(curTermMatrix, GrB_BOOL, nodeNum, nodeNum),
                    "GrB_Matrix_new");
            }
        }

        for (unsigned i = 0; i < gepMaxInd; ++i)
        {
            std::unordered_set parenthesis{TermKind::OpenParenthesis,
                                           TermKind::CloseParenthesis};
            for (auto parentesisKind : parenthesis)
            {
                TermToMatrix[parentesisKind].push_back(GrBMatrixOwner{
                    &parenToVec[parentesisKind][i], GrB_Matrix_free});
                GrB_Matrix* curTermMatrix =
                    TermToMatrix[parentesisKind][i].get();
                checkResult(
                    GrB_Matrix_new(curTermMatrix, GrB_BOOL, nodeNum, nodeNum),
                    "GrB_Matrix_new");
            }
        }

        std::unordered_map<int, std::unordered_set<int>> callOrRetEdges;
        for (auto& edgeIt : graph_->getCFLEdges())
        {
            auto edgeKind = edgeIt->getEdgeKindWithMask();
            auto srcId = SVFToLAGraphNodes.at(edgeIt->getSrcID());
            auto dstId = SVFToLAGraphNodes.at(edgeIt->getDstID());
            if (edgeKind == callKind_ || edgeKind == retKind_)
            {
                callOrRetEdges[srcId].insert(dstId);
                callOrRetEdges[srcId].insert(srcId);
            }
        }

        for (auto& edgeIt : graph_->getCFLEdges())
        {
            auto edgeKind = edgeIt->getEdgeKindWithMask();
            auto srcId = SVFToLAGraphNodes.at(edgeIt->getSrcID());
            auto dstId = SVFToLAGraphNodes.at(edgeIt->getDstID());

            auto attribute = edgeIt->getEdgeAttri();
            if (copyKinds_.count(edgeKind) == 0 &&
                bracketKinds.count(edgeKind) == 0)
            {
                continue;
            }
            if (bracketKinds.count(edgeKind) == 0 ||
                ((edgeKind == gepKind_ || edgeKind == gepBarKind_) &&
                 (attribute == 0 || unsigned(attribute) >= gepMaxInd)))
            {
                if ((callOrRetEdges.count(srcId) > 0 &&
                     callOrRetEdges[srcId].count(dstId) > 0) ||
                    (callOrRetEdges.count(dstId) > 0 &&
                     callOrRetEdges[dstId].count(srcId) > 0))
                {
                    // std::cout << "Skipped " << srcId << " and " << dstId
                    //           << " originally: " << LAGraphToSVFNodes[srcId]
                    //           << " and " << LAGraphToSVFNodes[dstId] << "\n";
                    continue;
                }

                // std::cout << "Setting reg between " << srcId << " and " <<
                // dstId
                //           << " originally: " << LAGraphToSVFNodes[srcId]
                //           << " and " << LAGraphToSVFNodes[dstId] << "\n";

                checkResult(GrB_Matrix_setElement_BOOL(*NormalMatrix, true,
                                                       srcId, dstId),
                            "GrB_Matrix_setElement_BOOL");
                checkResult(GrB_Matrix_setElement_BOOL(*NormalMatrix, true,
                                                       dstId, srcId),
                            "GrB_Matrix_setElement_BOOL");
                continue;
            }

            if (edgeKind == callKind_)
            {
                // std::cout << "Setting call between " << srcId << " and "
                //           << dstId
                //           << " originally: " << LAGraphToSVFNodes[srcId]
                //           << " and " << LAGraphToSVFNodes[dstId] << "\n";
                GrB_Matrix* curTermMatrix =
                    TermToMatrix[TermKind::OpenBracket][attribute].get();
                checkResult(GrB_Matrix_setElement_BOOL(*curTermMatrix, true,
                                                       srcId, dstId),
                            "GrB_Matrix_setElement_BOOL");
            }
            else if (edgeKind == retKind_)
            {
                // std::cout << "Setting ret between " << srcId << " and " <<
                // dstId
                //           << " originally: " << LAGraphToSVFNodes[srcId]
                //           << " and " << LAGraphToSVFNodes[dstId] << "\n";
                GrB_Matrix* curTermMatrix =
                    TermToMatrix[TermKind::CloseBracket][attribute].get();
                checkResult(GrB_Matrix_setElement_BOOL(*curTermMatrix, true,
                                                       srcId, dstId),
                            "GrB_Matrix_setElement_BOOL");
            }
            else if (edgeKind == gepKind_ || edgeKind == gepBarKind_)
            {
                if (edgeKind == gepBarKind_)
                    std::swap(srcId, dstId);
                // std::cout << "Setting gep from " << srcId << " to " << dstId
                //           << " originally: " << LAGraphToSVFNodes[srcId]
                //           << " and " << LAGraphToSVFNodes[dstId]
                //           << " with value " << attribute << "\n";
                GrB_Matrix* gepTermMatrix =
                    TermToMatrix[TermKind::OpenParenthesis][attribute].get();
                checkResult(GrB_Matrix_setElement_BOOL(*gepTermMatrix, true,
                                                       srcId, dstId),
                            "GrB_Matrix_setElement_BOOL");
                GrB_Matrix* gepBarTermMatrix =
                    TermToMatrix[TermKind::CloseParenthesis][attribute].get();
                checkResult(GrB_Matrix_setElement_BOOL(*gepBarTermMatrix, true,
                                                       dstId, srcId),
                            "GrB_Matrix_setElement_BOOL");
            }
            else
            {
                assert(false && "unreachable");
            }
        }
    }

    void solve() override
    {
        Output = GrBMatrixOwner{&OutputHolder, GrB_Matrix_free};

        IdrGraph input{};
        input.n = LAGraphToSVFNodes.size();
        input.normal = *NormalMatrix.get();

        input.n_bra = callMaxFunInd;
        input.open_bra = parenToVec[TermKind::OpenBracket].data();
        input.close_bra = parenToVec[TermKind::CloseBracket].data();

        input.n_par = gepMaxInd;
        input.open_par = parenToVec[TermKind::OpenParenthesis].data();
        input.close_par = parenToVec[TermKind::CloseParenthesis].data();
        checkResult(idr_get_over_approx(Output.get(), &input, IDR_DEFAULT, NULL,
                                        false, false),
                    "idr_get_over_approx");
        convertResults(OutputHolder);
        Output.reset();
    }

private:
    std::unordered_set<int> copyKinds_;
    std::unordered_set<int> bracketKinds;
    int callKind_;
    int retKind_;
    int gepKind_;
    int gepBarKind_;
    size_t callMaxFunInd = 0;
    size_t gepMaxInd = 0;
    using GrBMatrixOwner =
        std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>;
    using GrBMatrixArray = std::vector<GrBMatrixOwner>;

    std::unordered_map<int, int> LAGraphToSVFNodes;
    std::unordered_map<int, int> SVFToLAGraphNodes;

    GrB_Matrix NormalMatrixHolder = nullptr;
    GrB_Matrix OutputHolder = nullptr;
    std::unordered_map<TermKind, std::vector<GrB_Matrix>> parenToVec;

    // TODO Check with sanitizers the correctness of destruction
    GrBMatrixOwner NormalMatrix;
    GrBMatrixOwner Output;
    std::unordered_map<TermKind, GrBMatrixArray> TermToMatrix;

    std::unordered_map<int, std::unordered_set<int>> accessibleVertices;
};
}; // namespace SVF
#endif
