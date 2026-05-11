
#ifndef INCLUDE_CFL_DyckSolver_H_
#define INCLUDE_CFL_DyckSolver_H_

#include "CFL/CFGrammar.h"
#include "CFL/CFLDyckBase.h"
#include "Graphs/CFLGraph.h"
#include "LAGraphX.h"

namespace SVF
{

class CFLDyckSolver : public CFLDyckBase
{
    enum NonIndexedSymbols
    {
        S_NonTerm = 0,
        R_NonTerm,
        N_Term,
        LastNonIndexed,
    };

public:
    CFLDyckSolver(CFLGraph* graph, CFGrammar* grammar, int openKind,
                  int closeKind)
        : CFLDyckBase(graph, grammar), openKind_(openKind),
          closeKind_(closeKind)

    {
        auto terminals = grammar_->getTerminals();
        if (terminals.count("epsilon"))
            epsilonKind_ = terminals["epsilon"];
        setupGrammar();
    }

    // Grammar:
    // S -> R S | (_i S | eps
    // R -> (_i R )_i R | normal R | eps
    //
    // S -> R S
    // S -> O_i S
    // S -> eps
    //
    // R -> O_i A_i
    // A_i -> R B_i
    // B_i -> C_i R
    // R -> eps
    // R -> normal
    //
    // O_i -> (_i
    // C_i -> )_i
    void setupGrammar()
    {
        auto getMaxKind = [](auto& kindToAttrsMap, int kind) -> unsigned {
            if (kindToAttrsMap.count(kind) == 0)
                return 1;
            auto necessaryMap = kindToAttrsMap.at(kind);
            return *std::max_element(necessaryMap.begin(), necessaryMap.end()) +
                   1;
        };
        auto& kindToAttrsMap = grammar_->getKindToAttrsMap();
        noParens = kindToAttrsMap.count(openKind_) == 0;

        auto maxOpenKind = getMaxKind(kindToAttrsMap, openKind_);
        auto maxCloseKind = getMaxKind(kindToAttrsMap, closeKind_);

        auto indexVal = std::max(maxOpenKind, maxCloseKind);

        openParenInd = LastNonIndexed;
        closeParenInd = openParenInd + indexVal;

        int openParenNT = closeParenInd + indexVal;
        int closeParenNT = openParenNT + indexVal;

        int A_NT = closeParenNT + indexVal;
        int B_NT = A_NT + indexVal;
        symbolsCount = B_NT + indexVal;

        LAGraphRules.clear();
        // S -> R S
        LAGraphRules.push_back({.nonterm = S_NonTerm,
                                .prod_A = R_NonTerm,
                                .prod_B = S_NonTerm,
                                .indexed_count = 0,
                                .indexed = 0});
        // S -> O_i S
        LAGraphRules.push_back({.nonterm = S_NonTerm,
                                .prod_A = openParenNT,
                                .prod_B = S_NonTerm,
                                .indexed_count = indexVal,
                                .indexed = LAGraph_EWNCF_INDEX_PROD_A});
        // S -> eps
        LAGraphRules.push_back({.nonterm = S_NonTerm,
                                .prod_A = -1,
                                .prod_B = -1,
                                .indexed_count = 0,
                                .indexed = 0});
        // R -> O_i A_i
        LAGraphRules.push_back({.nonterm = R_NonTerm,
                                .prod_A = openParenNT,
                                .prod_B = A_NT,
                                .indexed_count = indexVal,
                                .indexed = LAGraph_EWNCF_INDEX_PROD_A |
                                           LAGraph_EWNCF_INDEX_PROD_B});
        // A_i -> R B_i
        LAGraphRules.push_back({.nonterm = A_NT,
                                .prod_A = R_NonTerm,
                                .prod_B = B_NT,
                                .indexed_count = indexVal,
                                .indexed = LAGraph_EWNCF_INDEX_NONTERM |
                                           LAGraph_EWNCF_INDEX_PROD_B});
        // B_i -> C_i R
        LAGraphRules.push_back({.nonterm = B_NT,
                                .prod_A = closeParenNT,
                                .prod_B = R_NonTerm,
                                .indexed_count = indexVal,
                                .indexed = LAGraph_EWNCF_INDEX_NONTERM |
                                           LAGraph_EWNCF_INDEX_PROD_A});
        // R -> eps
        LAGraphRules.push_back({.nonterm = R_NonTerm,
                                .prod_A = -1,
                                .prod_B = -1,
                                .indexed_count = 0,
                                .indexed = 0});
        // R -> normal
        LAGraphRules.push_back({.nonterm = R_NonTerm,
                                .prod_A = N_Term,
                                .prod_B = -1,
                                .indexed_count = 0,
                                .indexed = 0});
        // // O_i -> (_i
        LAGraphRules.push_back({.nonterm = openParenNT,
                                .prod_A = openParenInd,
                                .prod_B = -1,
                                .indexed_count = indexVal,
                                .indexed = LAGraph_EWNCF_INDEX_NONTERM |
                                           LAGraph_EWNCF_INDEX_PROD_A});
        // // C_i -> )_i
        LAGraphRules.push_back({.nonterm = closeParenNT,
                                .prod_A = closeParenInd,
                                .prod_B = -1,
                                .indexed_count = indexVal,
                                .indexed = LAGraph_EWNCF_INDEX_NONTERM |
                                           LAGraph_EWNCF_INDEX_PROD_A});
    }

    void convertGraphToLAGraph()
    {
        adjMatricesHolder.resize(symbolsCount);
        adjMatrices.clear();
        adjMatrices.reserve(symbolsCount);
        nodeNum = graph_->getTotalNodeNum();

        for (int i = 0; i != int(symbolsCount); ++i)
        {
            adjMatrices.push_back(
                std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>{
                    &adjMatricesHolder[i], GrB_Matrix_free});
            GrB_Matrix* curTermMatrix = adjMatrices[i].get();
            assert(GrB_Matrix_new(curTermMatrix, GrB_BOOL, nodeNum, nodeNum) ==
                   GrB_SUCCESS);
        }

        auto nonTerms = grammar_->getNonterminals();
        std::unordered_set<int> nonTermsKinds;
        for (auto&& [nonTermStr, nonTermKind] : nonTerms)
        {
            nonTermsKinds.insert(nonTermKind);
        }

        std::unordered_map<int, std::unordered_set<int>> callOrRetEdges;
        for (auto& edgeIt : graph_->getCFLEdges())
        {
            auto edgeKind = edgeIt->getEdgeKindWithMask();
            auto srcId = SVFToLAGraphNodes.at(edgeIt->getSrcID());
            auto dstId = SVFToLAGraphNodes.at(edgeIt->getDstID());
            if (edgeKind == openKind_ || edgeKind == closeKind_)
            {
                callOrRetEdges[srcId].insert(dstId);
                callOrRetEdges[dstId].insert(srcId);
            }
        }

        for (auto& edgeIt : graph_->getCFLEdges())
        {
            auto SVFSymbol = GrammarBase::Symbol(edgeIt->getEdgeKind());
            auto symbKind = SVFSymbol.kind;
            if (symbKind == epsilonKind_ || nonTermsKinds.count(symbKind) > 0)
                continue;

            auto srcId = SVFToLAGraphNodes.at(edgeIt->getSrcID());
            auto dstId = SVFToLAGraphNodes.at(edgeIt->getDstID());

            int term = N_Term;
            // TODO Check this
            if (symbKind == openKind_)
            {
                term = openParenInd + SVFSymbol.attribute;
            }
            else if (symbKind == closeKind_)
            {
                term = closeParenInd + SVFSymbol.attribute;
            }
            else if (callOrRetEdges.count(srcId) > 0 &&
                     callOrRetEdges[srcId].count(dstId) > 0)
                continue;
            // if (SVFSymbol.attribute > 2)
            // {
            //     term = N_Term;
            // }

            GrB_Matrix* curTermMatrix = adjMatrices[term].get();
            assert(GrB_Matrix_setElement_BOOL(*curTermMatrix, true, srcId,
                                              dstId) == GrB_SUCCESS);
        }
    }

    void setup(
        const std::unordered_map<int, int>& RefSVFToLAGraphNodes,
        const std::unordered_map<int, int>& RefLAGraphToSVFNodes) override
    {
        SVFToLAGraphNodes = RefSVFToLAGraphNodes;
        LAGraphToSVFNodes = RefLAGraphToSVFNodes;
        convertGraphToLAGraph();
    }

    void convertResults(GrB_Matrix matrix)
    {
        GrB_Index nonZeroElems = 0;

        assert(GrB_Matrix_nvals(&nonZeroElems, matrix) == 0 &&
               "On matrix nonzero element amount extraction");
        std::vector<GrB_Index> rowIndices(nonZeroElems);
        std::vector<GrB_Index> colIndices(nonZeroElems);
        auto vals = std::make_unique<bool[]>(nonZeroElems);
        assert(GrB_Matrix_extractTuples_BOOL(
                   rowIndices.data(), colIndices.data(), vals.get(),
                   &nonZeroElems, matrix) == GrB_SUCCESS);

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

    void solve() override
    {
        if (noParens)
            return;
        std::vector<GrB_Matrix> inputs(adjMatrices.size());
        std::transform(adjMatrices.begin(), adjMatrices.end(), inputs.begin(),
                       [](const auto& uniq_ptr) { return *uniq_ptr; });
        std::vector<GrB_Matrix> outputs(symbolsCount);
        std::transform(outputs.begin(), outputs.end(), outputs.begin(),
                       [this](GrB_Matrix mat) {
                           GrB_Matrix_new(&mat, GrB_BOOL, nodeNum, nodeNum);
                           return mat;
                       });

        assert(LAGraph_CFL_reachability_adv(outputs.data(), inputs.data(),
                                            symbolsCount, LAGraphRules.data(),
                                            LAGraphRules.size(), nullptr,
                                            1 | 4 | 8) == GrB_SUCCESS);
        convertResults(outputs[0]);
    }

    bool isAccessible(int srcId, int dstId) override
    {
        if (noParens)
            return true;
        if (srcId == dstId)
            return true;
        if (accessibleVertices.count(srcId) == 0)
            return false;

        return accessibleVertices[srcId].count(dstId) != 0;
    }

    unsigned openKind_;
    unsigned closeKind_;
    unsigned epsilonKind_ = -1;
    ;
    int openParenInd{};
    int closeParenInd{};
    int symbolsCount{};
    int nodeNum{};

    bool noParens = false;

    std::unordered_map<int, int> LAGraphToSVFNodes;
    std::unordered_map<int, int> SVFToLAGraphNodes;

    std::vector<LAGraph_rule_EWCNF> LAGraphRules;
    std::vector<GrB_Matrix> adjMatricesHolder;
    std::vector<std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>>
        adjMatrices;

    std::unordered_map<int, std::unordered_set<int>> accessibleVertices;
};

} // namespace SVF

#endif
