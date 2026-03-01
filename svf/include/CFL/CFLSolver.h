//===----- CFLSolver.h -- Context-free language reachability solver--------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * CFLSolver.h
 *
 *  Created on: March 5, 2022
 *      Author: Yulei Sui， Yuxiang Lei
 */

#ifndef INCLUDE_CFL_CFLSolver_H_
#define INCLUDE_CFL_CFLSolver_H_

#include "CFL/CFGrammar.h"
#include "GraphBLAS.h"
#include "Graphs/CFLGraph.h"
#include "LAGraphX.h"
#include "Util/WorkList.h"
#include <algorithm>

using namespace std;

namespace SVF
{
typedef GrammarBase::Symbol Label;

class CFLSolver
{

public:
    /// Define worklist
    typedef FIFOWorkList<const CFLEdge*> WorkList;
    typedef CFGrammar::Production Production;
    typedef CFGrammar::Symbol Symbol;

    static double numOfChecks;

    CFLSolver(CFLGraph* _graph, CFGrammar* _grammar): graph(_graph), grammar(_grammar)
    {
    }

    virtual ~CFLSolver()
    {
        delete graph;
        delete grammar;
    }

    /// Initialize worklist
    virtual void initialize();

    /// Process CFLEdge
    virtual void processCFLEdge(const CFLEdge* Y_edge);

    /// Start solving
    virtual void solve();

    /// Return CFL Graph
    inline const CFLGraph* getGraph() const
    {
        return graph;
    }

    /// Return CFL Grammar
    inline const CFGrammar* getGrammar() const
    {
        return grammar;
    }
    virtual inline bool pushIntoWorklist(const CFLEdge* item)
    {
        return worklist.push(item);
    }
    virtual inline bool isWorklistEmpty()
    {
        return worklist.empty();
    }

protected:
    /// Worklist operations
    //@{
    inline const CFLEdge* popFromWorklist()
    {
        return worklist.pop();
    }

    inline bool isInWorklist(const CFLEdge* item)
    {
        return worklist.find(item);
    }
    //@}

protected:
    CFLGraph* graph;
    CFGrammar* grammar;
    /// Worklist for resolution
    WorkList worklist;
};

struct MTXSolver : public CFLSolver
{
    MTXSolver(CFLGraph* _graph, CFGrammar* _grammar)
        : CFLSolver(_graph, _grammar)
    {
        LAGraph_Init(nullptr);
        setupGraphNodesMaps();
        setupNonTermMaps();
        setupTermMaps();
        convertGrammarToLAGraphRules();
    }
    std::vector<LAGraph_rule_WCNF> rules;
    std::unordered_map<GrammarBase::Symbol, GrammarBase::Productions,
                       CFGrammar::SymbolHash>
        origRules;

    std::unordered_map<GrammarBase::Symbol, int, CFGrammar::SymbolHash>
        SVFToLAGraphNonTerm;
    std::unordered_map<int, GrammarBase::Symbol> LAGraphToSVFNonTerm;
    std::unordered_map<GrammarBase::Symbol, int, CFGrammar::SymbolHash>
        SVFToLAGraphTerm;
    std::unordered_map<int, GrammarBase::Symbol> LAGraphToSVFTerm;

    std::unordered_map<GrammarBase::Symbol, int, CFGrammar::SymbolHash>
        SVFTermToLAGraphNonTerm;
    std::unordered_map<int, GrammarBase::Symbol> LAGraphNonTermToSVFTerm;

    std::unordered_map<int, int> SVFToLAGraphNodes;
    std::unordered_map<int, int> LAGraphToSVFNodes;

    std::vector<GrB_Matrix> adjMatricesHolder;
    std::vector<std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>>
        adjMatrices;

    int termsCount{};
    int nonTermsCount{};
    size_t nodeNum{};
    bool yetToBeSolved = false;

    inline bool pushIntoWorklist(const CFLEdge* item) override
    {
        auto LAGraphTerm = GrammarBase::Symbol(item->getEdgeKind());
        if (SVFToLAGraphTerm.count(LAGraphTerm) == 0)
            return false;

        auto srcId = SVFToLAGraphNodes.at(item->getSrcID());
        auto dstId = SVFToLAGraphNodes.at(item->getDstID());
        auto edgeKind = SVFToLAGraphTerm.at(LAGraphTerm);
        assert(edgeKind != -1);

        GrB_Matrix* curTermMatrix = adjMatrices[edgeKind].get();
        bool x = false;
        auto ret_val =
            GrB_Matrix_extractElement_BOOL(&x, *curTermMatrix, srcId, dstId);
        assert(ret_val == GrB_SUCCESS || ret_val == GrB_NO_VALUE);
        if ((ret_val == GrB_SUCCESS) && x)
            return false;

        assert(GrB_Matrix_setElement_BOOL(*curTermMatrix, true, srcId, dstId) ==
               GrB_SUCCESS);
        yetToBeSolved = true;

        return true;
    }

    inline bool isWorklistEmpty() override
    {
        return !yetToBeSolved;
    }

    int convertToLAGraph(int SVFTermOrNonTerm);

    void setupTermMaps();
    void setupNonTermMaps();

    void setupGraphNodesMaps();

    void handleSingleNonTermRules();
    void convertGrammarToLAGraphRules();

    void convertGraphToLAGraph();

    void convertResultsFromLAGraph(const std::vector<GrB_Matrix>& outputs);

    void initialize() override
    {
        convertGraphToLAGraph();
        yetToBeSolved = true;
    }

    void print()
    {
        std::cout << "Printing edges\n";
        for (auto&& it : graph->getCFLEdges())
        {
            auto i = it->getSrcID();
            auto j = it->getDstID();
            auto y = it->getEdgeKind();
            std::cout << "from " << i << " to " << j << " kind " << y << "\n";
        }
        for (std::size_t adjMatNum = 0; adjMatNum != adjMatrices.size();
             ++adjMatNum)
        {
            auto adjMat = adjMatrices[adjMatNum].get();
            for (std::size_t i = 0; i != nodeNum; ++i)
            {
                for (std::size_t j = 0; j != nodeNum; ++j)
                {
                    bool x = false;
                    auto ret_val =
                        GrB_Matrix_extractElement_BOOL(&x, *adjMat, i, j);
                    assert(ret_val == GrB_SUCCESS || ret_val == GrB_NO_VALUE);
                    if (x)
                        std::cout << "from " << i << " to " << j << " kind "
                                  << LAGraphToSVFTerm[adjMatNum] << "\n";
                }
            }
        }
    }
    void solve() override
    {
        initialize();
        std::vector<GrB_Matrix> inputs(adjMatrices.size());
        std::transform(adjMatrices.begin(), adjMatrices.end(), inputs.begin(),
                       [](const auto& uniq_ptr) { return *uniq_ptr; });

        std::vector<GrB_Matrix> outputs(nonTermsCount);
        std::transform(outputs.begin(), outputs.end(), outputs.begin(),
                       [this](GrB_Matrix mat) {
                           GrB_Matrix_new(&mat, GrB_BOOL, nodeNum, nodeNum);
                           return mat;
                       });

        LAGraph_CFL_reachability(outputs.data(), inputs.data(), termsCount,
                                 nonTermsCount, rules.data(), rules.size(),
                                 nullptr);
        yetToBeSolved = false;
        worklist.clear();
        convertResultsFromLAGraph(std::move(outputs));

        // CFLSolver::solve();
    }
};

struct MTXAdvancedSolver : public CFLSolver
{
    MTXAdvancedSolver(CFLGraph* _graph, CFGrammar* _grammar)
        : CFLSolver(_graph, _grammar)
    {
        int i = 0;
        for (auto&& [node_id, node_ptr] : *graph)
        {
            SVFToLAGraphNodes[node_id] = i;
            LAGraphToSVFNodes[i] = node_id;
            ++i;
        }
        setupRules();
    }

    void insertSymbols(
        const std::unordered_set<int>& symbolsSet,
        const std::unordered_map<int, int>& SymbolKindToMaxAttrVal)
    {
        for (auto sym : symbolsSet)
        {
            if (SVFToLAGraphSymbol.count(sym))
                continue;
            auto maxVal = maxAttrValOrZero(sym);
            CFGrammar::Symbol newNonTermSymbol = sym;
            for (int i = 0; i != maxVal + 1; ++i)
            {
                SVFToLAGraphSymbol[newNonTermSymbol] = symbolsCount;
                LAGraphToSVFSymbol[symbolsCount] = newNonTermSymbol;
                ++symbolsCount;
                ++newNonTermSymbol.attribute;
            }
        }
    }

    void setupRules()
    {
        std::unordered_map<std::vector<Symbol>, CFGrammar::Productions,
                           CFGrammar::SymbolVectorHash>
            ProductionToIndices;

        for (auto& [termName, termId] : grammar->getTerminals())
            origTerms.insert(termId);
        for (auto& [termName, termId] : grammar->getNonterminals())
            origNonTerms.insert(termId);

        auto UpdateSymbolMaxIndex = [this](CFGrammar::Symbol sym) {
            if (sym.attribute == 0)
                return;
            SymbolKindToMaxAttrVal[sym.kind] =
                std::max<int>(sym.attribute, SymbolKindToMaxAttrVal[sym.kind]);
        };

        CFGrammar::Symbol epsilonTerm = 0;
        if (grammar->getTerminals().count("epsilon"))
        {
            epsilonTerm = grammar->strToKind("epsilon");
            SVFToLAGraphSymbol[epsilonTerm] = -1;
            LAGraphToSVFSymbol[-1] = epsilonTerm;
        }

        for (auto& prod : grammar->getEpsilonProds())
        {
            auto& nonterm = grammar->getLHSSymbol(prod);
            assert(origTerms.count(nonterm.kind) == 0);

            UpdateSymbolMaxIndex(nonterm);

            CFGrammar::Symbol zeroedNonTerm = nonterm.kind;
            origRules[zeroedNonTerm].insert({epsilonTerm});
        }

        for (auto& [singleRhs, prods_vec] : grammar->getSingleRHSToProds())
        {
            for (auto& prod : prods_vec)
            {
                auto& nonterm = grammar->getLHSSymbol(prod);
                auto rhs = prod.at(1);
                assert(origTerms.count(nonterm.kind) == 0);

                UpdateSymbolMaxIndex(nonterm);
                UpdateSymbolMaxIndex(rhs);

                CFGrammar::Symbol zeroedNonTerm = nonterm.kind;
                CFGrammar::Symbol zeroedRhs = rhs.kind;
                origRules[zeroedNonTerm].insert({zeroedRhs});
            }
        }

        for (auto& [firstRhs, prods_vec] : grammar->getFirstRHSToProds())
        {
            for (auto& prod : prods_vec)
            {
                auto& Nonterm = grammar->getLHSSymbol(prod);
                assert(origTerms.count(Nonterm.kind) == 0);
                auto FirstRhs = prod.at(1);
                auto SecondRhs = prod.at(2);

                UpdateSymbolMaxIndex(Nonterm);
                UpdateSymbolMaxIndex(FirstRhs);
                UpdateSymbolMaxIndex(SecondRhs);

                CFGrammar::Symbol zeroedNonTerm = Nonterm.kind;
                CFGrammar::Symbol zeroedFirstRhs = FirstRhs.kind;
                CFGrammar::Symbol zeroedSecondRhs = SecondRhs.kind;
                origRules[zeroedNonTerm].insert(
                    {zeroedFirstRhs, zeroedSecondRhs});
            }
        }

        auto StartNonTerm = grammar->getStartKind();
        auto maxVal = 0;
        if (SymbolKindToMaxAttrVal.count(StartNonTerm) > 0)
        {
            maxVal = SymbolKindToMaxAttrVal.at(StartNonTerm);
        }
        CFGrammar::Symbol newNonTermSymbol = StartNonTerm;
        for (int i = 0; i != maxVal + 1; ++i)
        {
            SVFToLAGraphSymbol[newNonTermSymbol] = symbolsCount;
            LAGraphToSVFSymbol[symbolsCount] = newNonTermSymbol;
            ++symbolsCount;
            ++newNonTermSymbol.attribute;
        }

        // TODO Check for max to be the same??
        bool changed_max_attr = true;
        while (changed_max_attr)
        {
            changed_max_attr = false;
        }

        insertSymbols(origTerms, SymbolKindToMaxAttrVal);
        insertSymbols(origNonTerms, SymbolKindToMaxAttrVal);
    }

    void checkIndices()
    {
        std::unordered_set<Symbol, CFGrammar::SymbolHash> ToHandle;
        std::unordered_map<Symbol, int, CFGrammar::SymbolHash>
            SymbolToMaxAttrVal;

        std::unordered_set<int> WithZero;
        std::unordered_set<int> WithNonZero;

        std::unordered_map<int, std::unordered_set<int>>
            IndexedNonTermToIndexedTerms;
        std::unordered_map<int, int> IndexedSymbolToMaxVal;

        for (auto& [term, indValues] : grammar->getKindToAttrsMap())
        {
            auto maxVal = *std::max_element(indValues.begin(), indValues.end());
            IndexedSymbolToMaxVal.insert({term, maxVal});

            for (auto& rule : grammar->getProdsFromSingleRHS(term))
            {
                IndexedNonTermToIndexedTerms[grammar->getLHSSymbol(rule).kind]
                    .insert(term);
            }
            for (auto& rule : grammar->getProdsFromFirstRHS(term))
            {
                IndexedNonTermToIndexedTerms[grammar->getLHSSymbol(rule).kind]
                    .insert(term);
            }
            for (auto& rule : grammar->getProdsFromSecondRHS(term))
            {
                IndexedNonTermToIndexedTerms[grammar->getLHSSymbol(rule).kind]
                    .insert(term);
            }
        }

        for (auto& [nonTerm, indexedTerms] : IndexedNonTermToIndexedTerms)
        {
            auto MaxVal = IndexedSymbolToMaxVal[*indexedTerms.begin()];
            bool EqualMaxVals =
                std::all_of(indexedTerms.begin(), indexedTerms.end(),
                            [&IndexedSymbolToMaxVal, MaxVal](int kind) {
                                return IndexedSymbolToMaxVal.at(kind) == MaxVal;
                            });

            assert(EqualMaxVals &&
                   "Non term with different max values of terminals!!!\n");
            IndexedSymbolToMaxVal[nonTerm] = MaxVal;
        }

        for (auto& [nonTerm, prodsSet] : grammar->getRawProductions())
        {
            if (nonTerm.variableAttribute)
            {
                if (WithZero.count(nonTerm.kind))
                    assert(false &&
                           "Non term appeared both with and without index!!");
                WithNonZero.insert(nonTerm.kind);
            }

            if (!nonTerm.variableAttribute)
            {
                if (WithNonZero.count(nonTerm.kind))
                    assert(false &&
                           "Non term appeared both with and without index!!");
                WithZero.insert(nonTerm.kind);
            }
        }

        for (auto&& [nonTerm, prodsSet] : origRules)
        {
            if (nonTerm.attribute != 0)
            {
                ToHandle.insert(nonTerm.kind);
            }
        }
        for (auto& nonTerm : ToHandle)
        {
            auto SymbolToCheck = GrammarBase::Symbol(nonTerm);
            auto PrevAttrSymbol = GrammarBase::Symbol(nonTerm);
            auto RefProds = origRules.at(SymbolToCheck);
            ++SymbolToCheck.attribute;
            while (origRules.count(SymbolToCheck))
            {
                auto ProdsToCheck = origRules[SymbolToCheck];
                for (auto& prod : ProdsToCheck)
                {
                    GrammarBase::Production ProdWithDecrementedAttr;
                    std::transform(prod.begin(), prod.end(),
                                   std::back_inserter(ProdWithDecrementedAttr),
                                   [](const Symbol& sym) {
                                       auto newSym = sym;
                                       if (newSym.attribute)
                                           --newSym.attribute;
                                       return newSym;
                                   });
                    assert(origRules[PrevAttrSymbol].count(
                               ProdWithDecrementedAttr) > 0 &&
                           "Must have same rule with one smaller!!\n");

                    for (auto& sym : prod)
                    {
                        if (sym.attribute != 0)
                        {
                            if (sym.attribute != SymbolToCheck.attribute)
                                assert(false &&
                                       "The attribute values are not equal!!");
                        }
                    }
                    PrevAttrSymbol = SymbolToCheck;
                    ++SymbolToCheck.attribute;
                }
            }
        }
    }

    void convertGraphToLAGraph()
    {
        LAGraph_Init(nullptr);

        // terminal to edge map
        std::unordered_map<int, std::vector<std::pair<int, int>>> adjMat;
        nodeNum = graph->getTotalNodeNum();
        assert(SVFToLAGraphNodes.size() == nodeNum);

        // TODO Wrong? Should account for additional indices of symbols,
        // added when finding max of index
        adjMatricesHolder.resize(symbolsCount);
        adjMatrices.clear();
        adjMatrices.reserve(symbolsCount);
        for (int i = 0; i != int(symbolsCount); ++i)
        {
            adjMatrices.push_back(
                std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>{
                    &adjMatricesHolder[i], GrB_Matrix_free});
            GrB_Matrix* curTermMatrix = adjMatrices[i].get();
            assert(GrB_Matrix_new(curTermMatrix, GrB_BOOL, nodeNum, nodeNum) ==
                   GrB_SUCCESS);
        }

        for (auto& edgeIt : graph->getCFLEdges())
        {
            auto SVFSymbol = GrammarBase::Symbol(edgeIt->getEdgeKind());
            int edgeKind = SVFToLAGraphSymbol.at(SVFSymbol);
            if (edgeKind == -1)
                continue;

            auto srcId = SVFToLAGraphNodes.at(edgeIt->getSrcID());
            auto dstId = SVFToLAGraphNodes.at(edgeIt->getDstID());
            GrB_Matrix* curTermMatrix = adjMatrices[edgeKind].get();
            assert(GrB_Matrix_setElement_BOOL(*curTermMatrix, true, srcId,
                                              dstId) == GrB_SUCCESS);
        }
    }

    int maxAttrValOrZero(int kind)
    {
        if (SymbolKindToMaxAttrVal.count(kind))
            return SymbolKindToMaxAttrVal.at(kind);
        return 0;
    }

    // TODO Maybe bad design? Do not use out params?
    auto getProdInfo(int svfKind, bool prodA, uint8_t& indexedTermsUpdate,
                     int& maxAttrVal)
    {
        auto maxSingleRhsInd = maxAttrValOrZero(svfKind) + 1;
        if (maxSingleRhsInd > 1)
        {
            auto update =
                prodA ? LAGraph_EWNCF_INDEX_PROD_A : LAGraph_EWNCF_INDEX_PROD_B;
            indexedTermsUpdate |= update;
        }
        assert(!(maxAttrVal > 1 && maxSingleRhsInd > 1 &&
                 maxAttrVal != maxSingleRhsInd) &&
               "Different maximums!!");
        maxAttrVal = std::max(maxSingleRhsInd, maxAttrVal);
        auto singleRhsTermLAGraph = SVFToLAGraphSymbol.at(svfKind);

        return singleRhsTermLAGraph;
    }

    std::vector<LAGraph_rule_EWCNF> initRules()
    {
        std::vector<LAGraph_rule_EWCNF> rules;
        rules.reserve(origRules.size());

        for (auto&& [nonTerm, prods] : origRules)
        {
            auto nonTermIndexCount = maxAttrValOrZero(nonTerm.kind) + 1;
            uint8_t nonTermIndexed =
                nonTermIndexCount > 1 ? LAGraph_EWNCF_INDEX_NONTERM : 0;
            auto nonTermLAGraph = SVFToLAGraphSymbol.at(nonTerm.kind);

            for (auto&& prod : prods)
            {
                auto indexedCount = nonTermIndexCount;
                uint8_t indexedSymbols = nonTermIndexed;

                assert(prod.size() == 1 || prod.size() == 2);
                int prodA =
                    getProdInfo(prod[0], true, indexedSymbols, indexedCount);
                int prodB = -1;
                if (prod.size() == 2)
                    prodB = getProdInfo(prod[1], false, indexedSymbols,
                                        indexedCount);

                rules.push_back(LAGraph_rule_EWCNF{
                    .nonterm = nonTermLAGraph,
                    .prod_A = prodA,
                    .prod_B = prodB,
                    .indexed_count = static_cast<uint32_t>(indexedCount),
                    .indexed = indexedSymbols});
            }
        }

        return rules;
    }

    void convertResultsFromLAGraph(const std::vector<GrB_Matrix>& outputs)
    {
        for (int LAGraphSymbolId = 0, endI = outputs.size();
             LAGraphSymbolId != endI; ++LAGraphSymbolId)
        {
            auto SVFSymbol = LAGraphToSVFSymbol.at(LAGraphSymbolId);
            // if (origTerms.count(SVFSymbol.kind))
            //     continue;

            auto matrix = outputs[LAGraphSymbolId];
            for (size_t i = 0; i != nodeNum; ++i)
            {
                for (size_t j = 0; j != nodeNum; ++j)
                {
                    bool x = false;
                    auto ret_val =
                        GrB_Matrix_extractElement_BOOL(&x, matrix, i, j);
                    assert(ret_val == GrB_SUCCESS || ret_val == GrB_NO_VALUE);
                    if (x)
                    {
                        auto* SrcNode =
                            graph->getGNode(LAGraphToSVFNodes.at(i));
                        auto* DstNode =
                            graph->getGNode(LAGraphToSVFNodes.at(j));
                        graph->addCFLEdge(SrcNode, DstNode, SVFSymbol);
                        // std::cout << "Got from " << SrcNode->getId() << " to
                        // "
                        //           << DstNode->getId() << " symbol "
                        //           << grammar->kindToStr(SVFSymbol.kind)
                        //           << " which was " << LAGraphSymbolId <<
                        //           "\n";
                    }
                }
            }
        }
    }

    static void playground()
    {
        std::vector<GrB_Matrix> adjMatricesHolder;
        std::vector<std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>>
            testInput;
        int symbols_count = 5;
        int nodeNum = 3;

        adjMatricesHolder.resize(symbols_count);
        for (int i = 0; i != int(symbols_count); ++i)
        {
            testInput.push_back(
                std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>{
                    &adjMatricesHolder[i], GrB_Matrix_free});
            GrB_Matrix* curTermMatrix = testInput[i].get();
            assert(GrB_Matrix_new(curTermMatrix, GrB_BOOL, nodeNum, nodeNum) ==
                   GrB_SUCCESS);
        }
        assert(GrB_Matrix_setElement_BOOL(*(testInput[0].get()), true, 0, 1) ==
               GrB_SUCCESS);
        assert(GrB_Matrix_setElement_BOOL(*(testInput[2].get()), true, 1, 2) ==
               GrB_SUCCESS);

        std::vector<GrB_Matrix> inputs(testInput.size());
        std::transform(testInput.begin(), testInput.end(), inputs.begin(),
                       [](const auto& uniq_ptr) { return *uniq_ptr; });

        std::vector<GrB_Matrix> outputs(symbols_count);
        std::transform(outputs.begin(), outputs.end(), outputs.begin(),
                       [nodeNum](GrB_Matrix mat) {
                           GrB_Matrix_new(&mat, GrB_BOOL, nodeNum, nodeNum);
                           return mat;
                       });
        std::vector<LAGraph_rule_EWCNF> rules;
        rules.push_back({
            .nonterm = 3,
            .prod_A = 0,
            .prod_B = 1,
            .indexed_count = 2,
            .indexed = LAGraph_EWNCF_INDEX_NONTERM | LAGraph_EWNCF_INDEX_PROD_B,
        });

        LAGraph_CFL_reachability_adv(outputs.data(), inputs.data(),
                                     symbols_count, rules.data(), rules.size(),
                                     nullptr, 0);
        for (int LAGraphSymbolId = 0, endI = outputs.size();
             LAGraphSymbolId != endI; ++LAGraphSymbolId)
        {
            auto matrix = outputs[LAGraphSymbolId];
            for (int i = 0; i != nodeNum; ++i)
            {
                for (int j = 0; j != nodeNum; ++j)
                {
                    bool x = false;
                    auto ret_val =
                        GrB_Matrix_extractElement_BOOL(&x, matrix, i, j);
                    std::cout << "Got from " << i << " to " << j << " val " << x << std::endl;
                    assert(ret_val == GrB_SUCCESS || ret_val == GrB_NO_VALUE);
                }
            }
        }
    }

    void solve() override
    {
        convertGraphToLAGraph();
        playground();
        yetToBeSolved = true;
        std::vector<GrB_Matrix> inputs(adjMatrices.size());
        std::transform(adjMatrices.begin(), adjMatrices.end(), inputs.begin(),
                       [](const auto& uniq_ptr) { return *uniq_ptr; });
        std::vector<GrB_Matrix> outputs(symbolsCount);
        std::transform(outputs.begin(), outputs.end(), outputs.begin(),
                       [this](GrB_Matrix mat) {
                           GrB_Matrix_new(&mat, GrB_BOOL, nodeNum, nodeNum);
                           return mat;
                       });
        convertResultsFromLAGraph(inputs);
        std::cout << "Finish !!!!!" << std::endl;
        auto rules = initRules();

        LAGraph_CFL_reachability_adv(outputs.data(), inputs.data(),
                                     symbolsCount, rules.data(), rules.size(),
                                     nullptr, 0);
        yetToBeSolved = false;
        worklist.clear();
        convertResultsFromLAGraph(std::move(outputs));
    }

private:
    bool yetToBeSolved = false;
    // TODO Style
    size_t symbolsCount = 0;
    size_t nodeNum = 0;
    std::unordered_map<int, int> SVFToLAGraphNodes;
    std::unordered_map<int, int> LAGraphToSVFNodes;
    std::unordered_map<int, GrammarBase::Symbol> LAGraphToSVFSymbol;
    std::unordered_map<GrammarBase::Symbol, int, CFGrammar::SymbolHash>
        SVFToLAGraphSymbol;
    std::unordered_set<int> origTerms;
    std::unordered_set<int> origNonTerms;
    std::unordered_map<GrammarBase::Symbol, GrammarBase::Productions,
                       CFGrammar::SymbolHash>
        origRules;
    std::unordered_map<int, int> SymbolKindToMaxAttrVal;
    std::vector<GrB_Matrix> adjMatricesHolder;
    std::vector<std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>>
        adjMatrices;
};

/// Solver Utilize CFLData
class POCRSolver : public CFLSolver
{
public:
    typedef std::map<const Label, NodeBS> TypeMap;                  // Label with SparseBitVector of NodeID
    typedef std::unordered_map<NodeID, TypeMap> DataMap;            // Each Node has a TypeMap
    typedef typename DataMap::iterator iterator;                    // iterator for each node
    typedef typename DataMap::const_iterator const_iterator;

protected:
    DataMap succMap;                                                // succ map for nodes contains Label: Edgeset
    DataMap predMap;                                                // pred map for nodes contains Label: edgeset
    const NodeBS emptyData;                                         // ??
    NodeBS diff;
    // union/add data
    //@{
    inline bool addPred(const NodeID key, const NodeID src, const Label ty)
    {
        return predMap[key][ty].test_and_set(src);
    };

    inline bool addSucc(const NodeID key, const NodeID dst, const Label ty)
    {
        return succMap[key][ty].test_and_set(dst);
    };

    inline bool addPreds(const NodeID key, const NodeBS& data, const Label ty)
    {
        if (data.empty())
            return false;
        return predMap[key][ty] |= data;                            // union of sparsebitvector (add to LHS)
    }

    inline bool addSuccs(const NodeID key, const NodeBS& data, const Label ty)
    {
        if (data.empty())
            return false;
        return succMap[key][ty] |= data;                            // // union of sparsebitvector (add to LHS)
    }
    //@}
public:

    virtual void clear()
    {
        succMap.clear();
        predMap.clear();
    }

    inline const_iterator begin() const
    {
        return succMap.begin();
    }

    inline const_iterator end() const
    {
        return succMap.end();
    }

    inline iterator begin()
    {
        return succMap.begin();
    }

    inline iterator end()
    {
        return succMap.end();
    }

    inline DataMap& getSuccMap()
    {
        return succMap;
    }

    inline DataMap& getPredMap()
    {
        return predMap;
    }

    inline TypeMap& getSuccMap(const NodeID key)
    {
        return succMap[key];
    }

    inline TypeMap& getPredMap(const NodeID key)
    {
        return predMap[key];
    }

    inline NodeBS& getSuccs(const NodeID key, const Label ty)
    {
        return succMap[key][ty];
    }

    inline NodeBS& getPreds(const NodeID key, const Label ty)
    {
        return predMap[key][ty];
    }

    // Alias data operations
    //@{
    inline bool addEdge(const NodeID src, const NodeID dst, const Label ty)
    {
        addSucc(src, dst, ty);
        return addPred(dst, src, ty);
    }

    /// add edges and return the set of added edges (dst) for src
    inline NodeBS addEdges(const NodeID src, const NodeBS& dstData, const Label ty)
    {
        NodeBS newDsts;
        if (addSuccs(src, dstData, ty))
        {
            for (const NodeID datum: dstData)
                if (addPred(datum, src, ty))
                    newDsts.set(datum);
        }
        return newDsts;
    }

    /// add edges and return the set of added edges (src) for dst
    inline NodeBS addEdges(const NodeBS& srcData, const NodeID dst, const Label ty)
    {
        NodeBS newSrcs;
        if (addPreds(dst, srcData, ty))
        {
            for (const NodeID datum: srcData)
                if (addSucc(datum, dst, ty))
                    newSrcs.set(datum);
        }
        return newSrcs;
    }

    /// find src -> find src[ty] -> find dst in set
    inline bool hasEdge(const NodeID src, const NodeID dst, const Label ty)
    {
        const_iterator iter1 = succMap.find(src);
        if (iter1 == succMap.end())
            return false;

        auto iter2 = iter1->second.find(ty);
        if (iter2 == iter1->second.end())
            return false;

        return iter2->second.test(dst);
    }

    /* This is a dataset version, to be modified to a cflData version */
    inline void clearEdges(const NodeID key)
    {
        succMap[key].clear();
        predMap[key].clear();
    }
    //@}

    POCRSolver(CFLGraph* _graph, CFGrammar* _grammar) : CFLSolver(_graph, _grammar)
    {
        buildCFLData();
    }
    /// Destructor
    virtual ~POCRSolver()
    {
    }

    /// Process CFLEdge
    virtual void processCFLEdge(const CFLEdge* Y_edge);

    /// Init CFLData
    virtual void buildCFLData();

    virtual void initialize();
};
/*!
 * Hybrid graph representation for transitive relations
 * The implementation is based on
 * Yuxiang Lei, Yulei Sui, Shuo Ding, and Qirun Zhang.
 * Taming Transitive Redundancy for Context-Free Language Reachability.
 * ACM SIGPLAN Conference on Object-Oriented Programming, Systems, Languages, and Applications
 */
/// Solver Utilize Hybrid Representation of Graph
class POCRHybridSolver : public POCRSolver
{
//Hybrid
//{@
public:
    struct TreeNode
    {
        NodeID id;
        std::unordered_set<TreeNode*> children;

        TreeNode(NodeID nId) : id(nId)
        {}

        ~TreeNode()
        {
        }

        inline bool operator==(const TreeNode& rhs) const
        {
            return id == rhs.id;
        }

        inline bool operator<(const TreeNode& rhs) const
        {
            return id < rhs.id;
        }
    };

public:
    Map<NodeID, std::unordered_map<NodeID, TreeNode*>> indMap;   // indMap[v][u] points to node v in tree(u)

    bool hasInd_h(NodeID src, NodeID dst);

    /// Add a node dst to tree(src)
    TreeNode* addInd_h(NodeID src, NodeID dst);

    /// Get the node dst in tree(src)
    TreeNode* getNode_h(NodeID src, NodeID dst)
    {
        return indMap[dst][src];
    }

    /// add v into desc(x) as a child of u
    void insertEdge_h(TreeNode* u, TreeNode* v)
    {
        u->children.insert(v);
    }

    void addArc_h(NodeID src, NodeID dst);

    void meld_h(NodeID x, TreeNode* uNode, TreeNode* vNode);
//@}
public:
    POCRHybridSolver(CFLGraph* _graph, CFGrammar* _grammar) : POCRSolver(_graph, _grammar)
    {
    }
    /// Destructor
    virtual ~POCRHybridSolver()
    {
        for (auto iter1: indMap)
        {
            for (auto iter2: iter1.second)
            {
                delete iter2.second;
                iter2.second = NULL;
            }
        }
    }

    /// Process CFLEdge
    virtual void processCFLEdge(const CFLEdge* Y_edge);

    virtual void initialize();

public:
    void addArc(NodeID src, NodeID dst);
    void meld(NodeID x, TreeNode* uNode, TreeNode* vNode);
};
}

#endif /* INCLUDE_CFL_CFLSolver_H_*/