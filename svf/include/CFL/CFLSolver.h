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
#include "Util/GeneralType.h"
#include "Util/WorkList.h"
#include "GraphBLAS.h"
#include "Graphs/CFLGraph.h"
#include "LAGraphX.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include "Util/WorkList.h"
#include <algorithm>
#include <chrono>
#include <cstdlib>

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
    static void checkLAGraphResult(GrB_Info result, const char* operation,
                                   const char* message)
    {
        if (result == GrB_SUCCESS)
            return;

        SVFUtil::errs() << "LAGraph operation '" << operation
                        << "' failed with status " << result;
        if (message != nullptr && message[0] != '\0')
            SVFUtil::errs() << ": " << message;
        SVFUtil::errs() << '\n';
        std::abort();
    }

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
        // Will redo the initialization in initialize() anyway.
        // Just set the flag, that we are not done
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

    void convertResultFromLAGraph(GrB_Matrix output, Symbol label);
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
        auto begin_init = std::chrono::high_resolution_clock::now();
        initialize();
        std::vector<GrB_Matrix> inputs(adjMatrices.size());
        std::transform(adjMatrices.begin(), adjMatrices.end(), inputs.begin(),
                       [](const auto& uniq_ptr) { return *uniq_ptr; });

        std::vector<GrB_Matrix> outputs(nonTermsCount, nullptr);
        std::vector<std::unique_ptr<GrB_Matrix, decltype(&GrB_Matrix_free)>>
            outputOwners;
        outputOwners.reserve(outputs.size());
        for (auto& output : outputs)
            outputOwners.emplace_back(&output, &GrB_Matrix_free);
        auto end_init = std::chrono::high_resolution_clock::now();
        if (Options::CFLAliasMeasureAlgorithmRuntime())
        {
            auto diff = std::chrono::duration_cast<std::chrono::milliseconds>(
                            end_init - begin_init)
                            .count();
            std::cout << "MTX: for init time passed: " << diff << " ms"
                      << std::endl;
        }

        auto begin_first = std::chrono::high_resolution_clock::now();
        char message[LAGRAPH_MSG_LEN] = {};
        GrB_Info result = LAGraph_CFL_reachability(
            outputs.data(), inputs.data(), termsCount, nonTermsCount,
            rules.data(), rules.size(), message);
        checkLAGraphResult(result, "LAGraph_CFL_reachability", message);

        auto end_first = std::chrono::high_resolution_clock::now();
        if (Options::CFLAliasMeasureAlgorithmRuntime())
        {
            auto diff = std::chrono::duration_cast<std::chrono::milliseconds>(
                            end_first - begin_first)
                            .count();
            std::cout << "Time passed: " << diff << " ms" << std::endl;
        }
        yetToBeSolved = false;
        worklist.clear();
        auto begin_finish = std::chrono::high_resolution_clock::now();
        if (SVF::Options::MTXCopyBackOnlyStarting())
        {
            auto startLabel = SVFToLAGraphNonTerm[graph->getStartKind()];
            convertResultFromLAGraph(outputs[startLabel],
                                     graph->getStartKind());
        }
        else
        {
            convertResultsFromLAGraph(outputs);
        }

        auto end_finish = std::chrono::high_resolution_clock::now();
        if (Options::CFLAliasMeasureAlgorithmRuntime())
        {
            auto diff = std::chrono::duration_cast<std::chrono::milliseconds>(
                            end_finish - begin_finish)
                            .count();
            std::cout << "MTX: for copy back time passed: " << diff << " ms"
                      << std::endl;
        }
    }
};

struct AdvMTXSolver : public CFLSolver
{
    enum Optimization : uint8_t
    {
        EmptyOptimization = 1U << 0,
        FormatOptimization = 1U << 1,
        LazyOptimization = 1U << 2,
        BlockOptimization = 1U << 3,
    };

    static constexpr uint8_t AllOptimizations =
        EmptyOptimization | FormatOptimization | LazyOptimization |
        BlockOptimization;

    AdvMTXSolver(CFLGraph* _graph, CFGrammar* _grammar)
        : CFLSolver(_graph, _grammar)
    {
        normalCheckIndices();
        LAGraph_Init(nullptr);
        setupGraphNodesMaps();
        setupRules();
        LAGraphRules = initRules();
    }

    [[noreturn]] void rejectIndexedGrammar(const std::string& reason,
                                           Symbol symbol) const
    {
        std::string symbolName = grammar->kindToStr(symbol.kind);
        if (symbol.variableAttribute != 0)
            symbolName += "_" + std::string(1, char(symbol.variableAttribute));
        else if (grammar->getAttrSyms().count(symbol.kind) != 0)
            symbolName += "_" + std::to_string(symbol.attribute);

        SVFUtil::errs() << "AdvMTXSolver requires uniformly indexed grammar "
                           "rules: "
                        << reason << " (symbol " << symbolName << ")\n";
        std::abort();
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
            SVFSymbolKindToMaxAttrVal[sym.kind] = std::max<int>(
                sym.attribute, SVFSymbolKindToMaxAttrVal[sym.kind]);
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
        if (SVFSymbolKindToMaxAttrVal.count(StartNonTerm) > 0)
        {
            maxVal = SVFSymbolKindToMaxAttrVal.at(StartNonTerm);
        }
        CFGrammar::Symbol newNonTermSymbol = StartNonTerm;
        for (int i = 0; i != maxVal + 1; ++i)
        {
            SVFToLAGraphSymbol[newNonTermSymbol] = symbolsCount;
            LAGraphToSVFSymbol[symbolsCount] = newNonTermSymbol;
            ++symbolsCount;
            ++newNonTermSymbol.attribute;
        }

        insertSymbols(origTerms, SVFSymbolKindToMaxAttrVal);
        insertSymbols(origNonTerms, SVFSymbolKindToMaxAttrVal);
    }

    // Validate before setupRules() discards concrete attributes. Each rule
    // shape must contain exactly the family that indexed expansion recreates.
    void normalCheckIndices()
    {
        GrammarBase::Productions productions;
        for (const auto& prod : grammar->getEpsilonProds())
            productions.insert(prod);
        for (const auto& [rhs, prods] : grammar->getSingleRHSToProds())
            productions.insert(prods.begin(), prods.end());
        for (const auto& [rhs, prods] : grammar->getFirstRHSToProds())
            productions.insert(prods.begin(), prods.end());

        std::unordered_map<int, unsigned> maximumIndValue;
        for (const auto& prod : productions)
            for (Symbol symbol : prod)
            {
                if (symbol.variableAttribute != 0)
                    rejectIndexedGrammar("unexpanded index variable", symbol);
                maximumIndValue[symbol.kind] =
                    std::max(maximumIndValue[symbol.kind], unsigned(symbol.attribute));
            }

        std::unordered_map<Production, std::unordered_set<unsigned>,
                           GrammarBase::SymbolVectorHash>
            families;
        for (const auto& prod : productions)
        {
            Production ruleFilteredFromInds;
            std::unordered_set<int> maxIndexValues;
            std::transform(prod.begin(), prod.end(), std::inserter(maxIndexValues, maxIndexValues.begin()),
                        [&maximumIndValue](Symbol s){return maximumIndValue.at(s.kind);});
            if (maxIndexValues.size() > 2 || ( maxIndexValues.size() > 1 && maxIndexValues.count(0) == 0))
                rejectIndexedGrammar(
                    "indexed symbols in a rule must have matching "
                    "indices and ranges", prod[0]);

            std::unordered_set<int> indexValues;
            for (Symbol symbol : prod)
            {
                // Symbols with only index zero stay fixed during compression.
                if (maximumIndValue.at(symbol.kind) > 0)
                    indexValues.insert(symbol.attribute);
            }

            if (indexValues.size() > 1)
            {
                rejectIndexedGrammar(
                    "indexed symbols in a rule must have matching "
                    "indices and ranges",
                    prod[0]);
            }
            std::transform(prod.begin(), prod.end(), std::back_inserter(ruleFilteredFromInds),
                        [](Symbol s){return s.kind;});
            if (indexValues.empty())
                families[ruleFilteredFromInds].insert(0);
            else
                families[ruleFilteredFromInds].insert(*indexValues.begin());
        }

        for (const auto& [shape, indices] : families)
        {
            unsigned maximum = 0;
            for (Symbol symbol : shape)
                maximum = std::max(maximum, maximumIndValue.at(symbol.kind));
            // All observed indices lie in [0, maximum], so this cardinality
            // proves both density and completeness, including index zero.
            if (indices.size() != size_t(maximum) + 1)
                rejectIndexedGrammar(
                    "incomplete indexed rule family (expected every index "
                    "from zero through the family maximum)",
                    shape.front());
        }
    }

    void checkIndices()
    {
        std::unordered_set<int> WithZero;
        std::unordered_set<int> WithNonZero;
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

        for (auto& [sym, maxAttrVal] : SVFSymbolKindToMaxAttrVal)
        {
            auto& singleRhsRulesWithZero = grammar->getProdsFromSingleRHS(sym);
            for (int i = 1; i < maxAttrVal + 1; ++i)
            {
                Symbol newSymbol = sym;
                newSymbol.attribute = i;

                GrammarBase::Productions prodsWithI;
                auto singleRhsRulesWithI =
                    grammar->getProdsFromSingleRHS(newSymbol);
                auto zeroOutProd = [](const Production& prod) {
                    Production zeroedProd;
                    std::transform(
                        prod.begin(), prod.end(),
                        std::back_inserter(zeroedProd),
                        [](Symbol symbol) { return Symbol(symbol.kind); });
                    return zeroedProd;
                };
                std::transform(
                    singleRhsRulesWithI.begin(), singleRhsRulesWithI.end(),
                    std::inserter(prodsWithI, prodsWithI.begin()), zeroOutProd);
                assert(singleRhsRulesWithI == singleRhsRulesWithZero &&
                       "Non same rules for different indices!");
            }

            auto firstRhsRulesWithZero = grammar->getProdsFromFirstRHS(sym);
            auto secondRhsRulesWithZero = grammar->getProdsFromSecondRHS(sym);
        }
    }

    inline bool pushIntoWorklist(const CFLEdge* item) override
    {
        // Will redo the initialization in initialize() anyway.
        // Just set the flag, that we are not done
        yetToBeSolved = true;

        return true;
    }
    inline bool isWorklistEmpty() override
    {
        return !yetToBeSolved;
    }

    void setupGraphNodesMaps()
    {
        int i = 0;
        for (auto&& [node_id, node_ptr] : *graph)
        {
            SVFToLAGraphNodes[node_id] = i;
            LAGraphToSVFNodes[i] = node_id;
            ++i;
        }
    }

    void convertGraphToLAGraph()
    {
        setupGraphNodesMaps();

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

        auto& kindToAttrMap = grammar->getKindToAttrsMap();
        for (auto& edgeIt : graph->getCFLEdges())
        {
            auto SVFSymbol = GrammarBase::Symbol(edgeIt->getEdgeKind());

            // TODO Investigate this?
            if (origTerms.count(SVFSymbol.kind) && SVFSymbol.attribute > 0)
            {
                if (kindToAttrMap.count(SVFSymbol.kind) == 0)
                    continue;
                if (kindToAttrMap.at(SVFSymbol.kind)
                        .count(SVFSymbol.attribute) == 0)
                    continue;
            }

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
        if (SVFSymbolKindToMaxAttrVal.count(kind))
            return SVFSymbolKindToMaxAttrVal.at(kind);
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

    void handleSingleNonTermToSingleNonTerm()
    {
        auto newRules = origRules;
        bool changed = true;
        while (changed)
        {
            changed = false;
            for (auto&& [nonTerm, prods] : origRules)
            {
                for (auto&& prod : prods)
                {
                    if (prod.size() == 2 || origTerms.count(prod.front()) > 0)
                        continue;
                    auto& singleNonTerm = prod.front();
                    std::copy(origRules[singleNonTerm].begin(),
                              origRules[singleNonTerm].end(),
                              std::inserter(newRules[nonTerm],
                                            newRules[nonTerm].begin()));
                    newRules[nonTerm].erase(prod);
                    changed = true;
                }
            }
            origRules = newRules;
        }
    }

    int handleTermInDoubleProd(std::vector<LAGraph_rule_EWCNF>& rules, int kind,
                               int LAGraphId)
    {
        if (origNonTerms.count(kind))
            return LAGraphId;
        if (SVFTermToLAGraphNonTerm.count(kind))
            return SVFTermToLAGraphNonTerm.at(kind);

        int NewLAGraphNonTermId = symbolsCount;

        auto indexCount = maxAttrValOrZero(kind) + 1;
        for (int i = 0; i < indexCount; ++i)
        {
            Symbol SVFSymbol(kind);
            SVFSymbol.attribute = i;

            int LAGraphNonTermId = symbolsCount++;
            LAGraphAddedNonTerms.insert(LAGraphNonTermId);
            LAGraphToSVFSymbol[LAGraphNonTermId] = SVFSymbol;
        }

        uint8_t indexedSymbols =
            indexCount > 1
                ? (LAGraph_EWNCF_INDEX_NONTERM | LAGraph_EWNCF_INDEX_PROD_A)
                : 0;

        rules.push_back({.nonterm = NewLAGraphNonTermId,
                         .prod_A = LAGraphId,
                         .prod_B = -1,
                         .indexed_count = static_cast<uint32_t>(indexCount),
                         .indexed = indexedSymbols});
        return NewLAGraphNonTermId;
    }

    std::vector<LAGraph_rule_EWCNF> initRules()
    {
        std::vector<LAGraph_rule_EWCNF> rules;
        handleSingleNonTermToSingleNonTerm();

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
                {
                    prodB = getProdInfo(prod[1], false, indexedSymbols,
                                        indexedCount);
                    prodA = handleTermInDoubleProd(rules, prod[0], prodA);
                    prodB = handleTermInDoubleProd(rules, prod[1], prodB);
                }

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

    void convertResultFromLAGraph(GrB_Matrix matrix, Symbol label)
    {
        GrB_Index nonZeroElems = 0;
        assert(GrB_Matrix_nvals(&nonZeroElems, matrix) == 0 &&
               "On matrix nonzero element amount extraction");
        std::vector<GrB_Index> rowIndices(nonZeroElems);
        std::vector<GrB_Index> colIndices(nonZeroElems);
        auto vals = std::make_unique<bool[]>(nonZeroElems);
        GrB_Matrix_extractTuples_BOOL(rowIndices.data(), colIndices.data(),
                                      vals.get(), &nonZeroElems, matrix);
        for (size_t i = 0; i < nonZeroElems; ++i)
        {
            if (!vals[i])
                continue;
            auto* SrcNode =
                graph->getGNode(LAGraphToSVFNodes.at(rowIndices[i]));
            auto* DstNode =
                graph->getGNode(LAGraphToSVFNodes.at(colIndices[i]));
            graph->addCFLEdge(SrcNode, DstNode, label);
        }
    }

    void convertResultsFromLAGraph(const std::vector<GrB_Matrix>& outputs)
    {
        for (int LAGraphSymbolId = 0, endI = outputs.size();
             LAGraphSymbolId != endI; ++LAGraphSymbolId)
        {
            auto SVFSymbol = LAGraphToSVFSymbol.at(LAGraphSymbolId);
            if (origTerms.count(SVFSymbol.kind))
                continue;
            auto matrix = outputs[LAGraphSymbolId];
            convertResultFromLAGraph(matrix, SVFSymbol);
        }
    }

    void solve() override
    {
        convertGraphToLAGraph();
        std::vector<GrB_Matrix> inputs(adjMatrices.size());
        std::transform(adjMatrices.begin(), adjMatrices.end(), inputs.begin(),
                       [](const auto& uniq_ptr) { return *uniq_ptr; });
        std::vector<GrB_Matrix> outputs(symbolsCount, nullptr);
        std::vector<std::unique_ptr<GrB_Matrix, decltype(&GrB_Matrix_free)>>
            outputOwners;
        outputOwners.reserve(outputs.size());
        for (auto& output : outputs)
            outputOwners.emplace_back(&output, &GrB_Matrix_free);

        auto begin_first = std::chrono::high_resolution_clock::now();
        const u32_t configuredOptimizations =
            Options::AdvancedMTXOptimizations();
        if ((configuredOptimizations & ~u32_t(AllOptimizations)) != 0)
        {
            SVFUtil::errs()
                << "Invalid -adv-mtx-optimizations mask: "
                << configuredOptimizations
                << "; supported bits are 1, 2, 4, and 8\n";
            std::abort();
        }

        char message[LAGRAPH_MSG_LEN] = {};
        GrB_Info result = LAGraph_CFL_reachability_adv(
            outputs.data(), inputs.data(), symbolsCount, LAGraphRules.data(),
            LAGraphRules.size(), message,
            static_cast<int8_t>(configuredOptimizations));
        checkLAGraphResult(result, "LAGraph_CFL_reachability_adv", message);
        auto end_first = std::chrono::high_resolution_clock::now();
        if (Options::CFLAliasMeasureAlgorithmRuntime())
        {
            auto diff = std::chrono::duration_cast<std::chrono::milliseconds>(
                            end_first - begin_first)
                            .count();
            std::cout << "Time passed: " << diff << " ms" << std::endl;
        }
        yetToBeSolved = false;
        worklist.clear();
        if (SVF::Options::MTXCopyBackOnlyStarting())
        {
            auto startLabel = SVFToLAGraphSymbol[graph->getStartKind()];
            convertResultFromLAGraph(outputs[startLabel],
                                     graph->getStartKind());
        }
        else
        {
            convertResultsFromLAGraph(outputs);
        }
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
    std::unordered_map<GrammarBase::Symbol, int, CFGrammar::SymbolHash>
        SVFTermToLAGraphNonTerm;
    std::unordered_set<GrammarBase::Symbol, CFGrammar::SymbolHash>
        LAGraphAddedNonTerms;

    std::unordered_set<int> origTerms;
    std::unordered_set<int> origNonTerms;
    std::unordered_map<GrammarBase::Symbol, GrammarBase::Productions,
                       CFGrammar::SymbolHash>
        origRules;
    std::unordered_map<int, int> SVFSymbolKindToMaxAttrVal;
    std::vector<GrB_Matrix> adjMatricesHolder;
    std::vector<std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>>
        adjMatrices;
    std::vector<LAGraph_rule_EWCNF> LAGraphRules;
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
