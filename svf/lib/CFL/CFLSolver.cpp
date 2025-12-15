//===----- CFLSolver.cpp -- Context-free language reachability solver--------------//
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
 * CFLSolver.cpp
 *
 *  Created on: March 5, 2022
 *      Author: Yulei Sui
 */

#include "CFL/CFLSolver.h"
#include "CFL/CFGrammar.h"
#include <algorithm>

using namespace SVF;

double CFLSolver::numOfChecks = 0;

void CFLSolver::initialize()
{
    for(auto it = graph->begin(); it!= graph->end(); it++)
    {
        for(const CFLEdge* edge : (*it).second->getOutEdges())
        {
            pushIntoWorklist(edge);
        }
    }

    /// Foreach production X -> epsilon
    ///     add X(i,i) if not exist to E and to worklist
    for(const Production& prod : grammar->getEpsilonProds())
    {
        for(auto it = graph->begin(); it!= graph->end(); it++)
        {
            Symbol X = grammar->getLHSSymbol(prod);
            CFLNode* i = (*it).second;
            if(const CFLEdge* edge = graph->addCFLEdge(i, i, X))
            {
                pushIntoWorklist(edge);
            }
        }
    }
}

void CFLSolver::processCFLEdge(const CFLEdge* Y_edge)
{
    CFLNode* i = Y_edge->getSrcNode();
    CFLNode* j = Y_edge->getDstNode();

    /// For each production X -> Y
    ///     add X(i,j) if not exist to E and to worklist
    Symbol Y = Y_edge->getEdgeKind();
    if (grammar->hasProdsFromSingleRHS(Y))
        for(const Production& prod : grammar->getProdsFromSingleRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            numOfChecks++;
            if(const CFLEdge* newEdge = graph->addCFLEdge(i, j, X))
            {
                pushIntoWorklist(newEdge);
            }
        }

    /// For each production X -> Y Z
    /// Foreach outgoing edge Z(j,k) from node j do
    ///     add X(i,k) if not exist to E and to worklist
    if (grammar->hasProdsFromFirstRHS(Y))
        for(const Production& prod : grammar->getProdsFromFirstRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            for(const CFLEdge* Z_edge : j->getOutEdgeWithTy(grammar->getSecondRHSSymbol(prod)))
            {
                CFLNode* k = Z_edge->getDstNode();
                numOfChecks++;
                if(const CFLEdge* newEdge = graph->addCFLEdge(i, k, X))
                {
                    pushIntoWorklist(newEdge);
                }
            }
        }

    /// For each production X -> Z Y
    /// Foreach incoming edge Z(k,i) to node i do
    ///     add X(k,j) if not exist to E and to worklist
    if(grammar->hasProdsFromSecondRHS(Y))
        for(const Production& prod : grammar->getProdsFromSecondRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            for(const CFLEdge* Z_edge : i->getInEdgeWithTy(grammar->getFirstRHSSymbol(prod)))
            {
                CFLNode* k = Z_edge->getSrcNode();
                numOfChecks++;
                if(const CFLEdge* newEdge = graph->addCFLEdge(k, j, X))
                {
                    pushIntoWorklist(newEdge);
                }
            }
        }
}


void CFLSolver::solve()
{
    /// initial worklist
    initialize();

    while(!isWorklistEmpty())
    {
        /// Select and remove an edge Y(i,j) from worklist
        const CFLEdge* Y_edge = popFromWorklist();
        processCFLEdge(Y_edge);
    }
}

int MTXSolver::convertToLAGraph(int SVFTermOrNonTerm)
{
    if (SVFToLAGraphTerm.count(SVFTermOrNonTerm) > 0)
        return SVFToLAGraphTerm.at(SVFTermOrNonTerm);

    return SVFToLAGraphNonTerm.at(SVFTermOrNonTerm);
}

bool checkProductionsSame(
    const GrammarBase::SymbolMap<GrammarBase::Symbol, GrammarBase::Productions>&
        firstRHS,
    const GrammarBase::SymbolMap<GrammarBase::Symbol, GrammarBase::Productions>&
        secondRHS)
{
    GrammarBase::Productions fromFirstRhs;
    GrammarBase::Productions fromSecondRhs;
    for (auto& [firstRhs, prods_vec] : firstRHS)
    {
        for (auto& prod : prods_vec)
        {
            fromFirstRhs.insert(prod);
        }
    }
    for (auto& [secondRhs, prods_vec] : secondRHS)
    {
        for (auto& prod : prods_vec)
        {
            fromSecondRhs.insert(prod);
        }
    }

    return fromFirstRhs == fromSecondRhs;
}

void MTXSolver::setupTermMaps()
{
    termsCount = 0;
    for (auto& [nonterm, prod] : grammar->getSingleRHSToProds())
    {
        for (auto& single_prod : prod)
        {
            assert(single_prod.size() == 2);
            auto& termOrNonTerm = single_prod.back();
            if (SVFToLAGraphNonTerm.count(termOrNonTerm) > 0)
                continue;
            SVFToLAGraphTerm[termOrNonTerm] = termsCount;
            LAGraphToSVFTerm[termsCount] = termOrNonTerm;
            ++termsCount;
        }
    }

    for (auto& [nonterm, prod] : grammar->getFirstRHSToProds())
    {
        for (auto& single_prod : prod)
        {
            assert(single_prod.size() == 3);
            for (auto& termOrNonTerm : single_prod)
            {
                if (SVFToLAGraphNonTerm.count(termOrNonTerm) > 0)
                    continue;

                int newTerm = termsCount;
                bool alreadyInserted =
                    SVFToLAGraphTerm.count(termOrNonTerm) > 0;
                if (alreadyInserted)
                {
                    newTerm = SVFToLAGraphTerm.at(termOrNonTerm);
                }
                else
                {
                    SVFToLAGraphTerm[termOrNonTerm] = newTerm;
                    LAGraphToSVFTerm[newTerm] = termOrNonTerm;
                }

                // handle case of rule type A -> Bc by introducing new non term
                // and doing A -> BD D -> c
                if (SVFTermToLAGraphNonTerm.count(termOrNonTerm) == 0)
                {
                    SVFTermToLAGraphNonTerm[termOrNonTerm] = nonTermsCount;
                    LAGraphNonTermToSVFTerm[nonTermsCount] = termOrNonTerm;

                    // TODO Should be a separate function call
                    rules.push_back({.nonterm = nonTermsCount,
                                     .prod_A = newTerm,
                                     .prod_B = -1,
                                     .index = 0});
                    ++nonTermsCount;
                }
                if (!alreadyInserted)
                    ++termsCount;
            }
        }
    }

    auto& epsilonProds = grammar->getEpsilonProds();
    if (!epsilonProds.empty())
    {
        auto& epsilonTerm = epsilonProds.begin()->back();
        SVFToLAGraphTerm[epsilonTerm] = -1;
        LAGraphToSVFTerm[-1] = epsilonTerm;
    }
}

void MTXSolver::setupNonTermMaps()
{
    assert(checkProductionsSame(grammar->getFirstRHSToProds(),
                                grammar->getSecondRHSToProds()));
    // Nonterm map creation
    std::unordered_set<int> origTerms;
    for (auto& [termName, termId] : grammar->getTerminals())
        origTerms.insert(termId);

    nonTermsCount = 0;
    for (auto& [singleRhs, prods_vec] : grammar->getSingleRHSToProds())
    {
        for (auto& prod : prods_vec)
        {
            auto& nonterm = grammar->getLHSSymbol(prod);
            assert(origTerms.count(nonterm.kind) == 0);
            origRules[nonterm].insert({prod.at(1)});

            SVFToLAGraphNonTerm[nonterm] = nonTermsCount;
            LAGraphToSVFNonTerm[nonTermsCount] = nonterm;
            ++nonTermsCount;
        }
    }
    for (auto& [firstRhs, prods_vec] : grammar->getFirstRHSToProds())
    {
        for (auto& prod : prods_vec)
        {
            auto& nonterm = grammar->getLHSSymbol(prod);
            assert(origTerms.count(nonterm.kind) == 0);
            origRules[nonterm].insert({prod.at(1), prod.at(2)});

            SVFToLAGraphNonTerm[nonterm] = nonTermsCount;
            LAGraphToSVFNonTerm[nonTermsCount] = nonterm;
            ++nonTermsCount;
        }
    }
}

void MTXSolver::setupGraphNodesMaps()
{
    int i = 0;
    for (auto&& [node_id, node_ptr] : *graph)
    {
        SVFToLAGraphNodes[node_id] = i;
        LAGraphToSVFNodes[i] = node_id;
        ++i;
    }
}

void MTXSolver::handleSingleNonTermRules()
{
    bool changed = true;
    auto newOrigRules = origRules;
    while (changed)
    {
        changed = false;
        for (auto& [nonTerm, prods_vec] : origRules)
        {
            for (auto& prod : prods_vec)
            {
                if (prod.size() != 1 ||
                    SVFToLAGraphNonTerm.count(prod.front()) == 0)
                    continue;
                auto& singleNonTerm = prod.front();
                std::copy(origRules[singleNonTerm].begin(),
                          origRules[singleNonTerm].end(),
                          std::inserter(newOrigRules[nonTerm],
                                        newOrigRules[nonTerm].begin()));
                newOrigRules[nonTerm].erase(prod);
                changed = true;
            }
        }
        origRules = newOrigRules;
    }
}

void MTXSolver::convertGrammarToLAGraphRules()
{
    handleSingleNonTermRules();

    for (auto& epsilonProd : grammar->getEpsilonProds())
    {
        assert(epsilonProd.size() == 2);
        assert(SVFToLAGraphTerm.at(epsilonProd.back()) == -1);
        rules.push_back({.nonterm = SVFToLAGraphNonTerm.at(epsilonProd.front()),
                         .prod_A = -1,
                         .prod_B = -1,
                         .index = 0});
    }

    auto convertSVFNonTermToLAGraph = [this](GrammarBase::Symbol kind) {
        if (SVFTermToLAGraphNonTerm.count(kind) > 0)
        {
            return SVFTermToLAGraphNonTerm[kind];
        }
        return SVFToLAGraphNonTerm.at(kind);
    };

    for (auto& [nonTerm, prods_vec] : origRules)
    {
        for (auto& prod : prods_vec)
        {
            LAGraph_rule_WCNF newRule{.nonterm =
                                          SVFToLAGraphNonTerm.at(nonTerm),
                                      .prod_A = -1,
                                      .prod_B = -1,
                                      .index = 0};

            if (prod.size() == 1)
            {
                newRule.prod_A = SVFToLAGraphTerm.at(prod.at(0));
            }
            else if (prod.size() == 2)
            {
                newRule.prod_A = convertSVFNonTermToLAGraph(prod.at(0));
                newRule.prod_B = convertSVFNonTermToLAGraph(prod.at(1));
            }
            else
            {
                assert(false && "Wrong size of prods vec!!!!\n");
            }
            rules.push_back(std::move(newRule));
        }
    }
}

void MTXSolver::convertGraphToLAGraph()
{
    LAGraph_Init(nullptr);

    // terminal to edge map
    std::unordered_map<int, std::vector<std::pair<int, int>>> adjMat;
    nodeNum = graph->getTotalNodeNum();
    assert(SVFToLAGraphNodes.size() == nodeNum);
    for (auto& edgeIt : graph->getCFLEdges())
    {
        auto LAGraphTerm = GrammarBase::Symbol(edgeIt->getEdgeKind());
        if (SVFToLAGraphTerm.count(LAGraphTerm) == 0)
            continue;
        auto edgeKind = SVFToLAGraphTerm.at(LAGraphTerm);
        auto srcId = SVFToLAGraphNodes.at(edgeIt->getSrcID());
        auto dstId = SVFToLAGraphNodes.at(edgeIt->getDstID());
        if (edgeKind != -1)
            adjMat[edgeKind].push_back({srcId, dstId});
    }

    adjMatricesHolder.resize(termsCount);
    for (int i = 0; i != termsCount; ++i)
    {
        adjMatrices.push_back(
            std::unique_ptr<GrB_Matrix, GrB_Info (*)(GrB_Matrix* mat)>{
                &adjMatricesHolder[i], GrB_Matrix_free});
        GrB_Matrix* curTermMatrix = adjMatrices[i].get();
        assert(GrB_Matrix_new(curTermMatrix, GrB_BOOL, nodeNum, nodeNum) ==
               GrB_SUCCESS);

        auto& matForCurTerm = adjMat[i];
        for (auto& [srcId, dstId] : matForCurTerm)
        {
            // std::cout << "Setting {" << LAGraphToSVFNodes.at(srcId) << ", "
            //           << LAGraphToSVFNodes.at(dstId) << "} in " << i
            //           << std::endl;
            assert(size_t(srcId) < nodeNum);
            assert(size_t(dstId) < nodeNum);
            assert(GrB_Matrix_setElement_BOOL(*curTermMatrix, true, srcId,
                                              dstId) == GrB_SUCCESS);
        }
    }
}

void MTXSolver::convertResultsFromLAGraph(
    const std::vector<GrB_Matrix>& outputs)
{
    for (int LAGraphNonTermId = 0, endI = outputs.size();
         LAGraphNonTermId != endI; ++LAGraphNonTermId)
    {
        if (LAGraphToSVFNonTerm.count(LAGraphNonTermId) == 0)
            continue;
        auto matrix = outputs[LAGraphNonTermId];
        for (size_t i = 0; i != nodeNum; ++i)
        {
            for (size_t j = 0; j != nodeNum; ++j)
            {
                bool x = false;
                auto ret_val = GrB_Matrix_extractElement_BOOL(&x, matrix, i, j);
                assert(ret_val == GrB_SUCCESS || ret_val == GrB_NO_VALUE);
                if (x)
                {
                    auto* SrcNode = graph->getGNode(LAGraphToSVFNodes.at(i));
                    auto* DstNode = graph->getGNode(LAGraphToSVFNodes.at(j));
                    auto Label = LAGraphToSVFNonTerm[LAGraphNonTermId];
                    graph->addCFLEdge(SrcNode, DstNode, Label);
                }
            }
        }
    }
}

void POCRSolver::buildCFLData()
{
    for (CFLEdge* edge: graph->getCFLEdges())
        addEdge(edge->getSrcID(), edge->getDstID(), edge->getEdgeKind());
}

void POCRSolver::processCFLEdge(const CFLEdge* Y_edge)
{
    CFLNode* i = Y_edge->getSrcNode();
    CFLNode* j = Y_edge->getDstNode();

    /// For each production X -> Y
    ///     add X(i,j) if not exist to E and to worklist
    Symbol Y = Y_edge->getEdgeKind();
    if (grammar->hasProdsFromSingleRHS(Y))
        for(const Production& prod : grammar->getProdsFromSingleRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            numOfChecks++;
            if (addEdge(i->getId(), j->getId(), X))
            {
                const CFLEdge* newEdge = graph->addCFLEdge(Y_edge->getSrcNode(), Y_edge->getDstNode(), X);
                pushIntoWorklist(newEdge);
            }

        }

    /// For each production X -> Y Z
    /// Foreach outgoing edge Z(j,k) from node j do
    ///     add X(i,k) if not exist to E and to worklist
    if (grammar->hasProdsFromFirstRHS(Y))
        for(const Production& prod : grammar->getProdsFromFirstRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            NodeBS diffDsts = addEdges(i->getId(), getSuccMap(j->getId())[grammar->getSecondRHSSymbol(prod)], X);
            numOfChecks += getSuccMap(j->getId())[grammar->getSecondRHSSymbol(prod)].count();
            for (NodeID diffDst: diffDsts)
            {
                const CFLEdge* newEdge = graph->addCFLEdge(i, graph->getGNode(diffDst), X);
                pushIntoWorklist(newEdge);
            }
        }

    /// For each production X -> Z Y
    /// Foreach incoming edge Z(k,i) to node i do
    ///     add X(k,j) if not exist to E and to worklist
    if(grammar->hasProdsFromSecondRHS(Y))
        for(const Production& prod : grammar->getProdsFromSecondRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            NodeBS diffSrcs = addEdges(getPredMap(i->getId())[grammar->getFirstRHSSymbol(prod)], j->getId(), X);
            numOfChecks += getPredMap(i->getId())[grammar->getFirstRHSSymbol(prod)].count();
            for (NodeID diffSrc: diffSrcs)
            {
                const CFLEdge* newEdge = graph->addCFLEdge(graph->getGNode(diffSrc), j, X);
                pushIntoWorklist(newEdge);
            }
        }
}

void POCRSolver::initialize()
{
    for(auto edge : graph->getCFLEdges())
    {
        pushIntoWorklist(edge);
    }

    /// Foreach production X -> epsilon
    ///     add X(i,i) if not exist to E and to worklist
    for(const Production& prod : grammar->getEpsilonProds())
    {
        for(auto IDMap : getSuccMap())
        {
            Symbol X = grammar->getLHSSymbol(prod);
            if (addEdge(IDMap.first, IDMap.first, X))
            {
                CFLNode* i = graph->getGNode(IDMap.first);
                const CFLEdge* newEdge = graph->addCFLEdge(i, i, X);
                pushIntoWorklist(newEdge);
            }
        }
    }
}

void POCRHybridSolver::processCFLEdge(const CFLEdge* Y_edge)
{
    CFLNode* i = Y_edge->getSrcNode();
    CFLNode* j = Y_edge->getDstNode();

    /// For each production X -> Y
    ///     add X(i,j) if not exist to E and to worklist
    Symbol Y = Y_edge->getEdgeKind();
    if (grammar->hasProdsFromSingleRHS(Y))
        for(const Production& prod : grammar->getProdsFromSingleRHS(Y))
        {
            Symbol X = grammar->getLHSSymbol(prod);
            numOfChecks++;
            if (addEdge(i->getId(), j->getId(), X))
            {
                const CFLEdge* newEdge = graph->addCFLEdge(Y_edge->getSrcNode(), Y_edge->getDstNode(), X);
                pushIntoWorklist(newEdge);
            }

        }

    /// For each production X -> Y Z
    /// Foreach outgoing edge Z(j,k) from node j do
    ///     add X(i,k) if not exist to E and to worklist
    if (grammar->hasProdsFromFirstRHS(Y))
        for(const Production& prod : grammar->getProdsFromFirstRHS(Y))
        {
            if ((grammar->getLHSSymbol(prod) == grammar->strToSymbol("F")) && (Y == grammar->strToSymbol("F")) && (grammar->getSecondRHSSymbol(prod) == grammar->strToSymbol("F")))
            {
                addArc(i->getId(), j->getId());
            }
            else
            {
                Symbol X = grammar->getLHSSymbol(prod);
                NodeBS diffDsts = addEdges(i->getId(), getSuccMap(j->getId())[grammar->getSecondRHSSymbol(prod)], X);
                numOfChecks += getSuccMap(j->getId())[grammar->getSecondRHSSymbol(prod)].count();
                for (NodeID diffDst: diffDsts)
                {
                    const CFLEdge* newEdge = graph->addCFLEdge(i, graph->getGNode(diffDst), X);
                    pushIntoWorklist(newEdge);
                }
            }
        }

    /// For each production X -> Z Y
    /// Foreach incoming edge Z(k,i) to node i do
    ///     add X(k,j) if not exist to E and to worklist
    if(grammar->hasProdsFromSecondRHS(Y))
        for(const Production& prod : grammar->getProdsFromSecondRHS(Y))
        {
            if ((grammar->getLHSSymbol(prod) == grammar->strToSymbol("F")) && (Y == grammar->strToSymbol("F")) && (grammar->getFirstRHSSymbol(prod) == grammar->strToSymbol("F")))
            {
                addArc(i->getId(), j->getId());
            }
            else
            {
                Symbol X = grammar->getLHSSymbol(prod);
                NodeBS diffSrcs = addEdges(getPredMap(i->getId())[grammar->getFirstRHSSymbol(prod)], j->getId(), X);
                numOfChecks += getPredMap(i->getId())[grammar->getFirstRHSSymbol(prod)].count();
                for (NodeID diffSrc: diffSrcs)
                {
                    const CFLEdge* newEdge = graph->addCFLEdge(graph->getGNode(diffSrc), j, X);
                    pushIntoWorklist(newEdge);
                }
            }
        }
}

void POCRHybridSolver::initialize()
{
    for(auto edge : graph->getCFLEdges())
    {
        pushIntoWorklist(edge);
    }

    // init hybrid dataset
    for (auto it = graph->begin(); it != graph->end(); ++it)
    {
        NodeID nId = it->first;
        addInd_h(nId, nId);
    }

    ///     add X(i,i) if not exist to E and to worklist
    for(const Production& prod : grammar->getEpsilonProds())
    {
        for(auto IDMap : getSuccMap())
        {
            Symbol X = grammar->getLHSSymbol(prod);
            if (addEdge(IDMap.first, IDMap.first, X))
            {
                CFLNode* i = graph->getGNode(IDMap.first);
                const CFLEdge* newEdge = graph->addCFLEdge(i, i, X);
                pushIntoWorklist(newEdge);
            }
        }
    }
}

void POCRHybridSolver::addArc(NodeID src, NodeID dst)
{
    if(hasEdge(src, dst, grammar->strToSymbol("F")))
        return;

    for (auto& iter: indMap[src])
    {
        meld(iter.first, getNode_h(iter.first, src), getNode_h(dst, dst));
    }
}


void POCRHybridSolver::meld(NodeID x, TreeNode* uNode, TreeNode* vNode)
{
    numOfChecks++;

    TreeNode* newVNode = addInd_h(x, vNode->id);
    if (!newVNode)
        return;

    insertEdge_h(uNode, newVNode);
    for (TreeNode* vChild: vNode->children)
    {
        meld_h(x, newVNode, vChild);
    }
}

bool POCRHybridSolver::hasInd_h(NodeID src, NodeID dst)
{
    auto it = indMap.find(dst);
    if (it == indMap.end())
        return false;
    return (it->second.find(src) != it->second.end());
}

POCRHybridSolver::TreeNode* POCRHybridSolver::addInd_h(NodeID src, NodeID dst)
{
    TreeNode* newNode = new TreeNode(dst);
    auto resIns = indMap[dst].insert(std::make_pair(src, newNode));
    if (resIns.second)
        return resIns.first->second;
    delete newNode;
    return nullptr;
}

void POCRHybridSolver::addArc_h(NodeID src, NodeID dst)
{
    if (!hasInd_h(src, dst))
    {
        for (auto iter: indMap[src])
        {
            meld_h(iter.first, getNode_h(iter.first, src), getNode_h(dst, dst));
        }
    }
}

void POCRHybridSolver::meld_h(NodeID x, TreeNode* uNode, TreeNode* vNode)
{
    TreeNode* newVNode = addInd_h(x, vNode->id);
    if (!newVNode)
        return;

    insertEdge_h(uNode, newVNode);
    for (TreeNode* vChild: vNode->children)
    {
        meld_h(x, newVNode, vChild);
    }
}