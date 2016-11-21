-------------------------------------------------------------------------------
--	Natural Deduction Logic Module
--
--	This module defines the logic of proving utilizing Natural Deduction.
--
--	@authors: bpalkmim
--
-------------------------------------------------------------------------------

require "Logic/NatDGraph"
require "Logic/Goal"
require "Logic/ConstantsForNatD"
require "Logic/NaturalDeductionPrint"
require 'ParseInput'
require "logging"
require "logging.file"
require "Logic/Set"
require "Util/utility"

local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

LogicModule = {}

local goalsList = nil
local graph = nil
local counterModel = nil
local foundNodes = {}
local nstep = 0
local sufix = 0
-- Variável para indexação de descartes de hipótese
-- Também utilizado para indexação das →-Intro
local currentStepNumber = 0
-- Contagem das →-Elim
local elimIndex = 0

-- Lista das hipóteses a serem descartadas.
-- Uma hipótese é um predicado lógico. Na prática, essa lista contém os
-- nós do grafo da prova.
LogicModule.dischargeable = {}

-- Private functions

local function generateNewGoal(natDNode)

	if goalsList == nil then
		goalsList = {}
	end

	local edgesOut = natDNode:getEdgesOut()
	local newGoal = nil
	local j = 1

	if edgesOut ~= nil then
		for k, _ in ipairs(edgesOut) do
			for i = 1, #edgesOut[k] do
				local currentNode = edgesOut[k][i]:getDestino()
				local typeOfNode = currentNode:getInformation("type")

				-- TODO ver para mais tipos de nós
				if typeOfNode == opImp.graph then
					goalsList[j] = currentNode
					j = j + 1
				end
			end
		end
	end
	
	newGoal = Goal:new(natDNode, goalsList)
					 
	return newGoal
end

local function createGraphEmpty()

	local NatDGraph = Graph:new()
	NatDNode:resetCounters()
	
	local NodeGG = NatDNode:new(lblNodeGG)
	local nodes = {NodeGG}
	local edges = {}

	NatDGraph:addNodes(nodes)
	NatDGraph:addEdges(edges)
	NatDGraph:setRoot(NodeGG)
	return NatDGraph
end

-- @param letters Stores all atoms.  
local function createGraphFormula(formulasTable, letters)

	local S1
	local S2
	local nodes
	local edges
	local NodeLetter = nil	
	local FormulaGraph = Graph:new()

	if formulasTable.tag == "Atom" then 
		local prop_letter = formulasTable["1"]
		for k,v in pairs(letters) do 
			if k == prop_letter then 
				NodeLetter = v
			end
		end
		if not NodeLetter then	
			NodeLetter = NatDNode:new(prop_letter)
			letters[prop_letter] = NodeLetter
		end
	
		nodes = {NodeLetter}
		edges = {}
		
		FormulaGraph:addNodes(nodes)
		FormulaGraph:addEdges(edges)
		FormulaGraph:setRoot(NodeLetter)
		
	elseif formulasTable.tag == "imp" then

		S1, letters = createGraphFormula(formulasTable["1"],letters)
		S2, letters = createGraphFormula(formulasTable["2"],letters)

		local NodeImp = NatDNode:new(opImp.graph)
		local EdgeEsq = NatDEdge:new(lblEdgeEsq, NodeImp, S1.root)
		local EdgeDir = NatDEdge:new(lblEdgeDir, NodeImp, S2.root)

		nodes = {NodeImp}
		edges = {EdgeEsq, EdgeDir}

		FormulaGraph:addNodes(S1.nodes)
		FormulaGraph:addNodes(S2.nodes)
		FormulaGraph:addNodes(nodes)
		FormulaGraph:addEdges(S1.edges)
		FormulaGraph:addEdges(S2.edges)
		FormulaGraph:addEdges(edges)
		FormulaGraph:setRoot(NodeImp)

		-- TODO criar demais casos que não só implicação
	end

	return FormulaGraph, letters
end	

local function createGraphNatD(form_table, letters)

	local NatDGraph = Graph:new()
	local S,L
	local NodeGG = NatDNode:new(lblNodeGG)
	S,L = createGraphFormula(form_table, letters)

	local newEdge = NatDEdge:new(lblRootEdge, NodeGG, S.root)

	local nodes = {NodeGG}
	NatDGraph:addNodes(nodes)
	NatDGraph:addNodes(S.nodes)
	local edges = {newEdge}
	NatDGraph:addEdges(edges)
	NatDGraph:addEdges(S.edges)

	goalsList = {}
	goalsList[NodeGG:getLabel()] = {goal = generateNewGoal(NodeGG), weight = 1}

	return NatDGraph
end

local function markProvedPath(natDNode) 
	local node = natDNode

	while node ~= nil do
		node:setInformation("isProved", true)
		if node:getEdgeIn(lblEdgeDeducao) then 
			node = node:getEdgeIn(lblEdgeDeducao):getOrigem()
		else
			node = nil
		end
	end
end

local function markCounterExamplePath(natDNode) 
	local node = natDNode

	while node ~= nil do
		node:setInformation("isProved", false)
		if node:getEdgeIn(lblEdgeDeducao) then 
			node = node:getEdgeIn(lblEdgeDeducao):getOrigem()
		else
			node = nil
		end
	end
end

local function countGraphElements() 
	local countNodeElements = {}
	local countEdgesElements = {}  

	nodes = graph:getNodes()

	for i=1, #nodes do	
		if countNodeElements[nodes[i]:getInformation("type")] == nil then
			countNodeElements[nodes[i]:getInformation("type")] = 1
		else
			countNodeElements[nodes[i]:getInformation("type")] = countNodeElements[nodes[i]:getInformation("type")] + 1
		end
	end

	edges = graph:getEdges()

	for i=1, #edges do	
		if countEdgesElements[edges[i]:getLabel()] == nil then
			countEdgesElements[edges[i]:getLabel()] = 1
		else
			countEdgesElements[edges[i]:getLabel()] = countEdgesElements[edges[i]:getLabel()] + 1
		end
	end  

	for k,count in pairs(countNodeElements) do
		logger:info("statistics -- Total nodes of type "..krgrep.." is "..count)
	end

	for k,count in pairs(countEdgesElements) do
		logger:info("statistics -- Total nodes of type "..k.." is "..count)
	end

end

local function logGoalsList()
	logger:info("GoalsList:")	
	for k,v in pairs(goalsList) do
		if not goalsList[k].goal:getSequent():getInformation("isExpanded") then
			logger:info("seq: "..k.."; weight: "..goalsList[k].weight)
		end		
	end
end

local function resetGoalsWeight(pweight)

	local k, goalEntry
	
	for k,goalEntry in pairs(goalsList) do
		goalEntry.weight = pweight
	end	
end

local function degreeOfFormula(formulaNode)
	if formulaNode:getInformation("type") ~= opImp.graph then
		return 0
	else
		local degree = 1 + degreeOfFormula(formulaNode:getEdgeOut(lblEdgeDir):getDestino()) + degreeOfFormula(formulaNode:getEdgeOut(lblEdgeEsq):getDestino())
		return degree 
	end
end

local function compareFormulasDegree(formulaA, formulaB)
	local countFormulaA = degreeOfFormula(formulaA)
	local countFormulaB = degreeOfFormula(formulaB)

	return countFormulaB > countFormulaA
end

local function compareEdgesInBracket(edgeA, edgeB)
	local posA = tonumber(edgeA:getLabel())
	local posB = tonumber(edgeB:getLabel())

	return posA > posB
end

local function compareSequentsFormulas(sideSeq, sideSeqParent)
  
	local edgeSeqParent
	local formulaSeq
	local formulasSeqParent = {}
	local ret = true
	local i = 0	

	if sideSeqParent:getEdgesOut() == nil then
		formulasSeqParent = {}
	else		
		for _, edgeSeqParent in ipairs(sideSeqParent:getEdgesOut()) do
			local formulaNode = nil
			local ref = ""
			
			if edgeSeqParent:getDestino():getInformation("originalFormula") ~= nil then
				formulaNode = edgeSeqParent:getDestino():getInformation("originalFormula")
				local leftNodeParent = sideSeqParent:getEdgeIn("0"):getDestino()
				for _, edgeLeftParent in ipairs(leftNodeParent:getEdgesOut()) do
					if edgeLeftParent:getDestino() == formulaNode then
						ref = edgeLeftParent:getInformation("reference"):getLabel()
					end
				end
			else
				formulaNode = edgeSeqParent:getDestino()
				if edgeSeqParent:getInformation("reference") ~= nil then
					ref = edgeSeqParent:getInformation("reference"):getLabel()
				end						
			end					
			
			i = i + 1			
			formulasSeqParent[i] = formulaNode:getLabel()..ref		
		end
	end
	
	if sideSeq:getEdgesOut() == nil then
		if formulasSeqParent == nil then
			ret = true
		else
			ret = false
		end		
	else
		local setOfFormulas = Set:new(formulasSeqParent)
		
		for _, edgeSeq in ipairs(sideSeq:getEdgesOut()) do
			local formulaNode = nil
			local ref = ""
					
			if edgeSeq:getDestino():getInformation("originalFormula") ~= nil then
				formulaNode = edgeSeq:getDestino():getInformation("originalFormula")
				local leftNode = sideSeq:getEdgeIn("0"):getDestino()
				for _, edgeLeft in ipairs(leftNode:getEdgesOut()) do
					if edgeLeft:getDestino() == formulaNode then
						ref = edgeLeft:getInformation("reference"):getLabel()
					end
				end
			else
				formulaNode = edgeSeq:getDestino()
				if edgeSeq:getInformation("reference") ~= nil then
					ref = edgeSeq:getInformation("reference"):getLabel()
				end						
			end					 
				
			formulaSeq = formulaNode:getLabel()..ref
			if not setOfFormulas:contains(formulaSeq) then
				ret = false
				break
			end			
		end
	end
	
	return ret
end

local function checkLoop(natDNode)
  
	local esqNode, dirNode, dedSeq, esqNodeAnt, dirNodeAnt
	local ret = false
	local equalLeft, equalRight

	esqNode = natDNode:getEdgeOut(lblEdgeEsq):getDestino()
	dirNode = natDNode:getEdgeOut(lblEdgeDir):getDestino()

	if natDNode:getEdgeIn(lblEdgeDeducao) == nil then
		dedSeq = nil
	else
		dedSeq = natDNode:getEdgeIn(lblEdgeDeducao):getOrigem()
	end

	while dedSeq ~= nil do	  
		esqNodeAnt = dedSeq:getEdgeOut(lblEdgeEsq):getDestino()
		dirNodeAnt = dedSeq:getEdgeOut(lblEdgeDir):getDestino()

		equalLeft = compareSequentsFormulas(esqNode, esqNodeAnt)		
		equalRight = compareSequentsFormulas(dirNode, dirNodeAnt)
		
		if equalLeft and equalRight then
			ret = true
			natDNode:setInformation("repetition", true)
			dedSeq:setInformation("repetition", true)
			markCounterExamplePath(dedSeq)
			break
		else
			if dedSeq:getEdgeIn(lblEdgeDeducao) == nil then
				dedSeq = nil
			else
				dedSeq = dedSeq:getEdgeIn(lblEdgeDeducao):getOrigem()
			end
		end
	end

	
	return ret
end

local function generateCounterModel(natDNode, counterModel)

  local ret = nil

	if counterModel == nil then

		-- Cria nós dos mundos
		local world0 = Node:new(lblNodeWorld.."0")
		world0:setInformation("type", lblNodeWorld)
		
		local world1 = Node:new(lblNodeWorld.."1")
		world1:setInformation("type", lblNodeWorld)

		-- Criar aresta do sequente para o mundo 0
		local edgeCounter = Edge:new(lblEdgeCounterModel, natDNode, world0)
		
		-- Criar aresta do mundo 0 para o mundo 1
		local edgeAccess = Edge:new(lblEdgeAccessability, world0, world1)

		-- Adicionar nós e arestas no grafo
		graph:addNode(world0)
		graph:addNode(world1)
		graph:addEdge(edgeCounter)
		graph:addEdge(edgeAccess)
		
		local seqSideRight = natDNode:getEdgeOut(lblEdgeDir):getDestino()
		local seqSideLeft = natDNode:getEdgeOut(lblEdgeEsq):getDestino()
		local formula = nil
		local edgeSat = nil

		-- Para cada formula à esq do sequente, criar aresta SAT ligando ao mundo 1
		local leftFormulasEdges = seqSideLeft:getEdgesOut()
		for i=1,#leftFormulasEdges do
			formula = leftFormulasEdges[i]:getDestino()
			edgeSat = Edge:new(lblEdgeSatisfy, world1, formula)
			graph:addEdge(edgeSat)
		end

		-- Para cada formula à direita:
		-- Se estiver fora do bracket criar aresta NOT SAT ligando ao mundo 1
		local formulaOutsideBracket = seqSideRight:getEdgeOut("0"):getDestino()
		edgeSat = Edge:new(lblEdgeSatisfy, world1, formula)
		graph:addEdge(edgeSat)

		-- Se estiver no bracket criar aresta NOT SAT ligando ao mundo 0		
		local formulasInsideBracketEdges = seqSideRight:getEdgeOut("1"):getDestino():getEdgesOut()		
		for i=1,#formulasInsideBracketEdges do
			formula = formulasInsideBracketEdges[i]:getDestino()
			edgeSat = Edge:new(lblEdgeUnsatisfy, world0, formula)
			graph:addEdge(edgeSat)
		end
		
		ret = world0		
		
	end
	
	return ret3

end

local function getInitialNatDNode()
	if graph then  
		local goalEdge = graph:getNode(lblNodeGG):getEdgeOut(lblEdgeGoal)
		
		if goalEdge then
		  return goalEdge:getDestino()
		end
	end
end

-- Aplica a regra de introdução da implicação no nó selecionado, adicionando um elemento à lista
-- de hipóteses para descarte posterior.
local function applyImplyIntroRule(formulaNode)
	logger:debug("ImplyIntro: Expanding "..formulaNode:getLabel())

	local impLeft = formulaNode:getEdgeOut(lblEdgeEsq):getDestino()
	local impRight = formulaNode:getEdgeOut(lblEdgeDir):getDestino()

	-- Nós e arestas novos.
	local introStepNode = NatDNode:new(lblRuleImpIntro)
	local introStepEdge = NatDEdge:new(lblEdgeDeduction, formulaNode, introStepNode)
	local hypothesisEdge = NatDEdge:new(lblEdgeHypothesis, introStepNode, impLeft)
	local predicateEdge = NatDEdge:new(lblEdgePredicate, introStepNode, impRight)

	currentStepNumber = currentStepNumber + 1
	introStepEdge:setInformation("rule", opImp.tex.." \\mbox{intro}".."_{"..currentStepNumber.."}")

	-- Adiciona a hipótese à lista de hipóteses descartáveis
	LogicModule.dischargeable[currentStepNumber] = impLeft

	local newEdges = {introStepEdge, hypothesisEdge, predicateEdge}

	graph:addNode(introStepNode)
	graph:addEdges(newEdges)

	formulaNode:setInformation("isExpanded", true)

	logger:info("applyImplyIntroRule - "..formulaNode:getLabel().." was expanded")

	-- Aqui verificamos se o nó presente na parte superior da prova pode ser hipótese a descartar.
	for i, node in ipairs(LogicModule.dischargeable) do
		if LogicModule.nodeEquals(node, impRight) then
			impRight:setInformation("isExpanded", true)
			impRight:setInformation("discharged", true)
			break
		end
	end

	return graph
end

-- TODO alterar essa função para receber também a hipótese da esquerda
local function applyImplyElimRule(formulaNode, hypNode)
	logger:debug("ImplyElim: Expanding "..formulaNode:getLabel())

	local hypothesisNode = hypNode

	-- Nós e arestas novos.
	local elimStepNode = NatDNode:new(lblRuleImpElim)
	local newImpNode = NatDNode:new(opImp.graph)
	local newImpLeftEdge = NatDEdge:new(lblEdgeEsq, newImpNode, hypothesisNode)
	local newImpRightEdge = NatDEdge:new(lblEdgeDir, newImpNode, formulaNode)

	local elimStepEdge = NatDEdge:new(lblEdgeDeduction, formulaNode, elimStepNode)
	local predicateHypEdge = NatDEdge:new(lblEdgePredicate.."1", elimStepNode, hypothesisNode)
	local predicateImpEdge = NatDEdge:new(lblEdgePredicate.."2", elimStepNode, newImpNode)

	elimIndex = elimIndex + 1
	elimStepEdge:setInformation("rule", opImp.tex.." \\mbox{elim}".."_{"..elimIndex.."}")

	local newNodes = {newImpNode, elimStepNode}
	local newEdges = {newImpLeftEdge, newImpRightEdge, elimStepEdge, predicateHypEdge, predicateImpEdge}

	graph:addNodes(newNodes)
	graph:addEdges(newEdges)

	formulaNode:setInformation("isExpanded", true)

	logger:info("applyImplyElimRule - "..formulaNode:getLabel().." was expanded")

	-- Aqui verificamos se os nós presentes na parte superior da prova podem ser hipóteses a descartar.
	for i, node in ipairs(LogicModule.dischargeable) do
		if LogicModule.nodeEquals(node, newImpNode) then
			newImpNode:setInformation("isExpanded", true)
			newImpNode:setInformation("discharged", true)
		elseif LogicModule.nodeEquals(node, hypothesisNode) then
			hypothesisNode:setInformation("isExpanded", true)
			hypothesisNode:setInformation("discharged", true)
		end
	end

	return graph
end

function LogicModule.expandImplyIntroRule(agraph, formulaNode)
	local typeOfNode = formulaNode:getInformation("type")

	graph = agraph
	if typeOfNode == opImp.graph then
		impIntro(formulaNode)
	else
		logger:info("WARNING - ImpIntro used on an non-implication node.")
	end

	return true, graph	
end

function LogicModule.expandImplyElimRule(agraph, formulaNode, hypothesisNode)

	graph = agraph
	impElim(formulaNode, hypothesisNode)

	return true, graph	
end

-- Public functions

--- Create a graph from a formula in table form.
--- Returns a graph that represents the given formula.
--- @param form_table - Formula in table form.
function LogicModule.createGraphFromTable(form_table)
	local letters = {}
	sufix = 0
	local graph = nil
	
	if form_table =="empty" then 
		graph = createGraphEmpty()
	else
		graph = createGraphNatD(form_table, letters)
	end

	return graph
end

-- TODO aqui aplicar todos os implyintro e implyelim
function LogicModule.expandAll(agraph, natDNode)

	graph = agraph

	-- Começar a prova pelo nó inicial caso não tenha sido dado um nó
	local currentNode = natDNode
	if currentNode == nil then
		currentNode = graph:getNode(lblNodeGG):getEdgeOut(lblRootEdge):getDestino()
	end

	-- Primeiros passos: realizar repetidamente ImpIntros até não ter mais uma implicação
	while currentNode:getInformation("type") == opImp.graph do
		graph = applyImplyIntroRule(currentNode)
		currentNode = currentNode:getEdgeOut(lblEdgeDeduction):getDestino():getEdgeOut(lblEdgePredicate):getDestino()
	end

	-- Até aqui, temos a certeza de que há apenas um ramo a ser expandido, então guardamos esse nó.
	-- subRootNode será um nó fixo, para o qual voltaremos com currentNode caso necessário.
	local subRootNode = currentNode



	-- Passos seguintes: realizar ImpElims e ImpIntros conforme necessário nos ramos livres.
	-- Ramo aberto: sentença lógica ainda não provada.
	-- Ramo fechado: hipótese descartada.
	-- Utilizar também os Goals: serão retirados da lista de dischargeable.
	-- TODO verificar se há pelo menos alguma hipótese a ser utilizada (método auxiliar?)
	-- TODO alterar aqui para não pegar automaticamente da lista de dischargeable, mas pegar
	-- dos Goals.


	return true, graph
end

function LogicModule.getGraph()
	return graph
end

-- Função auxiliar recursiva para verificar igualdade de dois nós do grafo.
-- Adaptada apenas para implicações e termos atômicos, utilizada principalmente
-- para verificar se uma proposição lógica é uma hipótese a ser descartada.
-- Essa função é necessária pois podem haver dicersas implicações para um
-- mesmo par de proposições atômicas.
-- Exemplo: podemos ter dois nós com label imp0 e imp1, ambos ligados aos nós Q e P,
-- representando a mesma sentença Q → P. E, por terem labels diferentes, sem essa
-- função seriam considerados diferentes.
-- @param node1 Primeiro nó.
-- @param node2 Segundo nó.
-- @return true se são iguais, ou false caso sejam diferentes.
function LogicModule.nodeEquals(node1, node2)
	local node1Left, node1Right, node2Left, node2Right = nil

	-- Checagem de nós nulos. Aqui não é utilizado assert pois dois nós nulos teoricamente são iguais.
	--- Casos base
	if node1 == nil then
		logger:info("WARNING - function nodeEquals in module NaturalDeductionLogic recieved first parameter nil")
		-- Ambos os nós nulos, tecnicamente são iguais (mas é lançado um aviso).
		if node2 == nil then
			logger:info("WARNING - function nodeEquals in module NaturalDeductionLogic recieved second parameter nil")
			return true
		-- Primeiro nó nulo e segundo não nulo.
		else
			return false
		end
	else
		-- Primeiro nó não nulo e segundo nulo.
		if node2 == nil then
			logger:info("WARNING - function nodeEquals in module NaturalDeductionLogic recieved second parameter nil")
			return false
		end
	end

	-- Ambos os nós não nulos

	-- Ambos nós atômicos; basta comparar seus labels
	if node1:getInformation("type") ~= opImp.graph and node2:getInformation("type") ~= opImp.graph then
		return node1:getLabel() == node2:getLabel()
	-- Primeiro nó implicação, segundo nó atômico
	elseif node1:getInformation("type") == opImp.graph and node2:getInformation("type") ~= opImp.graph then
		return false
	-- Primeiro nó atômico, segundo nó implicação
	elseif node1:getInformation("type") ~= opImp.graph then
		return false

	-- Passo indutivo
	-- Ambos nós de implicação.
	else
		for i, edge in ipairs(node1:getEdgesOut()) do
			if edge:getLabel() == lblEdgeEsq then
				node1Left = edge:getDestino()
			elseif edge:getLabel() == lblEdgeDir then
				node1Right = edge:getDestino()
			end
		end

		for i, edge in ipairs(node2:getEdgesOut()) do
			if edge:getLabel() == lblEdgeEsq then
				node2Left = edge:getDestino()
			elseif edge:getLabel() == lblEdgeDir then
				node2Right = edge:getDestino()
			end
		end
		
		return LogicModule.nodeEquals(node1Left, node2Left) and LogicModule.nodeEquals(node1Right, node2Right)
	end
end

function clear()
	for i,v in ipairs(foundNodes) do
		v:setInformation("found", false)
	end
end

function load()
	local f = loadfile("commands.lua")
	f()
end

function impIntro(form)
	graph = applyImplyIntroRule(form)
	print_all()
	clear()
end

function impElim(form, hypNode)
	graph = applyImplyElimRule(form, hypNode)
	print_all()
	clear()
end

function run()
	LogicModule.expandAll(graph)
	clear()
end

function step(pstep)
	LogicModule.expandAll(graph, pstep)
	clear()
end

function print_all()
	PrintModule.printProof(graph, "", true, #LogicModule.dischargeable)
	os.showProofOnBrowser()	
	clear()	
end
