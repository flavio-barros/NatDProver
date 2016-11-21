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

local function copyMarkedFormula(natDNode, formulaNode)

	local newNode = NatDNode:new(formulaNode:getInformation("type"))
	newNode:setInformation("originalFormula", formulaNode)
	graph:addNode(newNode)

	local leftEdgesOut = natDNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()	
	local newEdge = NatDEdge:new(""..#leftEdgesOut, natDNode:getEdgeOut(lblEdgeEsq):getDestino(), newNode)
	graph:addEdge(newEdge)

	for _, leftEdge in ipairs(leftEdgesOut) do
		if leftEdge:getDestino() == formulaNode then 
			for k,info in pairs(leftEdge:getInformationTable()) do
				if k ~= "reference" then
					newEdge:setInformation(k, info)
				end
			end
		end		
	end	

	return newNode
end

local function generateNewGoal(natDNode)

	if goalsList == nil then
		goalsList = {}
	end

	local edgesOut = natDNode:getEdgesOut()
	local newGoal = nil
	local j = 1

	-- TODO assim, há apenas uma lista com os goals possíveis.
	-- Verificar se não é necessário uma lista de subgoals
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

---
--- @param letters Stores all atoms.  
local function createGraphFormula(formula_tabela, letters)

	local S1
	local S2
	local nodes
	local edges
	local NodeLetter = nil	
	local FormulaGraph = Graph:new()

	if formula_tabela.tag == "Atom" then 
		local prop_letter = formula_tabela["1"]
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
		
	elseif formula_tabela.tag == "imp" then

		S1, letters = createGraphFormula(formula_tabela["1"],letters)
		S2, letters = createGraphFormula(formula_tabela["2"],letters)

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

local function verifySideOfSequent(natDNode, formulaNode)
	edgesOut = natDNode:getEdgesOut()

	if edgesOut == nil then
		return false
	end

	local retValues = {}

	for i=1, #edgesOut do
		if edgesOut[i]:getDestino():getLabel() == formulaNode:getLabel() then
			return true
		end
	end

	return false
end

--- Verifies operator side in a sequent
local function verifySideOfOperator(natDNode, formulaNode)
	edgesOutList = natDNode:getEdgesOut()
	if edgesOutList == nil then
		return nil
	end

	for i=1, #edgesOutList do
		if edgesOutList[i]:getLabel() == lblEdgeEsq then
			if verifySideOfSequent(edgesOutList[i]:getDestino(), formulaNode) then
				return "Left"
			end
		end

		if edgesOutList[i]:getLabel() == lblEdgeDir then
			if verifySideOfSequent(edgesOutList[i]:getDestino(), formulaNode) then
				return "Right"
			end
		end					
	end
	
	return nil 
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

local function isExpandable(natDNode)
	local ret = false
	local rule = ""
	local formulaNode = nil

	local rightFormulaNode = natDNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("0"):getDestino()
	local typeOfNode = rightFormulaNode:getInformation("type")
	formulaNode = rightFormulaNode
	if typeOfNode == opImp.graph then
		ret = true
		rule = lblRuleImplyRight
		logger:info("isExpandable - "..natDNode:getLabel().." ainda tem implicação `a direita.")
	end	

	if not ret then
		local leftFormulasEdges = natDNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgesOut()

		for i=1, #leftFormulasEdges do
			formulaNode = leftFormulasEdges[i]:getDestino()
			local typeOfNode = formulaNode:getInformation("type")
			
			if leftFormulasEdges[i]:getLabel() ~= "0" then
				if (leftFormulasEdges[i]:getInformation("reference") == nil or leftFormulasEdges[i]:getInformation("reference") == rightFormulaNode) and
				not focusedFormulas[formulaNode] then
					ret = true
					rule = lblRuleFocus
					logger:info("isExpandable - "..natDNode:getLabel().." ainda tem fórmulas para focar.")
					break
				end
			end
		end
	end
	
	if not ret then
		local leftExpandedFormulas = natDNode:getInformation("leftExpandedFormulas")

		logger:info("isExpandable - Left Expanded Formulas - "..natDNode:getLabel())
		for k,v in pairs(leftExpandedFormulas) do
			logger:info(k:getLabel())
		end

		local edgesInOriginal = nil
		local referenceFormula = nil
		local hasReference = false
		for _,edgesInFocus in ipairs(natDNode:getEdgeOut(lblEdgeEsq):getDestino():getEdgeOut("0"):getDestino():getEdgesOut()) do
			formulaNode = edgesInFocus:getDestino()
			if not leftExpandedFormulas[formulaNode:getInformation("originalFormula")] and formulaNode:getInformation("type") == opImp.graph then

				-- for _,edgesInOriginal in ipairs(formulaNode:getInformation("originalFormula"):getEdgesIn()) do
				--	 if edgesInOriginal:getInformation("reference") ~= nil then
				--		 referenceFormula = edgesInOriginal:getInformation("reference")
				--		 hasReference = true
				--		 if referenceFormula == rightFormulaNode then
				--			 ret = true
				--			 rule = lblRuleImplyLeft
				--			 logger:info("isExpandable - "..natDNode:getLabel().." ainda tem fórmulas focada não expandida com imply-left.")
				--			 break
				--		 end				
				--	 end
				-- end
				
				-- if hasReference then
				--	 break
				-- end

				ret = true
				rule = lblRuleImplyLeft
				logger:info("isExpandable - "..natDNode:getLabel().." ainda tem fórmulas focada não expandida com imply-left.")
				break
			end
		end		
	end

	if not ret then
		local restartedFormulas = natDNode:getInformation("restartedFormulas")

		if restartedFormulas == nil then
			ret = true
		else
			local edgesFormulasInsideBracket = natDNode:getEdgeOut(lblEdgeDir):getDestino():getEdgeOut("1"):getDestino():getEdgesOut()

			logger:info("Restarted Formulas - "..natDNode:getLabel())
			for k,v in pairs(restartedFormulas) do
				logger:info(k:getLabel())
			end			

			local i = #edgesFormulasInsideBracket
			while i >= 1 do 
				logger:info("isExpandable - "..natDNode:getLabel().." Inside Bracket: "..edgesFormulasInsideBracket[i]:getDestino():getLabel())
				if not restartedFormulas:contains(edgesFormulasInsideBracket[i]:getDestino()) then
					logger:info("isExpandable - "..natDNode:getLabel().." Restarted Formulas não contém "..edgesFormulasInsideBracket[i]:getDestino():getLabel())
					logger:info("isExpandable - "..natDNode:getLabel().." ainda tem fórmulas para restartar.")
					ret = true
					rule = lblRuleRestart
					formulaNode = edgesFormulasInsideBracket[i]:getDestino()
					break
				end
				i = i - 1
			end
		end
		
	end
	
	return ret, rule, formulaNode
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
local function applyImplyElimRule(formulaNode)
	logger:debug("ImplyElim: Expanding "..formulaNode:getLabel())

	-- TODO depois modificar para não pegar sempre o primeiro
	-- TODO verificar se há pelo menos alguma hipótese a ser utilizada (método auxiliar?)
	local hypothesisNode = LogicModule.dischargeable[currentStepNumber]
	currentStepNumber = currentStepNumber - 1

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

	-- TODO verificar se o newImpNode ou o outro lado estão na lista de hipóteses	

	return graph
end

function LogicModule.expandImplyIntroRule(agraph, formulaNode)
	local typeOfNode = formulaNode:getInformation("type")

	graph = agraph
	if typeOfNode == opImp.graph then
		impIntro(formulaNode)
	else
		print("\n\n\nImpIntro deve ser utilizado em implicacoes.\n\n\n")
		logger:info("WARNING - ImpIntro used on an non-implication node.")
	end

	return true, graph	
end

function LogicModule.expandImplyElimRule(agraph, formulaNode)
	local typeOfNode = formulaNode:getInformation("type")

	graph = agraph
	
	impElim(formulaNode)

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
--[[
	local isAllExpanded = true
	local k, goalEntry

	if natDNode then
		resetGoalsWeight(0)
		goalsList[natDNode:getLabel()].weight = 1
	end

	graph = agraph					
	
	for k,goalEntry in pairs(goalsList) do

		if goalEntry.weight == 1 then
		
			local seq = goalEntry.goal:getSequent()

			if not seq:getInformation("isExpanded") then
				logger:info("expandAll - Expanding seq "..k)
				
				isAllExpanded = false

				local formulaNode = nil
				local restartedFormulas = nil
				local leftExpandedFormula = nil
				local newSeq = nil
				local leftSide = goalEntry.goal:getLeftSide()
				local rightSide = goalEntry.goal:getRightSide()
				local expanded = false
				local restarted = false
				local edgesInLeft, restartedAtom

				table.sort(leftSide, compareFormulasDegree)

				if pstep == nil then
					nstep = 1
				else
					if tonumber(pstep) <= nstep then
						nstep = 0
						break
					else
						nstep = nstep + 1
					end
				end
				
				if tonumber(k:sub(4)) == 36 then
					local x = 10
				end			 

				if not verifyAxiom(seq) then
					local ret, rule, formulaNode = isExpandable(seq)

					if ret then
						if rule == lblRuleImplyRight then
							applyImplyRightRule(seq, formulaNode)
						elseif rule == lblRuleImplyLeft then
							applyImplyLeftRule(seq, formulaNode)
						elseif rule == lblRuleRestart then
							applyRestartRule(seq, formulaNode)
						end												
					else
						goalsList = {}
						nstep = 0
						logger:info("expandAll - "..seq:getLabel().." não pode mais ser expandido.")
						break							
					end						
				end		  
			end
		end		
	end

	local ret
	if not isAllExpanded and nstep ~= 0 then
		graph = LogicModule.expandAll(graph, pstep)
		ret = false
	else
		nstep = 0
		sufix = sufix + 1
		LogicModule.printProof(graph, tostring(sufix))
		os.showProofOnBrowser(tostring(sufix))
		logGoalsList()
		logger:info("expandAll - All sequents expanded!")
		ret = true
	end
]]
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

	-- Passos seguintes: realizar ImpElims e ImpIntros conforme necessário nos ramos livres.
	-- Ramo aberto: sentença lógica ainda não provada.
	-- Ramo fechado: hipótese descartada.
	-- TODO

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

	-- Ambos nós atômicos; basta comparar seus labels
	if node1Left == nil and node1Right == nil and node2Left == nil and node2Right == nil then
		return node1:getLabel() == node2:getLabel()
	-- Primeiro nó implicação, segundo nó atômico
	elseif (node1Left == nil and node1Right == nil) then
		return false
	-- Primeiro nó atômico, segundo nó implicação
	elseif (node2Left == nil and node2Right == nil) then
		return false

	-- Passo indutivo
	-- Ambos nós de implicação.
	else
		return LogicModule.nodeEquals(node1Left, node2Left) and LogicModule.nodeEquals(node1Right, node2Right)
	end
end

function findf(form)
	local goalEdge = graph:getNode(lblNodeGG):getEdgesOut()
	local seqNode = goalEdge[1]:getDestino()
	local found = false
	local formulaNode = nil

	while seqNode ~= nil do
		local leftSide = seqNode:getEdgeOut(lblEdgeEsq):getDestino()
		local rightSide = seqNode:getEdgeOut(lblEdgeDir):getDestino()
			
		for i=1,#leftSide:getEdgesOut() do
			local itemNode = leftSide:getEdgesOut()[i]:getDestino()
			found, formulaNode = findf_sub(itemNode, form)
			if found then
				break
			end		
		end

		if not found then
			for i=1,#rightSide:getEdgesOut() do
				local itemNode = rightSide:getEdgesOut()[i]:getDestino()
				if itemNode:getInformation("type") == lblNodeBrackets then
					local itemNodeEdges = itemNode:getEdgesOut()
					for j=1,#itemNodeEdges do
						found, formulaNode = findf_sub(itemNodeEdges:getDestino(), form)
						if found then
							break
						end
					end
				else
					found, formulaNode = findf_sub(itemNode, form)
					if found then
						break
					end
				end
			end
		end
		
		if seqNode:getEdgeOut(lblEdgeDeducao) ~= nil then
			seqNode = seqNode:getEdgeOut(lblEdgeDeducao):getDestino()
		else
			seqNode = nil
		end
	end
	
	return formulaNode
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

-- TODO completar
function impIntro(form)
	-- local formNode = findf(form)

	-- assert(formNode, "Formula was not found to apply ImplyIntro")

	graph = applyImplyIntroRule(form)
	print_all()
	clear()
end

function impElim(form)
	-- local formNode = findForm(form, lblNodeImp)

	--assert(formNode, "Formula was not found to apply ImplyElim")

	graph = applyImplyElimRule(form)
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
