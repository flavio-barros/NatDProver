-------------------------------------------------------------------------------
--	Natural Deduction Print Module
--
--	This module defines the functions for printing proofs in Latex.
--
--	@authors: bpalkmim
--
-------------------------------------------------------------------------------

require "Logic/NatDGraph"
require "Logic/Goal"
require "Logic/ConstantsForNatD"
require 'ParseInput'
require "Logic/Set"
require "Util/utility"

PrintModule = {}

-- Funções Locais

-- Função auxiliar que procura por um nó do grafo na lista de hipóteses descartadas, retornando o índice.
-- Caso não encontre, retorna zero.
local function findInDischargeable(formulaNode)
	local dedNumber = 0
	for i, node in ipairs(LogicModule.dischargeable) do
		if LogicModule.nodeEquals(node, formulaNode) then
			dedNumber = i
		end
	end
	return dedNumber
end

-- Função que imprime uma fórmula em lógica minimal (atômica ou implicação).
-- É recursiva, portanto podem haver implicações de implicações etc.
function printFormula(formulaNode)
	local ret = ""
	local edge, nodeLeft, nodeRight = nil

	-- Pega os nós da Esquerda e Direita (apenas existentes no caso de explicação).
	for i, edge in ipairs(formulaNode:getEdgesOut()) do
		if edge:getLabel() == lblEdgeEsq then
			nodeLeft = edge:getDestino()
		elseif edge:getLabel() == lblEdgeDir then
			nodeRight = edge:getDestino()
		end
	end

	-- Caso seja um nó de implicação nodeLeft e nodeRight são não nulos.
	if (nodeLeft ~= nil) and (nodeRight ~= nil) then
		local printLeft = printFormula(nodeLeft)
		local printRight = printFormula(nodeRight)
		ret = ret.."\\left("..printLeft.." "..opImp.tex.." "..printRight.."\\right)"
		
	-- Verificação a fim de evitar imprimir o Label de um nó de Dedução (ImpIntro ou ImpElim).
	elseif (#formulaNode:getLabel() >= 7) then
		if (formulaNode:getLabel():sub(1, 7) ~= lblRuleImpIntro:sub(1, 7)) and (formulaNode:getLabel():sub(1, 7) ~= lblRuleImpElim) then
			-- Nó atômico.
			-- Vale notar que um nó atômico pode ter nós filhos, mas o único caso possível é
			-- por uma aresta com label lblEdgeDed.
			ret = ret.." "..formulaNode:getLabel().." "
		end
	else
		ret = ret.." "..formulaNode:getLabel().." "
	end

	return ret
end

-- Função que imprime um passo dedutivo do grafo.
function PrintModule.printProofStep(natDNode, file)
	local edge, nodeEsq, nodeDir, nodePred, nodePred1, nodePred2, nodeHyp = nil
	local rule = ""
	local formula = ""

	if natDNode ~= nil then

		for i, edge in ipairs(natDNode:getEdgesOut()) do

			if edge:getLabel() == lblEdgeEsq then
				nodeEsq = edge:getDestino()
			elseif edge:getLabel() == lblEdgeDir then
				nodeDir = edge:getDestino()
			elseif edge:getLabel() == lblEdgeDeduction then
				local stepDed = edge:getDestino()
				rule = edge:getInformation("rule")

			-- Na →-Intro, há um predicado apenas (o outro é uma hipótese descartada).
			elseif edge:getLabel() == lblEdgePredicate then
				nodePred = edge:getDestino()

			-- Na →-Elim, temos duas arestas de predicado, enumeradas.
			elseif edge:getLabel() == lblEdgePredicate.."1" then
				nodePred1 = edge:getDestino()
			elseif edge:getLabel() == lblEdgePredicate.."2" then
				nodePred2 = edge:getDestino()
			end
		end

		-- Nó raiz do grafo
		if natDNode:getLabel() == lblNodeGG then
			printProofStep(natDNode:getEdgeOut(lblRootEdge):getDestino(), file)

		-- Caso tenha um nó dedutivo como filho, precisamos criar a regra de inferência
		elseif stepDed ~= nil then
			file:write("\\infer["..rule.."]\n")
			
			formula = printFormula(natDNode)
			file:write("{{"..formula.."}\n")

			file:write("{")
			printProofStep(stepDed, file)
			file:write("}}")

		-- É um nó de →-Intro. Basta delegar para o nó nodePred
		elseif nodePred ~= nil then
			printProofStep(nodePred, file)

		-- É um nó de →-Elim. Basta delegar para os nós nodePred1 e nodePred2
		elseif nodePred1 ~= nil and nodePred2 ~= nil then
			printProofStep(nodePred1, file)
			file:write("\n&\n")
			printProofStep(nodePred2, file)

		-- Nó de predicado lógico que não tem ramificações.
		else
			formula = printFormula(natDNode)

			-- Caso a hipótese seja descartada
			if natDNode:getInformation("discharged") then
				formula = "["..formula.."]".."_{"..findInDischargeable(natDNode).."}"
			end

			file:write("{"..formula.."}\n")

		end
	end
end

-- Função pública
-- Função principal do módulo. Chama a função recursiva printProofStep.
-- @param agraph Grafo da prova.
-- @param nameSufix Sufixo para identificação da prova.
-- @return Uma string com a prova em LaTeX.
function PrintModule.printProof(agraph, nameSufix)
	graph = agraph

	if nameSufix == nil then nameSufix = "" end
	
	local file = io.open("aux/prooftree"..nameSufix..".tex", "w")	
	local goalEdge = agraph:getNode(lblNodeGG):getEdgesOut()
	local ret = false

	if (goalEdge ~= nil) and (#goalEdge > 0) then
		
		local step = goalEdge[1]:getDestino()

		file:write("\\documentclass[landscape]{article}\n\n")
		file:write("\\usepackage{color}\n")
		file:write("\\usepackage{proof}\n")
		file:write("\\usepackage{qtree}\n\n")
		file:write("\\begin{document}\n")
		file:write("$$\n")

		PrintModule.printProofStep(step, file)

		file:write("\n$$")
		file:write("\\end{document}\n")
		file:close()

		ret = true
	end

	return ret
end