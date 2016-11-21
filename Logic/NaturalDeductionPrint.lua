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

-- Função auxiliar para definir como lidar com o subnó do nó corrente sendo impresso.
local function printSubNode(subNode, output, file, printAll)
	local ret = output

	-- Hipótese descartada; fim do ramo de dedução.
	if subNode:getInformation("discharged") then
		formula = PrintModule.printFormula(subNode)
		ret = ret.."["..formula.."]".."_{"..findInDischargeable(subNode).."}"

	-- Um nó que tem ramificações ainda.
	else
		PrintModule.printProofStep(subNode, file, printAll)
	end

	file:write(ret)
end

-- Função que imprime uma fórmula em lógica minimal (atômica ou implicação).
-- É recursiva, portanto podem haver implicações de implicações etc.
function PrintModule.printFormula(formulaNode)
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
		local printLeft = PrintModule.printFormula(nodeLeft)
		local printRight = PrintModule.printFormula(nodeRight)
		ret = ret.."("..printLeft.." "..opImp.tex.." "..printRight..")"

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

-- Funções públicas

-- Funão que imprime um passo dedutivo do grafo.
function PrintModule.printProofStep(natDNode, file, printAll)
	local ret = ""
	local edge, nodeMain, nodeEsq, nodeDir, nodePred, nodePred1, nodePred2, nodeHyp = nil
	local deductions = {}
	local j = 1
	local rule = ""

	if natDNode ~= nil then

		local stepNumber = natDNode:getLabel():sub(4, natDNode:getLabel():len())

		for i, edge in ipairs(natDNode:getEdgesOut()) do

			if edge:getLabel() == lblEdgeEsq then
				nodeEsq = edge:getDestino()
			elseif edge:getLabel() == lblEdgeDir then
				nodeDir = edge:getDestino()
			elseif edge:getLabel() == lblEdgeDeduction then
				local stepDed = edge:getDestino()
				deductions[j] = stepDed
				rule = edge:getInformation("rule")
				j = j+1

			elseif edge:getLabel() == lblEdgeHypothesis then
				-- TODO ver como printar, se é necessário por aqui. Talvez aqui colocar os colchetes ao redor?
				nodeHyp = edge:getDestino()

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

		if not natDNode:getInformation("wasPrinted") or printAll then		  
			if #deductions > 0 then
				file:write("\\infer["..rule.."]\n")
			end

			if natDNode:getInformation("isAxiom") then
				file:write("{\\color{blue}{")
			else
				file:write("{")
			end

			if natDNode:getInformation("isProved") ~= nil and not natDNode:getInformation("isProved") then
				file:write("{\\color{red}{")
			else
				file:write("{")
			end

			if natDNode:getInformation("repetition") then
				file:write("{\\color{green}{")
			else
				file:write("{")
			end

			local formula = PrintModule.printFormula(natDNode)
			ret = ret..formula

			-- →-Intro
			if nodePred ~= nil then
				printSubNode(nodePred, ret, file, printAll)

			-- →-Elim
			elseif nodePred1 ~= nil and nodePred2 ~= nil then
				printSubNode(nodePred1, ret, file, printAll)
				file:write(" \\qquad ")
				printSubNode(nodePred2, ret, file, printAll)

			-- Demais nós
			else
				file:write(ret)
			end

			if natDNode:getInformation("isAxiom") then
				file:write("}}")
			else				
				file:write("}")
			end

			if natDNode:getInformation("isProved") ~= nil and not natDNode:getInformation("isProved") then
				file:write("}}")
			else
				file:write("}")
			end

			if natDNode:getInformation("repetition") then
				file:write("}}")
			else				
				file:write("}")
			end

			if #deductions > 0 then
				file:write("\n{\n")

				for i, edge in ipairs(deductions) do

					PrintModule.printProofStep(deductions[i], file, printAll)

					if #deductions > 1 and i < #deductions then
						file:write(" & ")
					end					  
				end

				file:write("\n}")
			end
		else
			local close = false
			if #deductions == 0 then
				if not natDNode:getInformation("isAxiom") then
					file:write("\\infer["..rule.."]\n")
					file:write("\n{}")
					file:write("\\qquad\\qquad\r")
				end
			else				
				for i, edge in ipairs(deductions) do
					if not deductions[i]:getInformation("wasPrinted") then
						file:write("\\infer["..rule.."]\n")
						file:write("\n{\n")
						close = true
					end
					
					PrintModule.printProofStep(deductions[i], file, printAll)

					if #deductions > 1 and i < #deductions then
						file:write(" & ")
					end

					if close then
						file:write("\n}")
						file:write("\\qquad\\qquad\r")					
						close = false
					end
				end
			end
		end

		natDNode:setInformation("wasPrinted", true)
	end
end

-- Função principal do módulo. Chama a função recursiva printProofStep.
-- @param agraph Grafo da prova.
-- @param nameSufix Sufixo para identificação da prova.
-- @param printAll Indicador de que a prova será toda impressa (booleano).
-- @return Uma string com a prova em LaTeX.
function PrintModule.printProof(agraph, nameSufix, printAll)
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

		PrintModule.printProofStep(step, file, printAll)

		file:write("\n$$")
		file:write("\\end{document}\n")
		file:close()

		ret = true
	end

	return ret
end