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

local function printFormula(formulaNode)
	local ret = ""
	local edge, subformula = nil

	-- Caso tenha nós filhos à esquerda ou à direita (implicação).
	if (formulaNode:getEdgesOut() ~= nil) and (#formulaNode:getEdgesOut() ~= 0) then
		for i, edge in ipairs(formulaNode:getEdgesOut()) do
			if edge:getLabel() == lblEdgeEsq then
				subformula = edge:getDestino()
				local printLeft = printFormula(subformula)
				if printLeft == "" then 
					ret = ret.."("
				else
					ret = ret.."("..printLeft.." "..opImp.tex.." "
				end
			end
		end

		for i, edge in ipairs(formulaNode:getEdgesOut()) do
			if edge:getLabel() == lblEdgeDir then
				subformula = edge:getDestino()
				ret = ret..printFormula(subformula)..")"
			end
		end
	else -- atômico
		-- Vale notar que um nó atômico pode ter nós filhos, mas o único caso possível é
		-- por uma aresta com label lblEdgeDed.
		ret = ret.." "..formulaNode:getLabel().." "
	end

	return ret
end

local function printProofStep(natDNode, file, printAll, currentStepNumber)
	local ret = ""
	local edge, nodeMain, nodeEsq, nodeDir, nodePred, nodePred1, nodePred2, nodeHyp = nil
	local deductions = {}
	local j = 1
	local rule = ""

	if natDNode ~= nil then

		if tonumber(natDNode:getLabel():sub(4)) == 8 then
			local x = 10
		end

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
--[[		
			if nodeHyp ~= nil then
				local formula = printFormula(nodeHyp)

				ret = ret.."\\["
				ret = ret..formula
				ret = ret.."\\]"
				-- TODO colocar o índice do descarte e igualá-lo ao da expressão que o descartou.
				-- TODO criar um contador global de hipóteses descartadas?
				ret = ret..","
				ret = ret:sub(1, ret:len()-1)
			end
]]
			local formula = printFormula(natDNode)
			ret = ret..formula

			-- →-Intro
			if nodePred ~= nil then
				printProofStep(nodePred, file, printAll, currentStepNumber)
				file:write(ret)
			-- →-Elim
			elseif nodePred1 ~= nil and nodePred2 ~= nil then
				local formula = printFormula(nodePred1)

				-- TODO verificar se é necessário correção
				ret = ret.."["..formula.."]".."_{"..currentStepNumber.."}"
				ret = ret.."\\qquad\\qquad\r"

				file:write(ret)

				printProofStep(nodePred2, file, printAll, currentStepNumber - 1)
			-- Nó pai de um nó de dedução
			elseif stepDed ~= nil then
				-- TODO ver se isso tá certo (provavelmente não!)
				printProofStep(stepDed, file, printAll, currentStepNumber - 1)
				file:write(ret)
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

					printProofStep(deductions[i], file, printAll, currentStepNumber)

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
					
					printProofStep(deductions[i], file, printAll, currentStepNumber)

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

-- Função pública

-- Função principal do módulo. Chama a função recursiva printProofStep.
-- @param agraph Grafo da prova.
-- @param nameSufix Sufixo para identificação da prova.
-- @param printAll Indicador de que a prova será toda impressa (booleano).
-- @return Uma string com a prova em LaTeX.
function PrintModule.printProof(agraph, nameSufix, printAll, currentStepNumber)
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

		printProofStep(step, file, printAll, currentStepNumber)

		file:write("\n$$")
		file:write("\\end{document}\n")
		file:close()

		ret = true
	end

	return ret
end