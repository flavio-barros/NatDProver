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

local function printFormula(formulaNode, shortedFormula)
	local ret = ""
	local edge, subformula = nil

	if shortedFormula == nil then shortedFormula = true end
		
	local formulaNumber = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
	local formulaNumberCopied = nil
	
	local originalFormula = formulaNode:getInformation("originalFormula")

	if originalFormula ~= nil then
		formulaNumber = originalFormula:getLabel():sub(6,formulaNode:getLabel():len())
		formulaNumberCopied = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
	end

	if (formulaNode:getEdgesOut() ~= nil) and (#formulaNode:getEdgesOut() ~= 0) then
		if not shortedFormula then
			for i, edge in ipairs(formulaNode:getEdgesOut()) do
				if edge:getLabel() == lblEdgeEsq then
					subformula = edge:getDestino()
					ret = ret.."("..printFormula(subformula, shortedFormula)
				end
			end
		end

		if originalFormula ~= nil then
			ret = ret.." "..opImp.tex.."_{"..formulaNumber.."}^{"..formulaNumberCopied.."}"
		else
			ret = ret.." "..opImp.tex.."_{"..formulaNumber.."}"
		end			

		if not shortedFormula then
			for i, edge in ipairs(formulaNode:getEdgesOut()) do
				if edge:getLabel() == lblEdgeDir then
					subformula = edge:getDestino()
					ret = ret..printFormula(subformula, shortedFormula)..")"
				end
			end
		end	
	else -- atômico
		ret = ret..formulaNode:getLabel()
	end

	return ret
end

local function printProofStep(natDNode, file, printAll)
	local ret = ""
	local edge, nodeMain, nodeEsq, nodeDir, nodePred = nil
	local deductions = {}
	local j = 1
	local rule = ""
	local shortedFormula = true

	if natDNode ~= nil then

		if tonumber(natDNode:getLabel():sub(4)) == 8 then
			local x = 10
		end

		local stepNumber = natDNode:getLabel():sub(4,natDNode:getLabel():len())
		if stepNumber == "1" then shortedFormula = false end

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
				-- TODO ver como printar, se é necessário por aqui. Talvez aqui colocar os parênteses ao redor?
			elseif edge:getLabel() == lblEdgePredicate then
				nodePred = edge:getDestino()
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
			if nodePred ~= nil then
				local formula = printFormula(nodePred, shortedFormula)

				ret = ret..formula
				ret = ret..","
				ret = ret:sub(1, ret:len()-1)
			end
]]
--[[
			edge = nil
			for i, edge in ipairs(nodeDir:getEdgesOut()) do
				ret = ret..printFormula(edge:getDestino(), shortedFormula)
				ret = ret..","
			end
			ret = ret:sub(1, ret:len()-1)
]]
			ret = ret..printFormula(natDNode, false)
			ret = ret..","
			ret = ret:sub(1, ret:len()-1)

			file:write(ret)
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
					printProofStep(deductions[i], file, printAll)
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
					
					printProofStep(deductions[i], file, printAll)
					if #deductions > 1 and i < #deductions then
						-- file:write(" & ")
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

		printProofStep(step, file, printAll)

		file:write("\n$$")	
		file:write("\\end{document}\n")
		file:close()

		ret = true
	end

	return ret
end