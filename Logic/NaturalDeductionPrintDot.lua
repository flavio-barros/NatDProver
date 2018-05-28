-------------------------------------------------------------------------------
--	Natural Deduction Print Dot Module
--
--	This module defines the functions for printing proofs in Dot.
--
--	@authors: bpalkmim
--
-------------------------------------------------------------------------------

require "Logic/NatDGraph"
require "Logic/ConstantsForNatD"
require "Logic/NaturalDeductionLogic"

PrintDotModule = {}

-- Funções Locais
-- Função auxiliar que procura por um nó do grafo na lista de hipóteses descartadas.
-- @param formulaNode Nó a ser buscado.
-- @return Índice nas hipóteses descartadas. Zero caso não tehna sido encontrada.
local function findInDischargeable(formulaNode)
	local dedNumber = 0
	for i, node in ipairs(LogicModule.dischargeable) do
		if LogicModule.nodeEquals(node, formulaNode) then
			dedNumber = i
			break
		end
	end

	return dedNumber
end

-- Função que returna uma string de fórmula em lógica minimal (atômica ou implicação).
-- É recursiva, portanto podem haver implicações de implicações etc.
-- @param formulaNode Fómula a ser impressa.
-- @return String contendo a representação de formulaNode em DOT.
local function printFormula(formulaNode)
	local ret = ""
	local nodeLeft, nodeRight = nil

	-- Pega os nós da Esquerda e Direita (apenas existentes no caso de explicação).
	for _, edge in ipairs(formulaNode:getEdgesOut()) do
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
		ret = ret.."("..printLeft.." -> "..printRight..")"

	-- Verificação a fim de evitar imprimir o Label de um nó de Dedução (ImpIntro ou ImpElim).
	elseif (#formulaNode:getLabel() >= 7) then
		if (formulaNode:getLabel():sub(1, 7) ~= lblRuleImpIntro:sub(1, 7)) and (formulaNode:getLabel():sub(1, 7) ~= lblRuleImpElim) then
			-- Nó atômico.
			-- Vale notar que um nó atômico pode ter nós filhos, mas o único caso possível é
			-- por uma aresta com label lblEdgeDed.."i", onde i vai de 1 ao número de deduções que partem do nó.
			ret = ret.." "..formulaNode:getLabel().." "
		end
	else
		ret = ret.." "..formulaNode:getLabel().." "
	end

	return ret
end

-- Função que retorna um string de nó de fim de ramo (aberto ou fechado).
-- @param natDNode Nó da prova a ser impresso.
-- @return String contendo a representação de natDNode em DOT.
local function printFinalNode(natDNode)
	local formula = printFormula(natDNode)

	if natDNode:getInformation("discharged") then
		formula = "["..formula.."]".."_{"..findInDischargeable(natDNode).."}"
	end

	return "\""..formula.."\""
end

-- Função que imprime um passo dedutivo do grafo. Vale notar que a função é recursiva.
-- @param natDNode Nó a ser impresso.
-- @param file Path do arquivo a ser criado.
-- @param currentRule Regra atual sendo aplicada.
-- @return String contendo a representação de natDNode em DOT.
local function printProofStep(natDNode, file, previous)
	local nodePred, nodeHyp, nodePred1, nodePred2, stepDed = nil
	local currentIntro = 0

	if natDNode ~= nil then
		for _, edge in ipairs(natDNode:getEdgesOut()) do
			-- Nó de implicação ou atômico que apresenta uma dedução
			if edge:getLabel() == lblEdgeDeduction..natDNode:getInformation("nextDED") then
				stepDed = edge:getDestino()

				-- Altera a dedução caso haja uma outra dedução diferente partindo deste nó.
				if natDNode:getEdgeOut(lblEdgeDeduction..(natDNode:getInformation("nextDED") + 1)) ~= nil then
					natDNode:setInformation("nextDED", natDNode:getInformation("nextDED") + 1)
				end

			-- Na →-Intro, há um predicado apenas (o outro é uma hipótese descartada).
			elseif edge:getLabel() == lblEdgePredicate then
				nodePred = edge:getDestino()
			elseif edge:getLabel() == lblEdgeHypothesis then
				nodeHyp = edge:getDestino()

			-- Na →-Elim, temos duas arestas de predicado, enumeradas.
			elseif edge:getLabel() == lblEdgePredicate.."1" then
				nodePred1 = edge:getDestino()
			elseif edge:getLabel() == lblEdgePredicate.."2" then
				nodePred2 = edge:getDestino()
			end
		end

		-- Verifica nós repetidos
		if natDNode:getInformation("Printed") == nil then
			natDNode:setInformation("Printed", 0)
		end

		-- Nó de predicado lógico que não tem ramificações, descartado. Em azul.
		if (natDNode:getInformation("discharged") == true and currentIntro >= findInDischargeable(natDNode)) then
			file:write("\""..printFinalNode(natDNode).."\" [color=blue];\n")

		-- Nó de predicado lógico que não ramifica mas não foi descartado. Em vermelho.
		elseif natDNode:getInformation("Invalid") == true and (natDNode:getEdgeOut(lblEdgeDeduction..(natDNode:getInformation("nextDED") + 1) == nil) or natDNode:getEdgeOut(lblEdgeDeduction.."1") == nil) then
			file:write("\""..printFormula(natDNode).."\" [color=red];\n")

		-- Caso tenha um nó dedutivo como filho, precisamos criar a regra de inferência
		elseif stepDed ~= nil then
			printProofStep(stepDed, file, natDNode)

		-- É um nó de →-Intro
		-- Arestas indicando descarte de hipóteses estão em verde.
		elseif nodePred ~= nil and nodeHyp ~= nil then
			local hypPrinted = nodeHyp:getInformation("Printed")
			local predPrinted = nodePred:getInformation("Printed")
			local prevPrinted = previous:getInformation("Printed")
			local hypFormula = printFormula(nodeHyp)
			local predFormula = printFormula(nodePred)
			local prevFormula = printFormula(previous)

			if hypFormula == nil then
				hypFormula = ""
			end

			if hypPrinted ~= nil and hypPrinted ~= 0 then
				hypFormula = hypFormula.."  "..hypPrinted
			end

			if predPrinted ~= nil and predPrinted ~= 0 then
				predFormula = predFormula.."  "..predPrinted
			end

			if prevPrinted ~= nil and prevPrinted ~= 0 then
				prevFormula = prevFormula.."  "..prevPrinted
			end

			file:write("\""..hypFormula.."\" -> \""..prevFormula.."\" [color=green];\n")
			file:write("\""..prevFormula.."\" -> \""..predFormula.."\";\n")

			printProofStep(nodePred, file, previous)

		-- É um nó de →-Elim
		elseif nodePred1 ~= nil and nodePred2 ~= nil then
			local pred1Printed = nodePred1:getInformation("Printed")
			local pred2Printed = nodePred2:getInformation("Printed")
			local prevPrinted = previous:getInformation("Printed")
			local pred1Formula = printFormula(nodePred1)
			local pred2Formula = printFormula(nodePred2)
			local prevFormula = printFormula(previous)

			if pred1Printed ~= nil then
				nodePred1:setInformation("Printed", pred1Printed + 1)
			else
				nodePred1:setInformation("Printed", 0)
			end
			if pred2Printed ~= nil then
				nodePred2:setInformation("Printed", pred2Printed + 1)
			else
				nodePred2:setInformation("Printed", 0)
			end

			pred1Printed = nodePred1:getInformation("Printed")
			pred2Printed = nodePred2:getInformation("Printed")

			if pred1Printed ~= 0 then
				pred1Formula = pred1Formula.."  "..pred1Printed
			end

			if pred2Printed ~= 0 then
				pred2Formula = pred2Formula.."  "..pred2Printed
			end

			if prevPrinted ~= 0 then
				prevFormula = prevFormula.."  "..prevPrinted
			end

			file:write("\""..prevFormula.."\" -> \""..pred1Formula.."\";\n")
			file:write("\""..prevFormula.."\" -> \""..pred2Formula.."\";\n")

			printProofStep(nodePred1, file, previous)
			printProofStep(nodePred2, file, previous)

		end
	end
end

-- Função Pública
-- Função principal do módulo. Chama a função recursiva printProofStep.
-- As arestas de demonstração da prova serão as "principais" e as demais, secundárias.
-- @param agraph Grafo da prova.
-- @param nameSufix Sufixo para identificação da prova.
-- @return true caso tenha recebido um grafo válido e escrito a prova.
function PrintDotModule.printProofDot(agraph, nameSufix)

	if nameSufix == nil then nameSufix = "" end

	local file = io.open("aux/prooftreeDot"..nameSufix..".dot", "w")
	local ret = false

	if agraph ~= nil then

		local step = agraph:getNode(lblNodeGG):getEdgeOut(lblRootEdge):getDestino()

		file:write("digraph prooftreeDot"..nameSufix.." {\n")

		printProofStep(step, file, nil)

		file:write("}\n")
		file:close()

		ret = true
	end

	return ret
end