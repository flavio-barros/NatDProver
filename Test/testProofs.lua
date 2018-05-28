-------------------------------------------------------------------------------
-- testProofs.lua
--
-- Este módulo testa as provas geradas por NatDProver, utilizando luaunit.
--
-- @author bpalkmim
-------------------------------------------------------------------------------

luaunit = require('luaunit')
require 'Logic/NaturalDeductionLogic'
require 'ParseInput'

TestProofs = {}

-- Testa a geração de prova de "a", que não consegue ser realizada.
function TestProofs:testA()
	local parsed_formula = parse_input("a")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertTrue(ret)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 2)
	luaunit.assertEquals(#(graph:getEdges()), 1) -- Mesmo tamanho do grafo anterior, nada foi feito
	logger:info("Teste Prova - A OK")
end

-- Testa a geração de prova de "a -> b", que fica incompleta.
function TestProofs:testAB()
	local parsed_formula = parse_input("a imp (b)")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertFalse(ret) -- Aqui garantimos que a prova não pôde ser realizada
	luaunit.assertEquals(#(graph:getNodes()), 5)
	luaunit.assertEquals(#(graph:getEdges()), 6)
	luaunit.assertEquals(graph:getNode("b"):getInformation("Invalid"), true) -- Nó marcado como inválido
	luaunit.assertEquals(#openBranchesList, 1)
	luaunit.assertEquals(openBranchesList[1], graph:getNode("b")) -- Há ramos abertos
	logger:info("Teste Prova - AB OK")
end

-- Testa a geração de prova de "a -> (b -> a)".
function TestProofs:testABA()
	local parsed_formula = parse_input("a imp (b imp (a))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertTrue(ret)
	luaunit.assertEquals(#(graph:getNodes()), 7)
	luaunit.assertEquals(#(graph:getEdges()), 11)
	luaunit.assertEquals(#openBranchesList, 0)
	logger:info("Teste Prova - ABA OK")
end

-- Testa a geração de prova de "(a imp (b imp (c))) imp (b imp (a imp (c)))".
function TestProofs:testABCBAC()
	local parsed_formula = parse_input("(a imp (b imp (c))) imp (b imp (a imp (c)))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertTrue(ret)
	luaunit.assertEquals(#(graph:getNodes()), 14)
	luaunit.assertEquals(#(graph:getEdges()), 26)
	luaunit.assertEquals(#openBranchesList, 0)
	logger:info("Teste Prova - ABCBAC OK")
end

-- Testa a geração de prova de "(A1 imp (A2)) imp (((A1 imp (A2 imp (A3)))) imp (((A2 imp (A3 imp (A4)))) imp (((A3 imp (A4 imp (A5)))) imp (((A4 imp (A5 imp (A6)))) imp (((A5 imp (A6 imp (A7)))) imp (A1 imp (A7)))))))".
function TestProofs:testFib7()
	local fib2 = "(A1 imp (A2))"
	local fib3 = fib2.." imp (((A1 imp (A2 imp (A3))))"
	local fib4 = fib3.." imp (((A2 imp (A3 imp (A4))))"
	local fib5 = fib4.." imp (((A3 imp (A4 imp (A5))))"
	local fib6 = fib5.." imp (((A4 imp (A5 imp (A6))))"
	local fib7 = fib6.." imp (((A5 imp (A6 imp (A7))))"
	local parsed_formula = parse_input(fib7.." imp (A1 imp (A7)))))))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertTrue(ret)
	luaunit.assertEquals(#(graph:getNodes()), 44)
	luaunit.assertEquals(#(graph:getEdges()), 91)
	luaunit.assertEquals(#openBranchesList, 0)
	logger:info("Teste Prova - Fib7 OK")
end

-- Testa a geração de prova de "(((A imp (B)) imp (B)) imp (A))", que fica incompleta.
function TestProofs:testPeirce()
	local parsed_formula = parse_input("(((A imp (B)) imp (B)) imp (A))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertFalse(ret) -- Aqui garantimos que a prova não pôde ser realizada
	luaunit.assertEquals(#(graph:getNodes()), 7)
	luaunit.assertEquals(#(graph:getEdges()), 10)
	luaunit.assertEquals(graph:getNode("A"):getInformation("Invalid"), true) -- Nó marcado como inválido
	luaunit.assertEquals(#openBranchesList, 1)
	luaunit.assertEquals(openBranchesList[1], graph:getNode("A")) -- Há ramos abertos
	logger:info("Teste Prova - Peirce OK\n")
end

-- Testa a geração de prova de "((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)".
function TestProofs:testHermannTest()
	local parsed_formula = parse_input("((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	local ret = false
	ret, graph = LogicModule.expandAll(graph, nil)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertTrue(ret)
	luaunit.assertEquals(#(graph:getNodes()), 15)
	luaunit.assertEquals(#(graph:getEdges()), 32)
	luaunit.assertEquals(#openBranchesList, 0)
	logger:info("Teste Prova - HermannTest OK")
end