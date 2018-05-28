-------------------------------------------------------------------------------
-- testGraph.lua
--
-- Este módulo testa criação dos grafos de entrada para NatDProver, utilizando luaunit.
--
-- @author bpalkmim
-------------------------------------------------------------------------------

luaunit = require('luaunit')
require 'Logic/NaturalDeductionLogic'
require 'ParseInput'

TestGraph = {}

-- Geração de grafo vazio. Contém apenas o nó raiz.
function TestGraph:testEmpty()
	local graph = LogicModule.createGraphFromTable("empty")
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 1)
	luaunit.assertEquals(#(graph:getEdges()), 0)
	logger:info("Teste de grafo - vazio OK")
end

-- Geração de grafo de apenas uma fórmula.
function TestGraph:testA()
	local parsed_formula = parse_input("a")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 2)
	luaunit.assertEquals(#(graph:getEdges()), 1)
	logger:info("Teste de grafo - A OK")
end

-- Geração de grafo de a -> b.
function TestGraph:testAB()
	local parsed_formula = parse_input("a imp (b)")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 4)
	luaunit.assertEquals(#(graph:getEdges()), 3)
	logger:info("Teste de grafo - AB OK")
end

-- Geração do grafo de a -> (b -> a)
function TestGraph:testABA()
	local parsed_formula = parse_input("a imp (b imp (a))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 5)
	luaunit.assertEquals(#(graph:getEdges()), 5)
	logger:info("Teste de grafo - ABA OK")
end

-- Geração do grafo de (a -> (b -> c)) -> (b -> (a -> c))
function TestGraph:testABCBAC()
	local parsed_formula = parse_input("(a imp (b imp (c))) imp (b imp (a imp (c)))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 9)
	luaunit.assertEquals(#(graph:getEdges()), 11)
	logger:info("Teste de grafo - ABCBAC OK")
end

-- Geração do grafo de "(A1 imp (A2)) imp (((A1 imp (A2 imp (A3)))) imp (((A2 imp (A3 imp (A4)))) imp (((A3 imp (A4 imp (A5)))) imp (((A4 imp (A5 imp (A6)))) imp (((A5 imp (A6 imp (A7)))) imp (A1 imp (A7)))))))"
function TestGraph:testFib7()
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
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 26)
	luaunit.assertEquals(#(graph:getEdges()), 37)
	logger:info("Teste de grafo - Fib7 OK")
end

-- Geração do grafo de "(((A imp (B)) imp (B)) imp (A))"
function TestGraph:testPeirce()
	local parsed_formula = parse_input("(((A imp (B)) imp (B)) imp (A))")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 6)
	luaunit.assertEquals(#(graph:getEdges()), 7)
	logger:info("Teste de grafo - Peirce OK\n")
end

-- Geração do grafo de "((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)"
function TestGraph:testHermannTest()
	local parsed_formula = parse_input("((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)")
	local t_formula = convert_formula_totable(parsed_formula)
	local t_mimp_formula = implicational(t_formula)
	local graph = LogicModule.createGraphFromTable(t_mimp_formula)
	luaunit.assertNotNil(graph)
	luaunit.assertIsTable(graph)
	luaunit.assertEquals(#(graph:getNodes()), 8)
	luaunit.assertEquals(#(graph:getEdges()), 11)
	logger:info("Teste de grafo - HermannTest OK")
end