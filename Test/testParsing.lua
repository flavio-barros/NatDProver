-------------------------------------------------------------------------------
-- testParsing.lua
--
-- Este módulo testa o parsing da entrada do usuário, utilizando luaunit.
--
-- @author bpalkmim
-------------------------------------------------------------------------------

luaunit = require('luaunit')
require 'ParseInput'

TestParsing = {}

-- Testa o parsing de "a imp (", que gera erro.
function TestParsing:testError1()
	luaunit.assertErrorMsgContains("falha no reconhecimento de a imp (", parse_input, "a imp (")
	logger:info("Teste de parsing - erro1 OK")
end

-- Testa o parsing de "a imp b", que gera erro.
function TestParsing:testError2()
	luaunit.assertErrorMsgContains("falha no reconhecimento de a imp b", parse_input, "a imp b")
	logger:info("Teste de parsing - erro2 OK")
end

-- Testa o parsing de "a im (b)", que gera erro.
function TestParsing:testError3()
	luaunit.assertErrorMsgContains("falha no reconhecimento de a im (b)", parse_input, "a im (b)")
	logger:info("Teste de parsing - erro3 OK")
end

-- Testa o parsing de "a (", que gera erro.
function TestParsing:testError4()
	luaunit.assertErrorMsgContains("falha no reconhecimento de a (", parse_input, "a (")
	logger:info("Teste de parsing - erro4 OK")
end

-- Testa o parsing de "( a", que gera erro.
function TestParsing:testError5()
	luaunit.assertErrorMsgContains("falha no reconhecimento de ( a", parse_input, "( a")
	logger:info("Teste de parsing - erro5 OK")
end

-- Testa o parsing de "a"
function TestParsing:testA()
	local parsed_formula = parse_input("a")
	local t_formula = convert_formula_totable(parsed_formula)
	local a = implicational(t_formula)
	luaunit.assertNotNil(a)
	luaunit.assertIsTable(a)
	luaunit.assertItemsEquals(a, {"a", "Atom"})
	logger:info("Teste de parsing - A OK")
end

-- Testa o parsing de "a imp (b)"
function TestParsing:testAB()
	local parsed_formula = parse_input("a imp (b)")
	local t_formula = convert_formula_totable(parsed_formula)
	local ab = implicational(t_formula)
	luaunit.assertNotNil(ab)
	luaunit.assertIsTable(ab)
	luaunit.assertItemsEquals(ab["1"], {"a", "Atom"})
	luaunit.assertItemsEquals(ab["2"], {"b", "Atom"})
	luaunit.assertEquals(ab["tag"], "imp")
	logger:info("Teste de parsing - AB OK")
end

-- Testa o parsing de "a imp (b imp (a))"
function TestParsing:testABA()
	local parsed_formula = parse_input("a imp (b imp (a))")
	local t_formula = convert_formula_totable(parsed_formula)
	local aba = implicational(t_formula)
	luaunit.assertNotNil(aba)
	luaunit.assertIsTable(aba)
	luaunit.assertItemsEquals(aba["1"], {"a", "Atom"})
	luaunit.assertItemsEquals(aba["2"]["1"], {"b", "Atom"})
	luaunit.assertItemsEquals(aba["2"]["2"], {"a", "Atom"})
	luaunit.assertEquals(aba["2"]["tag"], "imp")
	luaunit.assertEquals(aba["tag"], "imp")
	-- Essa linha garante que o nó utilizado é o mesmo, pois ela compara referências.
	luaunit.assertEquals(aba["1"], aba["2"]["2"])
	logger:info("Teste de parsing - ABA OK")
end

-- Testa o parsing de "(a imp (b imp (c))) imp (b imp (a imp (c)))"
function TestParsing:testABCBAC()
	local parsed_formula = parse_input("(a imp (b imp (c))) imp (b imp (a imp (c)))")
	local t_formula = convert_formula_totable(parsed_formula)
	local abcbac = implicational(t_formula)
	luaunit.assertNotNil(abcbac)
	luaunit.assertIsTable(abcbac)
	luaunit.assertItemsEquals(abcbac["1"]["1"], {"a", "Atom"})
	luaunit.assertItemsEquals(abcbac["2"]["1"], {"b", "Atom"})
	luaunit.assertItemsEquals(abcbac["1"]["2"]["2"], {"c", "Atom"})
	luaunit.assertEquals(abcbac["1"]["2"]["tag"], "imp")
	luaunit.assertEquals(abcbac["2"]["2"]["tag"], "imp")
	luaunit.assertEquals(abcbac["1"]["tag"], "imp")
	luaunit.assertEquals(abcbac["2"]["tag"], "imp")
	luaunit.assertEquals(abcbac["tag"], "imp")
	-- Essas linhas garantem que o nó utilizado é o mesmo, pois elas comparam referências.
	luaunit.assertEquals(abcbac["1"]["1"], abcbac["2"]["2"]["1"]) -- a
	luaunit.assertEquals(abcbac["2"]["1"], abcbac["1"]["2"]["1"]) -- b
	luaunit.assertEquals(abcbac["2"]["2"]["2"], abcbac["1"]["2"]["2"]) -- c
	logger:info("Teste de parsing - ABCBAC OK")
end

-- Testa o parsing de "(A1 imp (A2)) imp (((A1 imp (A2 imp (A3)))) imp (((A2 imp (A3 imp (A4)))) imp (((A3 imp (A4 imp (A5)))) imp (((A4 imp (A5 imp (A6)))) imp (((A5 imp (A6 imp (A7)))) imp (A1 imp (A7)))))))"
function TestParsing:testFib7()
	local fib2 = "(A1 imp (A2))"
	local fib3 = fib2.." imp (((A1 imp (A2 imp (A3))))"
	local fib4 = fib3.." imp (((A2 imp (A3 imp (A4))))"
	local fib5 = fib4.." imp (((A3 imp (A4 imp (A5))))"
	local fib6 = fib5.." imp (((A4 imp (A5 imp (A6))))"
	local fib7 = fib6.." imp (((A5 imp (A6 imp (A7))))"
	local parsed_formula = parse_input(fib7.." imp (A1 imp (A7)))))))")
	local t_formula = convert_formula_totable(parsed_formula)
	local fib7AST = implicational(t_formula)
	luaunit.assertNotNil(fib7AST)
	luaunit.assertIsTable(fib7AST)
	luaunit.assertItemsEquals(fib7AST["2"]["1"]["1"], {"A1", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["1"]["1"], {"A2", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["1"]["1"], {"A3", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["1"]["1"], {"A4", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["1"], {"A5", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["2"]["1"], {"A6", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["2"]["2"], {"A7", "Atom"})
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["1"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["1"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["1"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["1"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["1"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["1"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["1"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["1"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["1"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["2"]["tag"], "imp")
	luaunit.assertItemsEquals(fib7AST["tag"], "imp")
	-- Essas linhas garantem que o nó utilizado é o mesmo, pois elas comparam referências.
	luaunit.assertEquals(fib7AST["1"]["1"], fib7AST["2"]["2"]["2"]["2"]["2"]["2"]["1"]) -- A1
	luaunit.assertEquals(fib7AST["1"]["2"], fib7AST["2"]["2"]["1"]["1"]) -- A2
	luaunit.assertEquals(fib7AST["2"]["2"]["2"]["1"]["1"], fib7AST["2"]["2"]["1"]["2"]["1"]) -- A3
	luaunit.assertEquals(fib7AST["2"]["2"]["2"]["2"]["1"]["1"], fib7AST["2"]["2"]["2"]["1"]["2"]["1"]) -- A4
	luaunit.assertEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["1"], fib7AST["2"]["2"]["2"]["2"]["1"]["2"]["1"]) -- A5
	luaunit.assertEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["2"]["1"], fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["2"]["1"]) -- A6
	luaunit.assertEquals(fib7AST["2"]["2"]["2"]["2"]["2"]["2"]["2"], fib7AST["2"]["2"]["2"]["2"]["2"]["1"]["2"]["2"]) -- A7
	logger:info("Teste de parsing - Fib7 OK")
end

-- Testa o parsing de "(((A imp (B)) imp (B)) imp (A))".
function TestParsing:testPeirce()
	local parsed_formula = parse_input("(((A imp (B)) imp (B)) imp (A))")
	local t_formula = convert_formula_totable(parsed_formula)
	local peirce = implicational(t_formula)
	luaunit.assertNotNil(peirce)
	luaunit.assertIsTable(peirce)
	luaunit.assertItemsEquals(peirce["1"]["1"]["1"], {"A", "Atom"})
	luaunit.assertItemsEquals(peirce["1"]["1"]["2"], {"B", "Atom"})
	luaunit.assertItemsEquals(peirce["1"]["2"], {"B", "Atom"})
	luaunit.assertItemsEquals(peirce["2"], {"A", "Atom"})
	luaunit.assertEquals(peirce["1"]["1"]["tag"], "imp")
	luaunit.assertEquals(peirce["1"]["tag"], "imp")
	luaunit.assertEquals(peirce["tag"], "imp")
	-- Essas linhas garantem que o nó utilizado é o mesmo, pois elas comparam referências.
	luaunit.assertEquals(peirce["2"], peirce["1"]["1"]["1"]) -- A
	luaunit.assertEquals(peirce["1"]["2"], peirce["1"]["1"]["2"]) -- B
	logger:info("Teste de parsing - Peirce OK\n")
end

-- Testa o parsing de "((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)".
function TestParsing:testHermannTest()
	local parsed_formula = parse_input("((((A imp (B)) imp (A)) imp (A)) imp (B)) imp (B)")
	local t_formula = convert_formula_totable(parsed_formula)
	local herm = implicational(t_formula)
	luaunit.assertNotNil(herm)
	luaunit.assertIsTable(herm)
	luaunit.assertItemsEquals(herm["1"]["1"]["1"]["1"]["1"], {"A", "Atom"})
	luaunit.assertItemsEquals(herm["1"]["1"]["1"]["1"]["2"], {"B", "Atom"})
	luaunit.assertItemsEquals(herm["1"]["1"]["1"]["2"], {"A", "Atom"})
	luaunit.assertItemsEquals(herm["1"]["1"]["2"], {"A", "Atom"})
	luaunit.assertItemsEquals(herm["1"]["2"], {"B", "Atom"})
	luaunit.assertItemsEquals(herm["2"], {"B", "Atom"})
	luaunit.assertEquals(herm["1"]["1"]["1"]["1"]["tag"], "imp")
	luaunit.assertEquals(herm["1"]["1"]["1"]["tag"], "imp")
	luaunit.assertEquals(herm["1"]["1"]["tag"], "imp")
	luaunit.assertEquals(herm["1"]["tag"], "imp")
	luaunit.assertEquals(herm["tag"], "imp")
	-- Essas linhas garantem que o nó utilizado é o mesmo, pois elas comparam referências.
	luaunit.assertEquals(herm["1"]["1"]["2"], herm["1"]["1"]["1"]["1"]["1"]) -- A
	luaunit.assertEquals(herm["1"]["1"]["2"], herm["1"]["1"]["1"]["2"]) -- A
	luaunit.assertEquals(herm["2"], herm["1"]["2"]) -- B
	luaunit.assertEquals(herm["2"], herm["1"]["1"]["1"]["1"]["2"]) -- B
	logger:info("Teste de parsing - HermannTest OK")
end