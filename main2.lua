require 'ParseInput'
require 'Logic/NaturalDeductionLogic'
require 'Logic/NaturalDeductionPrintDot'

print("Geração de Provas")

file_name = arg[1]

print("arquivo: " .. file_name)

-- Ler aqruivo contendo as provas
-- Colocar as fórmulas em uma lista
local file = io.open(file_name, "r")
formulas = {}
for line in file:lines() do
    formulas[#formulas + 1] = line
end

print(#formulas.." fórmulas no arquivo "..file_name)

-- Gerar a prova para cada formula na lista de Provas
-- Salvar a prova gerada em arquivo .dot
for index = 1, #formulas do
    parsed_formula = parse_input(formulas[index])
    t_formula = convert_formula_totable(parsed_formula)
    local t_mimp_formula = implicational(t_formula)

    NatDGraph = LogicModule.createGraphFromTable(t_mimp_formula)
    ret, graph = LogicModule.expandAll(NatDGraph)
    ret = PrintDotModule.printProofDot(NatDGraph, index)
end
