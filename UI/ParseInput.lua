------------------------------------------------------------------------------
--   Parse Input Module
--
--   Utilitary module to parse formula input.
--
--   @authors: Vitor, Hermann, Jefferson
--
-------------------------------------------------------------------------------

require "Logic/Set"
require "logging" 
require "logging.file"

local lpeg = require "lpeg"
local atom_count = 0
local mimp_t = Set:new()
local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)


-- Parsing functions
local function table_atom(x)
   return (string.format("\"%s\"", x))
end

local function table_formula(f)
   if f.tag == "Atom" then 
      return("[ Atom "..table_atom(f[1]).." ]")
   elseif f.tag == "imp" then
      return("[ Imp"..table_formula(f[1])..","..table_formula(f[2]).."]")     
   elseif f.tag == "and" then
      return("[ And"..table_formula(f[1])..","..table_formula(f[2]).."]")     
   elseif f.tag == "or" then
      return("[ Or"..table_formula(f[1])..","..table_formula(f[2]).."]")     
   end 
end     

local function table_formulas(t)
   if #t > 0 then 
      local s = ""
      for i=1,#t do
	 p = p.." ( "..i..table_formula(t[i]).." ) "
      end    
   else 
      return(t.tag.."empty")
   end
end

local function print_Goal(t)
   io.write("[ Goal ")
   if #t > 0 then
      print_formulas(t[1])
      io.write(" SEQ ")
      print_formulas(t[2])
   end
   io.write("]")
end


local function print_ast(t)
   if t.tag == "Goal" then
      print_Goal(t)
   end
   print("nothing to print")
end

local function table_formula(t)
   if type(t) == "number" then 
      return(t)
   elseif type(t) == "string" then
      return(string.format("%s", t))
   elseif type(t) == "table" then 
      local s = "{ "
      for k,v in pairs(t) do
	 s = s.."[ "..table_formula(k).."="..table_formula(v).." ]"
      end
      s = s.." }"
      return(s)
   else
      print("cannot convert table object")
   end 
end 

-- Lexical Elements
local Space = lpeg.S(" \n\t")
local skip = Space^0

local upper = lpeg.R("AZ")
local lower = lpeg.R("az")
local letter = upper + lower
local dig = lpeg.R("09")^0

local Atom = lpeg.C(letter * dig) * skip

local function getcontents(filename)
   file = assert(io.open(filename, "r"))
   contents = file:read("*a")
   file:close()
   return contents
end

local function token(pat)
   return pat * skip
end

local function kw(str)
   return token (lpeg.P(str))
end

local function symb(str)
   return token (lpeg.P(str))
end

local function taggedCap(tag, pat)
   return lpeg.Ct(lpeg.Cg(lpeg.Cc(tag), "tag") * pat)
end

function parse_input(contents)
   -- Grammar
   local formula = lpeg.V("formula")
   local form, factor, term = lpeg.V("form"), lpeg.V("factor"), lpeg.V("term")
   local term_imp, term_and, term_or = lpeg.V("term_imp"), lpeg.V("term_and"), lpeg.V("term_or")
   local Atomo = taggedCap("Atom", token(Atom))
   G = lpeg.P{ 
      formula,
      formula = skip * form * skip * -1;
      form = term + factor;
      factor = taggedCap("Atom", token(Atom)) + symb("(") * form * symb(")");
      term = term_imp + term_and + term_or;
      term_imp = taggedCap("imp", factor * kw("imp") * symb("(") * form * symb(")"));
      term_and = taggedCap("and", factor * kw("and") * symb("(") * form * symb(")")); 
      term_or = taggedCap("or", factor * kw("or") * symb("(") * form * symb(")"));       
   }

   local t = lpeg.match(G, contents)
   assert(t, "falha no reconhecimento de "..contents)

   ast = table_formula(t)
   return(ast)
end

-- MIMP translation functions

local function fresh_atom()
   local ret = "p"..atom_count

   atom_count = atom_count + 1
   return ret
end

-- Recursivelly replace formulas by propositional letters
--
-- @param formula a formula, in table format which will have its
--               non-MIMP subformulas translated in new propostional letters
-- @return a propositonal representation of non-MIMP (sub)formulas as string
local function mimp(formula)
   local s_formula = convert_formula_tostring(formula)
   
   if mimp_t[s_formula] then
      return mimp_t[s_formula]
   else
      if formula["tag"] == "Atom" then
         return formula["1"]
      elseif formula["tag"] == "imp" then
         return "("..mimp(formula["1"]).." imp ("..mimp(formula["2"]).."))"
      elseif formula["tag"] == "and" then
         return fresh_atom()
      elseif formula["tag"] == "or" then
         return fresh_atom()
      end
   end
end

-- Recursivelly builds a set of axioms to make the translation to MIMP Logic
-- 
-- @param alpha the initial formula to be translated, in table format.
-- @param formula subformulas of the initial formula to be examined recursivelly.
-- @return a set of axioms of MIMP Logic in table format.
local function axioms(alpha, formula)
   
   local set1
   local set2
   
   if formula["tag"] == "Atom" then
      return Set:new()
      
   elseif formula["tag"] == "imp" then
      set1 = axioms(alpha, formula["1"])
      set2 = axioms(alpha, formula["2"])
      return set1:union(set2)
      
   elseif formula["tag"] == "and" then
      local s_formula = convert_formula_tostring(formula)
      local formula_esq_s = convert_formula_tostring(formula["1"])
      local formula_dir_s = convert_formula_tostring(formula["2"])  
      
      local p = mimp_t[s_formula]

      local axiom1 = parse_input(mimp_t[formula_esq_s].." imp ("..mimp_t[formula_dir_s].." imp ("..p.."))")
      local axiom2 = parse_input(p.." imp ("..mimp_t[formula_esq_s]..")")
      local axiom3 = parse_input(p.." imp ("..mimp_t[formula_dir_s]..")")
      
      local axiom1_t = convert_formula_totable(axiom1)
      local axiom2_t = convert_formula_totable(axiom2)
      local axiom3_t = convert_formula_totable(axiom3)
      
      local axioms_set = Set:new({axiom1_t, axiom2_t, axiom3_t})

      set1 = axioms_set:union(axioms(alpha, formula["1"]))
      set2 = set1:union(axioms(alpha, formula["2"]))
      
      return set2
      
   elseif formula["tag"] == "or" then
      local s_formula = convert_formula_tostring(formula)
      local formula_esq_s = convert_formula_tostring(formula["1"])
      local formula_dir_s = convert_formula_tostring(formula["2"])  
      
      local q = mimp_t[s_formula]

      local axiom1 = parse_input(mimp_t[formula_esq_s].." imp ("..q..")")   
      local axiom2 = parse_input(mimp_t[formula_dir_s].." imp ("..q..")")
      local axiom1_t = convert_formula_totable(axiom1)
      local axiom2_t = convert_formula_totable(axiom2)
      local axioms_set = Set:new({axiom1_t, axiom2_t})

      local axioms_sub = nil
      local axioms_sub_t = nil
      local axioms_sub_set = Set:new() 
      for k,_ in pairs(mimp_t) do
         axioms_sub = parse_input("("..mimp_t[formula_esq_s].." imp (".. mimp_t[k]..")) imp (("..mimp_t[formula_dir_s].." imp ("..mimp_t[k]..")) imp (("..
                                     q.." imp ("..mimp_t[k].."))))")
         axioms_sub_t = convert_formula_totable(axioms_sub)
         axioms_sub_set:add(axioms_sub_t)
      end

      local set_or = axioms_set:union(axioms_sub_set)
      
      set1 = set_or:union(axioms(alpha, formula["1"]))
      set2 = set1:union(axioms(alpha, formula["2"]))

      return set2
   end
   
end

local function subformulas(formula)
   
   if formula["tag"] == "Atom" then
      return  Set:new({convert_formula_tostring(formula)})
   else
      local sub1_set = subformulas(formula["1"])
      local sub2_set = subformulas(formula["2"])
      local sub1_u_sub2 = sub1_set:union(sub2_set)
      
      local actual_formula = Set:new({convert_formula_tostring(formula)})
      local subformulas_set = sub1_u_sub2:union(actual_formula)

      return subformulas_set
   end
end


local function compare_formulas_size(a, b)
   return (string.len(a) < string.len(b))
end


-- Translates formulas from Intuitionistic Logic to Minimal Implicational Logic
--
-- @param t_formula a formula parsed into table format
-- @return a translated formula in table format 
function implicational(t_formula)

   local s_formula = convert_formula_tostring(t_formula)
   local subformulas_set = subformulas(t_formula)

   local l = {}
   for k,_ in pairs(subformulas_set) do 
      table.insert(l, k)
   end
   
   table.sort(l, compare_formulas_size)
   
   for _,v in ipairs(l) do
      local new_v = mimp(convert_formula_totable(parse_input(v)))
      mimp_t[v] = new_v      
   end

   local axiom_set = axioms(t_formula, t_formula)
   
   local alpha = convert_formula_totable(parse_input(mimp_t[s_formula]))
   
   for k,_ in pairs(axiom_set) do
      local s_k = convert_formula_tostring(k)
      local s_alpha = convert_formula_tostring(alpha)
      alpha = {["1"] = k, ["2"] = alpha, ["tag"] = "imp"}
   end
   
   return alpha
end

-- String to Table/Table to String convertion functions

function convert_formula_totable(s)
   local t = {}
   
   if s == nil then
      return
   end
   
   for k in string.gmatch(s, "(%b[])") do
      v1=string.match(k,"%[%s*([^=]+)=.+")
      if v1 =="tag" then
	 v1,v2= string.match(k,"%[%s*([^=]+)=(%S+)%s")
	 t[v1]=v2
      else
	 if v1 then 
	    v2=string.match(k,"(%b{})")
	    if v2 then 
	       t[v1] = convert_formula_totable(v2,client)
	    else
	       v2=string.match(k,"[^=]+=%s*(%S+)%s*%]")
	       t[v1]= v2
	    end
	 end
      end
   end
   return(t)
end

function convert_formula_tostring(t)

   local s = ""
   
   if t["tag"] == "Atom" then
      s = t["1"]
   else
      s = "("..convert_formula_tostring(t["1"])..") "..t["tag"].." ("..convert_formula_tostring(t["2"])..")"      
   end

   return s
   
end
