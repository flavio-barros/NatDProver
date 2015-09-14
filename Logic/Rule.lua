-------------------------------------------------------------------------------
--   This module defines a Rule.
--
--   @author: Jefferson
-------------------------------------------------------------------------------
require "SequentGraph.lua"


Rule = {name = ""}

-------------------------------------------------------------------------------
-- Rule constructor

function Rule:new (o)
   o = o or {}
   setmetatable(o, self)
   self.__index = self 
   return o
end

function Rule:setSequent(seq)
   self.sequent = seq
end

function Rule:setFormula(form)
   self.formula = form
end




ImpLeft = Rule:new {name = "-->-Left"}

function ImpLeft:apply()
   print(self.name)
   print(self.sequent)
   print(self.formula)
end

