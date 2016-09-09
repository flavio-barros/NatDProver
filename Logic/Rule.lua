-------------------------------------------------------------------------------
--	This module defines a Rule.
--
--	@author: Jefferson, Bernardo
-------------------------------------------------------------------------------
require "NatDGraph.lua"


Rule = {name = ""}

-------------------------------------------------------------------------------
-- Rule constructor

function Rule:new (o)
	o = o or {}
	setmetatable(o, self)
	self.__index = self 
	return o
end

function Rule:setFormula(form)
	self.formula = form
end



ImpIntro = Rule:new {name = "-->-Intro"}
ImpElim = Rule:new {name = "-->-Elim"}

function ImpLeft:apply()
	print(self.name)
	print(self.formula)
end

