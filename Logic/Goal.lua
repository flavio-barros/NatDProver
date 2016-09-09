------------------------------------------------------------------------------
-- Goal Module
--
-- This module defines a Goal for an ATP utilizing primarily Natural Deduction.
--
-- @authors: Vitor, Bernardo
--
-------------------------------------------------------------------------------

--- Defining the Goal
Goal = {}

--- Defining the Metatable
Goal_Metatable = { __index = Goal }


--- Class Constructor
-- @param goalsList - Lista de goals para adição ao goal intermediário atual que está sendo criado.
function Goal:new (goalsList)
    local ini = {}

    if goalsList ~= nil then
        assert( type(goalsList) == "table", "Goal:new expects a table. goalsList is not a table")
        ini = {goalsList = goalsList}
    end

    return setmetatable( ini, Goal_Metatable )
end

function Goal:deleteGoal()
    self.goalsList = nil
    self = nil
end

--- Return the list of goals
function Goal:getGoalsList()
    return self.goalsList
end