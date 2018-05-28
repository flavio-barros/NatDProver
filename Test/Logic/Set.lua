-------------------------------------------------------------------------------
--   This module defines the Set structure.
--
--   @author: Jefferson
-------------------------------------------------------------------------------


Set = {}
Set_Metatable = { __index = Set }

-- Cria um novo Set.
-- @param t Uma tabela com os elementos a serem inseridos.
-- @return O Set criado.
function Set:new (t)
   local ini = {}

   if t ~= nil then
      for _,v in pairs(t) do ini[v] = true end
   end

   return setmetatable( ini, Set_Metatable )
end

-- Indica se um elemento pertence a um Set.
-- @param e O elemento a ser verificado.
-- @return Um booleano que indica se e está no Set.
function Set:contains(e)
   return self[e]
end

-- Adicona um elemento a um Set.
-- @param e O elemento a ser adicionado.
function Set:add(e)
   self[e] = true
end

-- Une dois Sets.
-- @param set2 O Set a ser unido.
-- @return Um novo Set que representa a união de self com set2.
function Set:union(set2)
   local s = Set:new()

   for k, _ in pairs(self) do 
      s[k] = true
   end

   for k, _ in pairs(set2) do 
      s[k] = true
   end

   return s
end
