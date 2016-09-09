-------------------------------------------------------------------------------
--   Sequent Graph Module
--
--   Extends Node and Edge modules. 
--   Here is defined the node estructure of the Sequent Graph
--
--   @authors: Vitor, Hermann, Jefferson
--
-------------------------------------------------------------------------------

require "Logic/ConstantsForSequent"
require 'Logic/Graph'

-- Contadores dos operadores
edgeCount = 0
andNodeCount = 0
notNodeCount = 0
orNodeCount  = 0
implyNodeCount = 0
sequentNodeCount = 0
esqNodeCount = 0
dirNodeCount = 0
bracketNodeCount = 0
focusNodeCount = 0

--- Defining the SequentNode, extends Node
SequentNode = {}

function SequentNode:new(labelNode)
   local typeNode = labelNode

   if labelNode == opSeq.graph then
      labelNode = labelNode .. sequentNodeCount		
      sequentNodeCount = sequentNodeCount + 1
   elseif labelNode == opNot.graph then
      labelNode = labelNode .. notNodeCount
      notNodeCount = notNodeCount + 1
   elseif labelNode == opOr.graph then
      labelNode = labelNode .. orNodeCount
      orNodeCount = orNodeCount + 1
   elseif labelNode == opAnd.graph then
      labelNode = labelNode .. andNodeCount
      andNodeCount = andNodeCount + 1
   elseif labelNode == opImp.graph then
      labelNode = labelNode .. implyNodeCount
      implyNodeCount = implyNodeCount + 1
   elseif labelNode == lblNodeEsq then
      labelNode = labelNode .. esqNodeCount
      esqNodeCount = esqNodeCount + 1
   elseif labelNode == lblNodeDir then		
      labelNode = labelNode .. dirNodeCount
      dirNodeCount = dirNodeCount + 1
   elseif labelNode == lblNodeBrackets then		
      labelNode = labelNode .. bracketNodeCount
      bracketNodeCount = bracketNodeCount + 1
   elseif labelNode == lblNodeFocus then		
      labelNode = labelNode .. focusNodeCount
      focusNodeCount = focusNodeCount + 1      
   end
   
   local newNode = Node:new(labelNode)

   newNode:setInformation("type", typeNode)
   newNode:setInformation("isExpanded", false)

   newNode:initEdgesIn()
   newNode:initEdgesOut()

   return newNode
end

function SequentNode:resetCounters()
   edgeCount = 0
   andNodeCount = 0
   notNodeCount = 0
   orNodeCount  = 0
   implyNodeCount = 0
   sequentNodeCount = 0
   esqNodeCount = 0
   dirNodeCount = 0
   bracketNodeCount = 0
   focusNodeCount = 0
end

SequentEdge = {}

--- If label is equals to "", then a number is created acording to the origin node edgeCount field.	
function SequentEdge:new(label, origem, destino)

   local edgeCount = nil
   
   if label ~= '' then
      return Edge:new(label, origem, destino)
   end
   
   local labelNodeOrigin = string.sub(origem:getLabel(), 2)		
   
   if tonumber(labelNodeOrigin) == nil then
      return Edge:new(label, origem, destino)
   end
   
   edgeCount = origem:getInformation("edgeCount")
   
   if edgeCount == nil then		
      origem:setInformation("edgeCount", 0)
      edgeCount = 0
   else
      edgeCount = edgeCount + 1
      origem:setInformation("edgeCount", edgeCount)
   end
   
   label = label .. edgeCount

   return Edge:new(label, origem, destino)
end




