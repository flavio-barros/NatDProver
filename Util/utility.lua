-------------------------------------------------------------------------------
--   Utility Module
--
--   Contain functions that can be used by all the aplication. Normaly functions
--   for string manipulation or for debuging.
--   This is provided by the grafic module to all others that want to use this
--   functions.
--
--   @authors: Vitor, Hermann, Jefferson
--
-------------------------------------------------------------------------------

function os.capture()
   local f = assert(io.popen('uname', 'r'))
   local s = assert(f:read('*a'))
   f:close()
   s = string.gsub(s, '^%s+', '')
   s = string.gsub(s, '%s+$', '')
   s = string.gsub(s, '[\n\r]+', ' ')
   return s
end

function os.showProofOnBrowser(nameSufix)

   if nameSufix == nil then nameSufix = "" end
   
   --os.execute("pdflatex -output-directory=aux aux/prooftree.tex")
   
   os.execute("htlatex aux/prooftree"..nameSufix..".tex '' '' -daux/"  )
   
   if os.capture() == "Darwin" then
      os.execute("open aux/prooftree"..nameSufix..".html")                                        
   elseif os.capture() == "Linux" then
      os.execute("xdg-open aux/prooftree"..nameSufix..".html")
   else
      os.execute("start aux/prooftree"..nameSufix..".html")
   end

   os.execute("rm -f prooftree*")  
end
