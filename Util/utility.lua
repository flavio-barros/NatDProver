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

-- Captura entrada da io padrão.
function os.capture()
    local f = assert(io.popen('uname', 'r'))
    local s = assert(f:read('*a'))
    f:close()
    s = string.gsub(s, '^%s+', '')
    s = string.gsub(s, '%s+$', '')
    s = string.gsub(s, '[\n\r]+', ' ')
    return s
end

-- Mostra no web browser a representação do grafo em LaTeX.
-- @param nameSuffix string contendo o identificador de uma prova em específico
function os.showProofOnBrowser(nameSuffix)

    if nameSuffix == nil then nameSuffix = "" end

    os.execute("pdflatex -output-directory=aux aux/prooftree.tex")

    os.execute("htlatex aux/prooftree"..nameSuffix..".tex '' '' -daux/")

    if os.capture() == "Darwin" then
        os.execute("open aux/prooftree"..nameSuffix..".html")
    elseif os.capture() == "Linux" then
        os.execute("xdg-open aux/prooftree"..nameSuffix..".html")
    else
        os.execute("start aux/prooftree"..nameSuffix..".html")
    end

    os.execute("rm -f prooftree*")
end

-- Mostra no web browser a representação do grafo da prova em DOT (ainda em fase de testes).
-- @param nameSuffix string contendo o identificador de uma prova em específico
function os.showProofDotOnBrowser(nameSuffix)

    if nameSuffix == nil then nameSuffix = "" end

    os.execute("dot -Tpng aux/prooftreeDot"..nameSuffix..".dot -o aux/prooftreeDot"..nameSuffix..".png")

end

function format_dot_files()
    
end
