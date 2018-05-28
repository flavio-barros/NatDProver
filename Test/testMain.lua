-------------------------------------------------------------------------------
-- testMain.lua
--
-- Este módulo executa os demais módulos de teste específicos, utilizando luaunit.
--
-- @author bpalkmim
-------------------------------------------------------------------------------

luaunit = require('luaunit')
require "testParsing"
require "testGraph"
require "testProofs"
require "logging"
require "logging.file"

lu = luaunit.LuaUnit.new()
lu:setOutputType("tap")

logger = logging.file("tests%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)
logger:info("\n\nTestes iniciados\n\n")

-- Executa a suíte de testes.
os.exit( lu:runSuite() )