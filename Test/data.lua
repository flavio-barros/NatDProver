local fib2 = "(A1 imp (A2))"
local fib3 = fib2.." imp (((A1 imp (A2 imp (A3))))"
local fib4 = fib3.." imp (((A2 imp (A3 imp (A4))))"
local fib5 = fib4.." imp (((A3 imp (A4 imp (A5))))"
local fib6 = fib5.." imp (((A4 imp (A5 imp (A6))))"
local fib7 = fib6.." imp (((A5 imp (A6 imp (A7))))"

Formula{"Fibonacci3", fib3.." imp (A1 imp (A3)))"}
--Formula{"Fibonacci5", fib5.." imp (A1 imp (A5)))))"}
--Formula{"Fibonacci6", fib6.." imp (A1 imp (A6))))))"}
Formula{"Fibonacci7", fib7.." imp (A1 imp (A7)))))))"}

--Formula{"Valid1", "(A imp (B)) imp ((B imp (C)) imp (B imp (D imp (C))))"}
--Formula{"Valid2", "(B imp ((C imp (A)))) imp ((A imp (B)) imp ((A imp (C)) imp ((A imp (C)))))"}
--Formula{"Valid3", "(q imp (p imp (p))) imp (p imp (q imp (p)))"}
--Formula{"Valid4", "(A imp (B imp (C))) imp (B imp (A imp (C)))"}
--Formula{"Valid5", "(q imp (p)) imp (q imp (p))"}
--Formula{"Valid6", "A imp ((A imp (t)) imp ((t imp (r)) imp ((r imp (p)) imp (p))))"}

-- Chi Formulas:
local chi1 = "B"
local chi2 = "(((C imp ("..chi1..")) imp (C)) imp (C)) imp ("..chi1..")"
local chi3 = "(((D imp ("..chi2..")) imp (D)) imp (D)) imp ("..chi2..")"

local alpha1 = "((((A imp ("..chi1..")) imp (A)) imp (A)) imp ("..chi1..")) imp (B)"
Formula{"HermannTest", alpha1}

local alpha2 = "((((A imp ("..chi2..")) imp (A)) imp (A)) imp ("..chi2..")) imp (B)"
--Formula{"Valid-chi1", alpha2}
local alpha3 = "((((A imp ("..chi3..")) imp (A)) imp (A)) imp ("..chi3..")) imp (B)"
--Formula{"Valid-chi2", alpha3}

--Formula{"Lets see", "((((A imp (B)) imp (B)) imp (A)) imp (A))"}

--Formula{"Invalid1-peirce", "(((A imp (B)) imp (B)) imp (A))"}
--Formula{"Invalid2-dummet", "((p imp (q)) imp (r)) imp ((((q imp (p)) imp (r))) imp (r))"}
--Formula{"Invalid3", "(A imp (B)) imp (B imp (A))"}
--Formula{"Invalid4", "A imp ((A imp (t)) imp (((t imp (r)) imp (q imp (r))) imp ((r imp (q)) imp (p))))"}
