Description
===========

NatDProver is a theorem prover for Propositional Minimal Logic. In current development it implements only the implication connective. 

Installation
============

NatDProver depends on the following libraries (listed with the versions I'm using):

* love (0.10,1)
* luasocket (3.0rc1-1)
* lpeg (0.12-1)
* lualogging (1.3.0-1)

Löve is a canvas for Lua game development that we use to build the prover user interface. It can be downloaded from [the project website](https://love2d.org/).

Luasocket is a library for socket communication in Lua. It can be installed using [luarocks](http://luarocks.org/), a package manager for Lua.

Lpeg is a pattern-matching library for Lua. We use lpeg to parse input formulae in our prover. It also can be installed using [luarocks](http://luarocks.org/).

Usage
=====

Inside NatDProver directory:

1. Run the prover graphical interface

`love .`

2. Follow commands in the graphical interface

Input formula example
=====================

Formulae only support implication (`imp`). Parentheses are required to the right side of every subformula. 

The formula A &rarr; (B &rarr; A) has to be entered as:

`A imp (B imp (A))`
