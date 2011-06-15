module Core where

import Common

preludeDefs :: CoreProgram
preludeDefs = [("I", [([Var "x"], EVar "x")]),
               ("K", [([Var "x", Var "y"], EVar "x")]),
               ("K1",[([Var "x", Var"y"], EVar "y")]),
               ("S", [([Var "f", Var "g", Var "x"], EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x")))]),
               ("compose", [([Var "f", Var "g", Var "x"], EAp (EVar "f") (EAp (EVar "g") (EVar "x")))]),
               ("twice", [([Var "f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))])
               -- TODO: fix
               -- ,("if", [([Var "cond", Var "et", Var "ef"], ECase (EVar "cond") [([Constr 1 1 []], EVar "ef"), ([Constr 1 2 []], EVar "et")]            )])
                ]

