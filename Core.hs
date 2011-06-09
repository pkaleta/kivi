module Core where


import Common
import Data.Map as Map


preludeDefs :: CoreProgram
preludeDefs = [("I", [([EVar "x"], (EVar "x"))]),
               ("K", [([EVar "x", EVar "y"], (EVar "x"))]),
               ("K1",[([EVar "x", EVar "y"], (EVar "y"))]),
               ("S", [([EVar "f", EVar "g", EVar "x"], (EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x"))))]),
               ("compose", [([EVar "f", EVar "g", EVar "x"], (EAp (EVar "f") (EAp (EVar "g") (EVar "x"))))]),
               ("twice", [([EVar "f"], (EAp (EAp (EVar "compose") (EVar "f")) (EVar "f")))]),
               ("if", [([EVar "cond", EVar "et", EVar "ef"], (ECase (EVar "cond") [(1, [], (EVar "ef")), (2, [], (EVar "et"))]))])]

