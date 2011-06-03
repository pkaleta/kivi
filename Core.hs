module Core where


import Common
import Data.Map as Map


preludeDefs :: CoreProgram
preludeDefs = [("I", [(["x"], (EVar "x"))]),
               ("K", [(["x","y"], (EVar "x"))]),
               ("K1",[(["x","y"], (EVar "y"))]),
               ("S", [(["f","g","x"], (EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x"))))]),
               ("compose", [(["f","g","x"], (EAp (EVar "f") (EAp (EVar "g") (EVar "x"))))]),
               ("twice", [(["f"], (EAp (EAp (EVar "compose") (EVar "f")) (EVar "f")))]),
               ("if", [(["cond", "et", "ef"], (ECase (EVar "cond") [(1, [], (EVar "ef")), (2, [], (EVar "et"))]))])]

