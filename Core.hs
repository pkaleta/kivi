module Core where

import Common

preludeDefs :: [CoreScDefn]
preludeDefs = [(ScDefn "I" ["x"] (EVar "x")),
               (ScDefn "K" ["x","y"] (EVar "x")),
               (ScDefn "K1" ["x","y"] (EVar "y")),
               (ScDefn "S" ["f","g","x"] (EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x")))),
               (ScDefn "compose" ["f","g","x"] (EAp (EVar "f") (EAp (EVar "g") (EVar "x")))),
               (ScDefn "twice" ["f"] (EAp (EAp (EVar "compose") (EVar "f")) (EVar "f")))
               --,(ScDefn "if" ["cond", "et", "ef"] (ECase (EVar "cond") [(1, [], (EVar "ef")), (2, [], (EVar "et"))]))
               ]

