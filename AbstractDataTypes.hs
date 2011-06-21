module AbstractDataTypes where


import Common


data AExpr = AConstr Name Int


primitiveADTs :: [ProgramElement Name]
primitiveADTs = [(DataType "Bool" [("True", 0, 0), ("False", 1, 0)]),
                 (DataType "List" [("Nil", 2, 0), ("Cons", 3, 2)])]


initialTag :: Int
initialTag = 4


undefinedTag :: Int
undefinedTag = -1

