module TypeChecker where


import Common
import Data.Map as Map


type TVarName = String
data TExpr = TVar TVarName | TOp String [TExpr]


arrow :: TExpr -> TExpr -> TExpr
arrow t1 t2 = TOp "arrow" [t1, t2]


int :: TExpr
int = TOp "int" []


cross :: TExpr -> TExpr -> TExpr
cross t1 t2 = TOp "cross" [t1, t2]


list :: TExpr -> TExpr
list t = TOp "list" [t]


tVarNames :: TExpr -> [TVarName]
tVarNames (TVar name) = [name]
tVarNames (TOp op tVars) = foldl collect [] tVars
    where
        collect acc tVar = acc ++ tVarNames tVar

