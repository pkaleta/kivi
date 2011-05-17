module LambdaLifter where


import Utils
import Common
import Data.Set


type AnnExpr a b = (b, AnnExpr' a b)

data AnnExpr' a b = AVar Name
                  | ANum Int
                  | AConstr Int Int
                  | AAp (AnnExpr a b) (AnnExpr a b)
                  | ALet IsRec [AnnDefn a b] (AnnExpr a b)
                  | ACase (AnnExpr a b) [AnnAlt a b]
                  | ALam [a] (AnnExpr a b)

type AnnDefn a b = (a, AnnExpr a b)
type AnnAlt a b = (Int, [a], AnnExpr a b)
type AnnProgram a b = [(Name, [a], AnnExpr a b)]


lift :: CoreProgram -> CoreProgram
lift = collectSc . rename . abstract . freeVars


freeVars :: CoreProgram -> AnnProgram Name (Set Name)
freeVars [] = []
freeVars ((name, args, expr) : scs) = (name, args, calcFreeVars (fromList args) expr) : (freeVars scs)


calcFreeVars :: (Set Name) -> CoreExpr -> AnnExpr Name (Set Name)
calcFreeVars localVars (ENum n) = (empty, ANum n)
calcFreeVars localVars (EVar v) | member v localVars = (singleton v, AVar v)
calcFreeVars localVars (EAp e1 e2) = (union s1 s2, AAp ae1 ae2)
    where
        ae1@(s1, _) = calcFreeVars localVars e1
        ae2@(s2, _) = calcFreeVars localVars e2
calcFreeVars localVars (ELam args expr) = (difference fvs args, ALam args expr')
    where
        expr'@(fvs, _) = calcFreeVars (union localVars $ fromList args) expr
calcFreeVars localVars (ELet isRec defns expr) =
    (union bodyFvs defnsFvs, ALet isRec defns' expr')
    where
        binders = fromList $ bindersOf defns
        exprLvs = union binders localVars
        rhsLvs | isRec = exprLvs
               | otherwise = localVars
        -- annotated stuff
        rhss' = map (calcFreeVars rhsLvs) $ rhsOf defns
        defns' = zip binders rhss'
        expr' = calcFreeVars exprLvs
        rhssFvs = foldl union empty (map freeVarsOf rhss')
        defnsFvs | isRec = difference rhssFvs binders
                 | otherwise = rhssFvs
        bodyFvs = difference (freeVarsOf body') binders
calcFreeVars localVars (ECase expr alts) = error "Not implemented yet"
calcFreeVars localVars (EConstr t n) = error "Not implemented yet"


abstract :: AnnProgram Name (Set Name) -> CoreProgram
abstract program = [(name, args, abstractExpr expr) | (name, args, expr) <- program]


abstractExpr :: AnnExpr Name (Set Name) -> CoreExpr
abstractExpr (freeVars, ANum n) = ENum n
abstractExpr (freeVars, AVar v) = EVar v
abstractExpr (freeVars, AAp e1 e2) = EAp (abstractExpr e1) (abstractExpr e2)
abstractExpr (freeVars, ALet isRec defns expr) =
    ELet isRec [(name, abstractExpr body) | (name, body) <- defns] (abstractExpr expr)
abstractExpr (freeVars, ALam args expr) =
    foldl EAp sc $ map EVar freeVarsList
    where
        freeVarsList = toList freeVars
        sc = ELet False [("sc", )] (EVar "sc")
        scBody = ELam (freeVarsList ++ args) (abstractExpr expr)


rename :: CoreProgram -> CoreProgram


collectSc :: CoreProgram -> CoreProgram


freeVarsOf :: AnnExpr Name (Set Name) -> Set Name
freeVarsOf (fvs, _) = fvs
