module LambdaCalculusTransformer where


import Common
import LetTransformer
import CaseTransformer
import PatternMatching
import ParserTypes
import NameSupply



transformToLambdaCalculus :: PatTypeScPair -> CoreProgram
transformToLambdaCalculus = transform . (traverse transformCase) . patternMatch . (traverse transformLet)


-- generic program traversal function
traverse :: ([PatProgramElement] -> Expr Pattern -> Expr Pattern)
         -> ([PatProgramElement], [PatProgramElement])
         -> ([PatProgramElement], [PatProgramElement])
traverse transformFunction (adts, scs) = (adts, scs')
    where
        scs' = [(PatScDefn name $ traverseEqs (transformFunction adts) eqs) | (PatScDefn name eqs) <- scs]


traverseEqs :: (Expr Pattern -> Expr Pattern) -> [Equation] -> [Equation]
traverseEqs transformFunction eqs = [traverseEq transformFunction eq | eq <- eqs]


traverseEq :: (Expr Pattern -> Expr Pattern) -> Equation -> Equation
traverseEq transformFunction (patterns, expr) = (patterns, transformFunction expr)


transformPattern :: Pattern -> String
transformPattern (PVar v) = v
transformPattern pattern  = error $ "Unexpected pattern found when transforming into lambda calculus: " ++ show pattern


transform :: PatTypeScPair -> CoreProgram
transform (adts, scs) = (adts', [transformSc sc | sc <- scs])
    where
        adts' = [DataType name cs | (PatDataType name cs) <- adts]


transformSc :: PatProgramElement -> ProgramElement Name
transformSc (PatScDefn name [(patterns, expr)]) =
    ScDefn name [transformPattern pattern | pattern <- patterns] $ transformExpr expr


transformExpr :: Expr Pattern -> CoreExpr
transformExpr (ENum n) = ENum n
transformExpr (EVar v) = EVar v
transformExpr (EConstr t a) = EConstr t a
transformExpr (EAp e1 e2) = EAp (transformExpr e1) (transformExpr e2)
transformExpr (ELam patterns expr) = ELam patterns' expr'
    where
        patterns' = [transformPattern pattern | pattern <- patterns]
        expr' = transformExpr expr
transformExpr (ELet isRec defns expr) = ELet isRec defns' expr'
    where
        expr' = transformExpr expr
        defns' = [(transformPattern pattern, transformExpr rhs) | (pattern, rhs) <- defns]
transformExpr (ECaseSimple expr alts) = ECaseSimple expr' alts'
    where
        expr' = transformExpr expr
        alts' = [(n, transformExpr expr) | (n, expr) <- alts]
transformExpr (ECaseConstr expr alts) = ECaseSimple expr' alts'
    where
        expr' = transformExpr expr
        alts' = [(n, transformExpr expr) | (n, expr) <- alts]
transformExpr (ESelect r i v) = ESelect r i v

