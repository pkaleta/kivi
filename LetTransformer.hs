module LetTransformer where


import ParserTypes
import Common
import List
import NameSupply
import AbstractDataTypes



transformLet :: [PatProgramElement] -> Expr Pattern -> Expr Pattern
transformLet adts (EAp e1 e2) = EAp (transformLet adts e1) (transformLet adts e2)
transformLet adts (ELam args expr) = ELam args $ transformLet adts expr
transformLet adts (ECase expr alts) = ECase expr' alts'
    where
        expr' = transformLet adts expr
        alts' = [(pattern, transformLet adts expr) | (pattern, expr) <- alts]
transformLet adts (ELet isRec defns expr) =
    (irrefutableToSimple adts) . (conformalityTransform adts) $ ELet isRec defns' expr'
    where
        expr' = transformLet adts expr
        defns' = [(pattern, transformLet adts rhs) | (pattern, rhs) <- defns]
transformLet adts expr = expr


isRefutable :: Pattern -> Bool
isRefutable (PVar v) = False
isRefutable (PConstr tag arity args) =
    foldl (||) False [isRefutable arg | arg <- args]
isRefutable other = True


conformalityTransform :: [PatProgramElement] -> Expr Pattern -> Expr Pattern
conformalityTransform adts (ELet isRec defns expr) = ELet isRec defns' expr
    where
        defns' = [case isRefutable pattern of
            True -> conformalityTransformDefn adts defn
            False -> defn
            | defn@(pattern, expr) <- defns]


conformalityTransformDefn :: [PatProgramElement] -> Defn Pattern -> Defn Pattern
conformalityTransformDefn adts (pattern, expr) = (pattern', expr')
    where
        pattern' = getTuplePattern adts pattern
        expr' = ELet False [(PVar "v", expr)] body
        body = EAp (ELam [pattern] $ getTupleConstr adts pattern) (EVar "v")


getTupleConstr :: [PatProgramElement] -> Pattern -> Expr Pattern
getTupleConstr adts pattern = foldl EAp (EConstr tag arity) exprs
    where
        name = "Tuple" ++ show arity
        tag = tagFromName name adts
        arity = length exprs

        exprs = [EVar v | v <- getPatternVarNames pattern]


getTuplePattern :: [PatProgramElement] -> Pattern -> Pattern
getTuplePattern adts pattern = (PConstr tag arity patterns)
    where
        name = "Tuple" ++ show arity
        tag = tagFromName name adts
        arity = length patterns

        patterns = [PVar v | v <- getPatternVarNames pattern]


getPatternVarNames :: Pattern -> [Name]
getPatternVarNames (PNum n) = []
getPatternVarNames (PVar v) = [v]
getPatternVarNames (PConstr tag arity patterns) = foldl collectVars [] patterns
    where
        collectVars vars pattern = vars ++ getPatternVarNames pattern


createLet :: [PatProgramElement] -> (Pattern, Expr Pattern) -> Expr Pattern -> Expr Pattern
createLet adts (pattern@(PVar v), rhs) expr = ELet False [(pattern, rhs)] expr
createLet adts (pattern@(PConstr tag arity args), rhs) expr =
    ELet False [(PVar "v", rhs)] $ foldr mkLet expr $ [vars] ++ [[constr] | constr <- constrs]
    where
        mkLet patterns letExpr =
            case head patterns of
                -- there should not be the case for num because when num is in
                -- pattern it means that pattern is refutable
                (PVar v, pos) ->
                    ELet False [(PVar v, ESelect arity pos "v") | (PVar v, pos) <- patterns] letExpr
                (PConstr t a ps, pos) ->
                    ELet False [(PVar "w", ESelect arity pos "v")] body
                    where
                        body = foldr (createLet adts) letExpr [(pattern, ESelect a i "w") | (pattern, i) <- zip ps [0..]]

        (vars, constrs) = partition isVar $ zip args [0..]

        isVar ((PVar v), pos) = True
        isVar _               = False


createLetrec :: [PatProgramElement] -> NameSupply -> [(Pattern, Expr Pattern)] -> (Pattern, Expr Pattern) -> [(Pattern, Expr Pattern)]
createLetrec adts ns defns (pattern@(PVar v), rhs) = (pattern, rhs) : defns
createLetrec adts ns defns (pattern@(PConstr tag arity args), rhs) =
    defns ++ [(PVar varName, rhs)] ++ (foldl (collectDefs ns' varName arity) [] $ zip args [0..])
    where
        (ns', varName) = getName ns "v"

collectDefs :: NameSupply -> Name -> Int -> [Defn Pattern] -> (Pattern, Int) -> [Defn Pattern]
collectDefs ns name arity acc ((PVar v), i) = acc ++ [(PVar v, ESelect arity i name)]
collectDefs ns name arity acc ((PConstr t a as), i) =
    foldl (collectDefs ns' name' a) (acc ++ [(PVar name', ESelect arity i name)]) (zip as [0..])
    where
        (ns', name') = getName ns "v"


irrefutableToSimple :: [PatProgramElement] -> Expr Pattern -> Expr Pattern
irrefutableToSimple adts (ELet False defns expr) = foldr (createLet adts) expr defns
irrefutableToSimple adts (ELet True defns expr) = ELet True defns' expr
    where
        defns' = foldl (createLetrec adts initialNameSupply) [] defns
irrefutableToSimple adts expr =
    error $ "Trying to apply transformation for irrefutable let(rec)s into simple let(rec)s for: " ++ show expr

