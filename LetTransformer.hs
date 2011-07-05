module LetTransformer where


import ParserTypes
import Common
import List
import NameSupply
import AbstractDataTypes


transformLet :: [DataType] -> Expr Pattern -> Expr Pattern
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


conformalityTransform :: [DataType] -> Expr Pattern -> Expr Pattern
conformalityTransform adts (ELet isRec defns expr) = ELet isRec defns' expr
    where
--        defns' = [case isRefutable pattern of
--            True -> conformalityTransformDefn adts defn
--            False -> defn
--            | defn@(pattern, expr) <- defns]
        (ns, defns') = mapAccumL (conformalityTransformDefn adts) initialNameSupply defns


conformalityTransformDefn :: [DataType] -> NameSupply -> Defn Pattern -> (NameSupply, Defn Pattern)
conformalityTransformDefn adts ns defn@(pattern, expr) =
        case isRefutable pattern of
            True -> (ns', (pattern', expr'))
                where
                    pattern' = getTuplePattern adts pattern
                    expr' = ELet False [(PVar varName, expr)] body
                    body = EAp (ELam [pattern] $ getTupleConstr adts pattern) (EVar varName)
                    (ns', varName) = getName ns "v"
            False -> (ns, defn)


getTupleConstr :: [DataType] -> Pattern -> Expr Pattern
getTupleConstr adts pattern = foldl EAp (EConstr tag arity) exprs
    where
        name = "Tuple" ++ show arity
        tag = tagFromName name adts
        arity = length exprs

        exprs = [EVar v | v <- getPatternVarNames pattern]


getTuplePattern :: [DataType] -> Pattern -> Pattern
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


createLet :: [DataType] -> (Pattern, Expr Pattern) -> (NameSupply, Expr Pattern) -> (NameSupply, Expr Pattern)
createLet adts (pattern@(PVar v), rhs) (ns, expr) = (ns, ELet False [(pattern, rhs)] expr)
createLet adts (pattern@(PConstr tag arity args), rhs) (ns, expr) =
    (ns2, ELet False defns' expr')
    where
        (ns1, var1) = getName ns "v"

        defns' = [(PVar var1, rhs)]
        (ns2, expr') = foldr mkLet (ns1, expr) $ [vars] ++ [[constr] | constr <- constrs]

        mkLet patterns (ns, letExpr) =
            case head patterns of
                -- there should not be the case for num because when num is in
                -- pattern it means that pattern is refutable
                (PVar v, pos) ->
                    (ns, ELet False [(PVar v, ESelect arity pos var1) | (PVar v, pos) <- patterns] letExpr)
                (PConstr t a ps, pos) ->
                    (ns2, ELet False [(PVar varName, ESelect arity pos var1)] body)
                    where
                        (ns1, varName) = getName ns "v"
                        (ns2, body) = foldr (createLet adts) (ns1, letExpr) [(pattern, ESelect a i varName) | (pattern, i) <- zip ps [0..]]

        (vars, constrs) = partition isVar $ zip args [0..]

        isVar ((PVar v), pos) = True
        isVar _               = False


createLetrec :: [DataType] -> (NameSupply, [(Pattern, Expr Pattern)]) -> (Pattern, Expr Pattern) -> (NameSupply, [(Pattern, Expr Pattern)])
createLetrec adts (ns, defns) (pattern@(PVar v), rhs) = (ns, (pattern, rhs) : defns)
createLetrec adts (ns, defns) (pattern@(PConstr tag arity args), rhs) =
    (ns2, defns ++ [(PVar varName, rhs)] ++ innerDefns)
    where
        (ns2, innerDefns) = foldl (collectDefs varName arity) (ns1, []) $ zip args [0..]
        (ns1, varName) = getName ns "v"

collectDefs :: Name -> Int -> (NameSupply, [Defn Pattern]) -> (Pattern, Int) -> (NameSupply, [Defn Pattern])
collectDefs name arity (ns, acc) ((PVar v), i) = (ns, acc ++ [(PVar v, ESelect arity i name)])
collectDefs name arity (ns, acc) ((PConstr t a as), i) =
    foldl (collectDefs name' a) (ns', (acc ++ [(PVar name', ESelect arity i name)])) (zip as [0..])
    where
        (ns', name') = getName ns "v"


irrefutableToSimple :: [DataType] -> Expr Pattern -> Expr Pattern
irrefutableToSimple adts (ELet False defns expr) = letExpr
    where
        (ns, letExpr) = foldr (createLet adts) (initialNameSupply, expr) defns
irrefutableToSimple adts (ELet True defns expr) = ELet True defns' expr
    where
        (ns, defns') = foldl (createLetrec adts) (initialNameSupply, []) defns
irrefutableToSimple adts expr =
    error $ "Trying to apply transformation for irrefutable let(rec)s into simple let(rec)s for: " ++ show expr

