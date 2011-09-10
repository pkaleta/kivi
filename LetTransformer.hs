module LetTransformer where


import ParserTypes
import Common
import List
import NameSupply
import AbstractDataTypes
import Debug.Trace


transformLet :: [DataType] -> Expr Pattern -> Expr Pattern
transformLet adts expr = expr'
    where
        (ns', expr') = transformLet' initialNameSupply adts expr


transformLet' :: NameSupply -> [DataType] -> Expr Pattern -> (NameSupply, Expr Pattern)
transformLet' ns adts (EAp e1 e2) = (ns2, EAp e1' e2')
    where
        (ns1, e1') = transformLet' ns adts e1
        (ns2, e2') = transformLet' ns1 adts e2
transformLet' ns adts (ELam args expr) = (ns', ELam args expr')
    where
        (ns', expr') = transformLet' ns adts expr
transformLet' ns adts (ECase expr alts) = (ns2, ECase expr' alts')
    where
        (ns1, expr') = transformLet' ns adts expr
        (ns2, alts') = mapAccumL collectCase ns1 alts

        collectCase ns (pattern, expr) = (ns', (pattern, expr'))
            where
                (ns', expr') = transformLet' ns adts expr
transformLet' ns adts (ELet isRec defns expr) =
    (irrefutableToSimple adts) . (conformalityTransform adts) $ (ns2, ELet isRec defns' expr')
    where
        (ns1, expr') = transformLet' ns adts expr
        (ns2, defns') = mapAccumL collectLet ns1 defns

        collectLet ns (pattern, expr) = (ns, (pattern, expr))
            where
                (ns', expr') = transformLet' ns adts expr
transformLet' ns adts expr = (ns, expr)


isRefutable :: [DataType] -> Pattern -> Bool
isRefutable adts (PVar v) = False
isRefutable adts (PConstr tag arity args) =
    ((length $ constructors tag adts) > 1) || (or [isRefutable adts arg | arg <- args])
isRefutable adts other = True


conformalityTransform :: [DataType] -> (NameSupply, Expr Pattern) -> (NameSupply, Expr Pattern)
conformalityTransform adts (ns, ELet isRec defns expr) = (ns', ELet isRec defns' expr)
    where
        (ns', defns') = mapAccumL (conformalityTransformDefn adts) ns defns


conformalityTransformDefn :: [DataType] -> NameSupply -> Defn Pattern -> (NameSupply, Defn Pattern)
conformalityTransformDefn adts ns defn@(pattern, expr) =
        case isRefutable adts pattern of
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
getPatternVarNames (PChar c) = []
getPatternVarNames (PVar v) = [v]
getPatternVarNames (PConstr tag arity patterns) = foldl collectVars [] patterns
    where
        collectVars vars pattern = vars ++ getPatternVarNames pattern


createLet :: [DataType] -> (Pattern, Expr Pattern) -> (NameSupply, Expr Pattern) -> (NameSupply, Expr Pattern)
createLet adts (pattern@(PConstr tag arity args), rhs) (ns, expr) = (ns1, ELet False defns' expr')
    where
        (ns1, var1) = getName ns "v"

        defns' = [(PVar var1, rhs)]
        (ns2, expr') = foldr mkLet (ns1, expr) $ [vars] ++ [[constr] | constr <- constrs]

        mkLet [] acc = acc
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
                        (ns2, body) = foldr (createLet adts) (ns1, letExpr) defns'
                        defns' = [(pattern, ESelect a i varName) | (pattern, i) <- zip ps [0..]]

        (vars, constrs) = partition isVar $ zip args [0..]

        isVar ((PVar v), pos) = True
        isVar _               = False
createLet adts (pattern, rhs) (ns, expr) = (ns, ELet False [(pattern, rhs)] expr)


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


irrefutableToSimple :: [DataType] -> (NameSupply, Expr Pattern) -> (NameSupply, Expr Pattern)
irrefutableToSimple adts (ns, ELet False defns expr) = foldr (createLet adts) (ns, expr) defns
irrefutableToSimple adts (ns, ELet True defns expr) = (ns', ELet True defns' expr)
    where
        (ns', defns') = foldl (createLetrec adts) (ns, []) defns
irrefutableToSimple adts (ns, expr) =
    error $ "Trying to apply transformation for irrefutable let(rec)s into simple let(rec)s for: " ++ show expr

