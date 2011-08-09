module CaseTransformer where


import Common
import Utils
import NameSupply
import ParserTypes


defaultTag :: Int
defaultTag = -1


transformCase :: [DataType] -> Expr Pattern -> Expr Pattern
transformCase dts (EAp e1 e2) = EAp (transformCase dts e1) (transformCase dts e2)
transformCase dts (ELam args expr) = ELam args $ transformCase dts expr
transformCase dts (ELet isRec defns expr) = ELet isRec defns' expr'
    where
        expr' = transformCase dts expr
        defns' = [(var, transformCase dts expr) | (var, expr) <- defns]
transformCase dts (ECase expr alts) =
    case length alts == 1 of
        True -> transformCaseProduct initialNameSupply dts expr' alts'
        False -> transformCaseSum initialNameSupply dts expr' alts'
    where
        alts' = [(pattern, transformCase dts rhs) | (pattern, rhs) <- alts]
        expr' = transformCase dts expr
transformCase dts expr = expr


transformCaseProduct :: NameSupply -> [DataType] -> Expr Pattern -> [Alter Pattern Pattern] -> Expr Pattern
--TODO: tempporarily use transformCaseSum, fix later to own implementation
transformCaseProduct = transformCaseSum


transformCaseSum :: NameSupply -> [DataType] -> Expr Pattern -> [Alter Pattern Pattern] -> Expr Pattern
transformCaseSum ns dts expr@(EVar name) alts =
    -- At this stage, there might be only two possible patterns occuring in
    -- case expressions, namely constructors and numbers. What is more they
    -- cannot exist in single case expression because earlier stage - type
    -- checking would prevent such situation.
    case head alts of
        (PNum n, body) -> transformCaseSimple ns dts expr alts
        (PConstr t a ps, body) -> transformCaseConstr ns dts expr alts
        (pattern, body) -> error $ "Unexpected pattern while transforming case expressions: " ++ show pattern
transformCaseSum ns dts expr alts = ELet False [(PVar name, expr)] (transformCaseSum ns' dts (EVar name) alts)
    where
        (ns', name) = getName ns "v"


transformCaseSimple :: NameSupply -> [DataType] -> Expr Pattern -> [Alter Pattern Pattern] -> Expr Pattern
transformCaseSimple ns dts expr@(EVar name) alts = ECaseSimple expr alts'
    where
        alts' = case foldl collectAlt (False, []) alts of
            (True, elems)  -> elems
            (False, elems) -> elems ++ [(defaultTag, defExpr)]

        collectAlt oldAcc@(found, acc) (pattern, expr) =
            case found of
                True -> oldAcc
                False -> case pattern of
                    (PNum n)   -> (False, acc ++ [(n, expr)])
                    _          -> (True, acc ++ [(defaultTag, expr)])

        defExpr = EError "No matching pattern found"


transformCaseConstr :: NameSupply -> [DataType] -> Expr Pattern -> [Alter Pattern Pattern] -> Expr Pattern
transformCaseConstr ns dts expr@(EVar name) alts = ECaseConstr expr alts'
    where
        alts' = map transform alts

        mkLet arity vars rhs = ELet False defns rhs
            where
                defns = [(v, ESelect arity i name) | (v, i) <- zip vars [0..]]

        transform (pattern@(PConstr tag arity vars), rhs) =
            case length vars == 0 of
                True -> (tag, rhs)
                False -> (tag, mkLet arity vars rhs)
        transform (pattern, rhs) = error $ "Unexpected pattern while transforming constructor case expressions: " ++ show pattern

