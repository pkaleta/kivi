module CaseTransformer where


import Common
import Utils
import NameSupply


transformCase :: CoreProgram -> CoreProgram
transformCase (dts, scs) = (dts, scs')
    where
        scs' = [(name, args, transformExpr dts expr) | (name, args, expr) <- scs]


transformExpr :: [DataType] -> CoreExpr -> CoreExpr
transformExpr dts (EAp e1 e2) = EAp (transformExpr dts e1) (transformExpr dts e2)
transformExpr dts (ELam args expr) = ELam args $ transformExpr dts expr
transformExpr dts (ELet isRec defns expr) = ELet isRec defns' expr'
    where
        expr' = transformExpr dts expr
        defns' = [(var, transformExpr dts expr) | (var, expr) <- defns]
transformExpr dts (ECase expr alts) =
    case length alts == 1 of
        True -> transformCaseProduct initialNameSupply dts expr' alts
        False -> transformCaseSum initialNameSupply dts expr' alts
    where
        expr' = transformExpr dts expr
transformExpr dts expr = expr


transformCaseProduct :: NameSupply -> [DataType] -> CoreExpr -> [CoreAlt] -> CoreExpr
--TODO: tempporarily use transformCaseSum, fix later to own implementation
transformCaseProduct = transformCaseSum


transformCaseSum :: NameSupply -> [DataType] -> CoreExpr -> [CoreAlt] -> CoreExpr
transformCaseSum ns dts expr@(EVar name) alts = ECase expr alts'
    where
        alts' = map transform alts

        mkLet arity vars rhs = ELet False defns rhs'
            where
                defns = [(v, ESelect arity i name) | (v, i) <- zip vars [0..]]
                rhs' = transformExpr dts rhs

        transform (pattern@(PConstr tag arity vars), rhs) =
            case length vars == 0 of
                True -> (pattern, rhs)
                False -> (pattern, mkLet arity [v | (PVar v) <- vars] rhs)
        transform (pattern, rhs) = (pattern, rhs)
transformCaseSum ns dts expr alts = ELet False [(name, expr)] (transformCaseSum ns' dts (EVar name) alts)
    where
        (ns', name) = getName ns "v"
