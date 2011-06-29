module PatternMatching where


import List
import Common
import Utils
import Data.Map as Map
import ParserTypes
import Debug.Trace
import NameSupply as NS
import AbstractDataTypes


data PatternClass = Num | Var | Constr

instance Eq PatternClass where
    Num == Num = True
    Var == Var = True
    Constr == Constr = True
    _ == _ = False


mergePatterns :: PatTypeScPair -> PatTypeScPair
mergePatterns (dts, scs) = (dts, scs')
    where
        scs' = [PatScDefn name defns | (name, defns) <- Map.toList $ foldl mergePattern Map.empty scs]


mergePattern :: Map Name [Equation] -> PatProgramElement -> Map Name [Equation]
mergePattern scMap (PatScDefn name defns) = -- it would always contain only one definition
    Map.alter update name scMap
    where
        update Nothing = Just defns
        update (Just oldDefns) = Just (oldDefns ++ defns)


subst :: Expr Pattern -> Name -> Name -> Expr Pattern
subst (ENum n) new old = ENum n
subst (EVar v) new old | v == old  = EVar new
                       | otherwise = EVar v
subst (EConstr tag arity) new old = EConstr tag arity
subst (EAp e1 e2) new old = EAp (subst e1 new old) (subst e2 new old)
subst (ELam pattern expr) new old = ELam pattern $ subst expr new old
subst (ELet isRec defns expr) new old = ELet isRec defns' expr'
    where
        defns' = [(patExpr, subst rhs new old) | (patExpr, rhs) <- defns]
        expr' = subst expr new old
subst (ECase expr alts) new old = ECase expr' alts'
    where
        expr' = subst expr new old
        alts' = [(pattern, subst rhs new old) | (pattern, rhs) <- alts]


classifyEquation :: Equation -> PatternClass
classifyEquation (PVar name : ps, expr) = Var
classifyEquation (PConstr tag arity ps' : ps, expr) = Constr
classifyEquation (PNum n : ps, expr) = Num


isConstr :: Equation -> Bool
isConstr (PConstr tag arity pattern : ps, expr) = True
isConstr _                                      = False


getConstr :: Equation -> Int
getConstr ((PConstr tag arity ps') : ps, expr) = tag
getConstr x = error $ show x


patternMatch :: PatTypeScPair -> CoreProgram
patternMatch (dts, scs) = (dts', scs')
    where
        scs' = List.map (matchSc dts) scs
        dts' = [(DataType name cs) | (PatDataType name cs) <- dts]

matchSc :: [PatProgramElement] -> PatProgramElement -> ProgramElement Name
matchSc dts (PatScDefn name eqs) = ScDefn name vars $ matchEquations ns' dts n vars eqs def
    where
        (patterns, expr) = head eqs
        n = length patterns
        (ns', vars) = getNames initialNameSupply ["_u" | i <- [1..n]]
        def = EError "No matching pattern found"


matchExpr :: [PatProgramElement] -> Expr Pattern -> CoreExpr -> CoreExpr
matchExpr dts (ENum n) def = ENum n
matchExpr dts (EVar v) def = EVar v
matchExpr dts (EConstr t a) def = EConstr t a
matchExpr dts (ESelect arity pos name) def = ESelect arity pos name
matchExpr dts (EAp e1 e2) def = EAp (matchExpr dts e1 def) (matchExpr dts e2 def)
matchExpr dts (ELam pattern expr) def = ELam args' expr'
    where
        (ns', name) = getName initialNameSupply "_u"
        args' = [name]
        expr' = matchEquations ns' dts 1 args' [(pattern, expr)] def
matchExpr dts (ELet isRec defns expr) def = ELet isRec defns' expr'
    where
        expr' = matchExpr dts expr def
        defns' = [(v, matchExpr dts rhs def) | (PVar v, rhs) <- defns]
matchExpr dts (ECase expr alts) def = ECase expr' alts'
    where
        expr' = matchExpr dts expr def
        alts' = [(pattern, matchExpr dts rhs def) | (pattern, rhs) <- alts] ++ [(PDefault, def)]


matchEquations :: NameSupply -> [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchEquations ns dts n [] eqs def =
    case eqs of
        ((pattern, expr) : eqs') -> matchExpr dts expr def
        _ -> def
matchEquations ns dts n vs eqs def = foldr (matchPatternClass ns dts n vs) def $ Utils.partition classifyEquation eqs


matchPatternClass :: NameSupply -> [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchPatternClass ns dts n vars eqs def =
    case classifyEquation $ head eqs of
        Constr -> matchConstr ns dts n vars eqs def
        Var    -> matchVar ns dts n vars eqs def
        Num    -> matchNum ns dts n vars eqs def


matchVar :: NameSupply -> [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchVar ns dts n (var : vars) eqs def =
    matchEquations ns dts n vars [(ps, subst expr var name) | (PVar name : ps, expr) <- eqs] def


matchNum :: NameSupply -> [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchNum ns dts n vars@(v : vs) eqs def =
    ECase (EVar v) $ [(numPattern, matchEquations ns dts n vs [(ps, expr)] def) | (numPattern : ps, expr) <- eqs] ++ [(PDefault, def)]


matchConstr :: NameSupply -> [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchConstr ns dts n vars@(v : vs) eqs def =
    ECase (EVar v) [matchConstrAlter ns dts tag n vars (choose tag eqs) def | tag <- tags]
    where
        -- it's sufficient to take only the head of equations since all of the
        -- constructors in eqs will be constructors of the same type (assuming
        -- that program is typechecked)
        tags = constructors (getConstr $ head eqs) dts

        choose tag eqs = List.filter (isConstr tag) eqs
        isConstr t1 (PConstr t2 arity ps' : ps, expr) | t1 == t2 = True
        isConstr t _ = False


matchConstrAlter :: NameSupply -> [PatProgramElement] -> Int -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreAlt
matchConstrAlter ns dts tag n (v : vs) eqs def =
    (PConstr tag n' $ List.map PVar vs', matchEquations ns' dts (n' + n) (vs' ++ vs) eqs' def)
    where
        n' = arity tag dts
        (ns', vs') = getNames ns ["_u" | i <- [1..n']]
        eqs' = [(ps' ++ ps, expr) | ((PConstr tag arity ps' : ps), expr) <- eqs]

