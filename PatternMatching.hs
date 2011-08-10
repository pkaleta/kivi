module PatternMatching where


import List
import Common
import Utils
import Data.Map as Map
import ParserTypes
import Debug.Trace
import NameSupply as NS
import AbstractDataTypes
import LetTransformer
import CaseTransformer


data PatternClass = Num | Var | Constr

instance Eq PatternClass where
    Num == Num = True
    Var == Var = True
    Constr == Constr = True
    _ == _ = False


mergePatterns :: PatProgram -> PatProgram
mergePatterns (dts, scs) = (dts, scs')
    where
        scs' = [PatScDefn name defns | (name, defns) <- Map.toList $ foldl mergePattern Map.empty scs]


mergePattern :: Map Name [Equation] -> PatScDefn -> Map Name [Equation]
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


patternMatch :: PatProgram -> PatProgram
patternMatch (dts, scs) = (dts, scs')
    where
        scs' = [matchSc dts sc | sc <- scs]


matchSc :: [DataType] -> PatScDefn -> PatScDefn
matchSc dts (PatScDefn name eqs) = (PatScDefn name [(vars, expr')])
    where
        (ns2, expr') = matchEquations ns1 dts n varNames eqs def
        (patterns, expr) = head eqs
        n = length patterns
        (ns1, varNames) = getNames initialNameSupply ["_u" | i <- [1..n]]
        vars = [PVar v | v <- varNames]
        def = EError "No matching pattern found"


matchExpr :: NameSupply -> [DataType] -> Expr Pattern -> Expr Pattern -> (NameSupply, Expr Pattern)
matchExpr ns dts (ENum n) def = (ns, ENum n)
matchExpr ns dts (EVar v) def = (ns, EVar v)
matchExpr ns dts (EConstr t a) def = (ns, EConstr t a)
matchExpr ns dts (ESelect arity pos name) def = (ns, ESelect arity pos name)
matchExpr ns dts (EAp e1 e2) def = (ns2, EAp e1' e2')
    where
        (ns1, e1') = matchExpr ns dts e1 def
        (ns2, e2') = matchExpr ns1 dts e2 def
matchExpr ns dts (ELam patterns expr) def = (ns2, ELam (Prelude.map PVar names) expr')
    where
        (ns1, names) = getNames ns . replicate (length patterns) $ "_u"
        (ns2, expr') = matchEquations ns1 dts 1 names [(patterns, expr)] def
matchExpr ns dts (ELet isRec defns expr) def = (ns2, ELet isRec defns' expr')
    where
        (ns1, expr') = matchExpr ns dts expr def
        (ns2, defns') = mapAccumL collectDefns ns1 defns

        collectDefns ns (pattern, rhs) = (ns', (pattern, expr'))
            where (ns', expr') = matchExpr ns dts rhs def
matchExpr ns dts (ECase expr alts) def = (ns2, ECase expr' alts')
    where
        (ns1, expr') = matchExpr ns dts expr def
        (ns2, alts') = mapAccumL collectAlts ns1 alts

        collectAlts ns (pattern, rhs) = (ns', (pattern, expr'))
            where (ns', expr') = matchExpr ns dts rhs def


matchEquations :: NameSupply -> [DataType] -> Int -> [Name] -> [Equation] -> Expr Pattern -> (NameSupply, Expr Pattern)
matchEquations ns dts n [] eqs def =
    case eqs of
        ((pattern, expr) : eqs') -> matchExpr ns dts expr def
        _ -> (ns, def)
matchEquations ns dts n vs eqs def = foldr matchEquations' (ns, def) $ Utils.partition classifyEquation eqs
    where
        matchEquations' eqs (ns, def) = matchPatternClass ns dts n vs eqs def


matchPatternClass :: NameSupply -> [DataType] -> Int -> [Name] -> [Equation] -> Expr Pattern -> (NameSupply, Expr Pattern)
matchPatternClass ns dts n vars eqs def =
    case classifyEquation $ head eqs of
        Constr -> matchConstr ns dts n vars eqs def
        Var    -> matchVar ns dts n vars eqs def
        Num    -> matchNum ns dts n vars eqs def


matchVar :: NameSupply -> [DataType] -> Int -> [Name] -> [Equation] -> Expr Pattern -> (NameSupply, Expr Pattern)
matchVar ns dts n (var : vars) eqs def =
    matchEquations ns dts n vars [(ps, subst expr var name) | (PVar name : ps, expr) <- eqs] def


matchNum :: NameSupply -> [DataType] -> Int -> [Name] -> [Equation] -> Expr Pattern -> (NameSupply, Expr Pattern)
matchNum ns dts n vars@(v : vs) eqs def =
    (ns', ECase (EVar v) (alts ++ [(PDefault, def)]))
    where
        (ns', alts) = mapAccumL matchAlts ns eqs

        matchAlts ns (numPattern : ps, expr) = (ns', (numPattern, expr'))
            where (ns', expr') = matchEquations ns dts n vs [(ps, expr)] def


matchConstr :: NameSupply -> [DataType] -> Int -> [Name] -> [Equation] -> Expr Pattern -> (NameSupply, Expr Pattern)
matchConstr ns dts n vars@(v : vs) eqs def =
    (ns', ECase (EVar v) alts')
    where
        -- it's sufficient to take only the head of equations since all of the
        -- constructors in eqs will be constructors of the same type (assuming
        -- that program is typechecked)
        tags = constructors (getConstr $ head eqs) dts

        choose tag eqs = List.filter (isConstr tag) eqs
        isConstr t1 (PConstr t2 arity ps' : ps, expr) | t1 == t2 = True
        isConstr t _ = False

        (ns', alts') = mapAccumL matchAlts ns tags

        matchAlts ns tag = matchConstrAlter ns dts tag n vars (choose tag eqs) def


matchConstrAlter :: NameSupply
                 -> [DataType]
                 -> Int
                 -> Int
                 -> [Name]
                 -> [Equation]
                 -> Expr Pattern
                 -> (NameSupply, Alter Pattern Pattern)
matchConstrAlter ns dts tag n (v : vs) eqs def =
    (ns2, (PConstr tag n' $ List.map PVar vs', expr'))
    where
        n' = arity tag dts
        (ns1, vs') = getNames ns ["_u" | i <- [1..n']]
        eqs' = [(ps' ++ ps, expr) | ((PConstr tag arity ps' : ps), expr) <- eqs]

        (ns2, expr') = matchEquations ns1 dts (n' + n) (vs' ++ vs) eqs' def

