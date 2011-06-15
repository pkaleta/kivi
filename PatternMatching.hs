module PatternMatching where


import List
import Common
import Utils
import Data.Map as Map
import Parser
import Debug.Trace


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


--TODO: implement
arity :: Int -> [PatProgramElement] -> Int
arity tag (PatDataType name cs : types) =
    case findConstr tag cs of
        Nothing -> arity tag types
        Just (t, a) -> a
arity tag [] = error $ "Could not find constructor with tag: " ++ show tag


--TODO: implement
constructors :: Int -> [PatProgramElement] -> [Int]
constructors tag (PatDataType name cs : types) =
    case findConstr tag cs of
        Nothing -> constructors tag types
        Just (t, a) -> [t | (t, a) <- cs]
constructors tag [] = error $ "Could not find constructor with tag: " ++ show tag


findConstr :: Int -> [Constr] -> Maybe Constr
findConstr tag ((t, a) : cs) | tag == t = Just (t, a)
                             | otherwise = findConstr tag cs
findConstr tag [] = Nothing


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


isVar :: Equation -> Bool
isVar (PVar name : ps, expr) = True
isVar _ = False


isConstr :: Equation -> Bool
isConstr eq = not $ isVar eq


getConstr :: Equation -> Int
getConstr ((PConstr tag arity ps') : ps, expr) = tag
getConstr x = error $ show x


makeName :: Int -> Name
makeName n = "_u" ++ show n


partition :: (Eq b) => (a -> b) -> [a] -> [[a]]
partition f [] = []
partition f (x : xs) = acc ++ [cur]
    where
        (acc, cur) = foldl partition' ([], [x]) xs

        partition' (acc, cur) y =
            case f (head cur) == f y of
                True -> (acc, cur ++ [y])
                False -> (acc ++ [cur], [y])


match :: PatTypeScPair -> CoreProgram
match (dts, scs) = (dts', scs')
    where
        scs' = List.map mapSc scs
        dts' = [(DataType name cs) | (PatDataType name cs) <- dts]

        mapSc (PatScDefn name eqs) = ScDefn name vars $ matchEquations dts n vars eqs $ EVar "Nop"
            where
                (patterns, expr) = head eqs
                n = length patterns
                vars = List.map makeName [1..n]


matchExpr :: [PatProgramElement] -> Expr Pattern -> CoreExpr
matchExpr dts (ENum n) = ENum n
matchExpr dts (EVar v) = EVar v
matchExpr dts (EConstr t a) = EConstr t a
matchExpr dts (EAp e1 e2) = EAp (matchExpr dts e1) (matchExpr dts e2)
matchExpr dts (ELam pattern expr) = ELam args' expr'
    where
        name = makeName 1
        args' = [name]
        expr' = matchEquations dts 1 args' [(pattern, expr)] (EVar "Nop")
--TODO: implement cases other than EVar
matchExpr dts (ELet isRec defns expr) = ELet isRec defns' expr'
    where
        expr' = matchExpr dts expr
        defns' = [(v, matchExpr dts expr) | (PVar v, rhs) <- defns]
--TODO: what about case?


matchEquations :: [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchEquations dts n [] eqs def = (matchExpr dts) . snd . head $ eqs
--TODO: get rid of Fatbar
--foldr Fatbar def [matchExpr dts expr | ([], expr) <- eqs]
matchEquations dts n vs eqs def = foldr (matchVarCon dts n vs) def $ PatternMatching.partition isVar eqs


matchVarCon :: [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchVarCon dts n vars eqs def | isVar $ head eqs = matchVar dts n vars eqs def
                               | otherwise = matchConstr dts n vars eqs def


matchVar :: [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchVar dts n (var : vars) eqs def = matchEquations dts n vars [(ps, subst expr var name) | (PVar name : ps, expr) <- eqs] $ def


matchConstr :: [PatProgramElement] -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreExpr
matchConstr dts n vars@(v : vs) eqs def =
    ECase (EVar v) [matchAlter dts tag n vars (choose tag eqs) def | tag <- tags]
    where
        -- it's sufficient to take only the head of equations since all of the
        -- constructors in eqs will be constructors of the same type (assuming
        -- that program is typechecked)
        tags = constructors (getConstr $ head eqs) dts

        choose tag eqs = List.filter (isConstr tag) eqs
        isConstr t1 (PConstr t2 arity ps' : ps, expr) | t1 == t2 = True
        isConstr t _ = False


matchAlter :: [PatProgramElement] -> Int -> Int -> [Name] -> [Equation] -> CoreExpr -> CoreAlt
matchAlter dts tag n (v : vs) eqs def =
    (PConstr tag n' $ List.map PVar vs', matchEquations dts (n' + n) (vs' ++ vs) eqs' def)
    where
        n' = arity tag dts
        vs' = [makeName (n+i) | i <- [1..n']]
        eqs' = [(ps' ++ ps, expr) | ((PConstr tag arity ps' : ps), expr) <- eqs]

