module PatternMatching where


import List
import Common
import Utils
import Data.Map as Map
import Parser
import Debug.Trace


mergePatterns :: CoreProgram -> CoreProgram
mergePatterns (dts, scs) = (dts, scs')
    where
        scs' = [ScDefn name defns | (name, defns) <- Map.toList $ foldl mergePattern Map.empty scs]


mergePattern :: Map Name [CoreEquation] -> ProgramElement Name -> Map Name ([CoreEquation])
mergePattern scMap (ScDefn name defns) = -- it would always contain only one definition
    Map.alter update name scMap
    where
        update Nothing = Just defns
        update (Just oldDefns) = Just (oldDefns ++ defns)


--TODO: implement
arity :: Int -> [CoreProgramElement] -> Int
arity tag (DataType name cs : types) =
    case findConstr tag cs of
        Nothing -> arity tag types
        Just (t, a) -> a
arity tag [] = error $ "Could not find constructor with tag: " ++ show tag


--TODO: implement
constructors :: Int -> [CoreProgramElement] -> [Int]
constructors tag (DataType name cs : types) =
    case findConstr tag cs of
        Nothing -> constructors tag types
        Just (t, a) -> [t | (t, a) <- cs]
constructors tag [] = error $ "Could not find constructor with tag: " ++ show tag


findConstr :: Int -> [Constr] -> Maybe Constr
findConstr tag ((t, a) : cs) | tag == t = Just (t, a)
                             | otherwise = findConstr tag cs
findConstr tag [] = Nothing


subst :: Expr Name -> Name -> Name -> Expr Name
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


isVar :: CoreEquation -> Bool
isVar (PVar name : ps, expr) = True
isVar _ = False


isConstr :: CoreEquation -> Bool
isConstr eq = not $ isVar eq


getConstr :: CoreEquation -> Int
getConstr ((PConstr tag arity ps') : ps, expr) = tag
getConstr x = error $ show x


makeName :: Int -> Name
makeName n = "_u" ++ show n


partition :: (Eq b) => (a -> b) -> [a] -> [[a]]
partition f (x : xs) = acc ++ [cur]
    where
        (acc, cur) = foldl partition' ([], [x]) xs

        partition' (acc, cur) y =
            case f (head cur) == f y of
                True -> (acc, cur ++ [y])
                False -> (acc ++ [cur], [y])


match :: CoreProgram -> CoreProgram
match (dts, scs) = (dts, scs')
    where
        scs' = List.map mapSc scs

        mapSc (ScDefn name eqs) = ScDefn name [([], matchEquations dts n vars eqs $ EVar "Nop")]
            where
                (patterns, expr) = head eqs
                n = length patterns
                vars = List.map makeName [1..n]


matchEquations :: [CoreProgramElement] -> Int -> [Name] -> [CoreEquation] -> Expr Name -> Expr Name
matchEquations dts n [] eqs def = foldr Fatbar def [expr | ([], expr) <- eqs]
matchEquations dts n vs eqs def = foldr (matchVarCon dts n vs) def $ PatternMatching.partition isVar eqs


matchVarCon :: [CoreProgramElement] -> Int -> [Name] -> [CoreEquation] -> Expr Name -> Expr Name
matchVarCon dts n vars eqs def | isVar $ head eqs = matchVar dts n vars eqs def
                               | otherwise = matchConstr dts n vars eqs def


matchVar :: [CoreProgramElement] -> Int -> [Name] -> [CoreEquation] -> Expr Name -> Expr Name
matchVar dts n (var : vars) eqs def = matchEquations dts n vars [(ps, subst expr var name) | (PVar name : ps, expr) <- eqs] $ def


matchConstr :: [CoreProgramElement] -> Int -> [Name] -> [CoreEquation] -> Expr Name -> Expr Name
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


matchAlter :: [CoreProgramElement] -> Int -> Int -> [Name] -> [CoreEquation] -> Expr Name -> Alter Name
matchAlter dts tag n (v : vs) eqs def =
    (PConstr tag n' $ List.map PVar vs', matchEquations dts (n' + n) (vs' ++ vs) eqs' def)
    where
        n' = arity tag dts
        vs' = [makeName (n+i) | i <- [1..n']]
        eqs' = [(ps' ++ ps, expr) | ((PConstr tag arity ps' : ps), expr) <- eqs]

