module PatternMatching where


import List
import Common
import Utils
import Data.Map as Map
import Parser
import Debug.Trace


mergePatterns :: CoreProgram -> CoreProgram
mergePatterns program = Map.toList $ foldl mergePattern Map.empty program

mergePattern :: Map Name [Equation] -> CoreScDefn -> Map Name ([Equation])
mergePattern scAcc (name, defns) = -- it would always contain only one definition
    Map.alter update name scAcc
    where
        update Nothing = Just defns
        update (Just oldDefns) = Just (oldDefns ++ defns)


--TODO: implement
arity :: Int -> Int
arity tag = 0


--TODO: implement
constructors :: Int -> [Int]
constructors tag = [tag]


--TODO: implement
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


isVar :: Equation -> Bool
isVar (Var name : ps, expr) = True
isVar _ = False


isConstr :: Equation -> Bool
isConstr eq = not $ isVar eq


getConstr :: Equation -> Int
getConstr ((Constr tag arity ps') : ps, expr) = tag
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


match :: Int -> [Name] -> [Equation] -> Expr Name -> Expr Name
match n [] eqs def = foldr Fatbar def [expr | ([], expr) <- eqs]
match n vs eqs def = foldr (matchVarCon n vs) def $ PatternMatching.partition isVar eqs


matchVarCon :: Int -> [Name] -> [Equation] -> Expr Name -> Expr Name
matchVarCon n vars eqs def | isVar $ head eqs = matchVar n vars eqs def
                           | otherwise = matchConstr n vars eqs def


matchVar :: Int -> [Name] -> [Equation] -> Expr Name -> Expr Name
matchVar n (var : vars) eqs def = match n vars [(ps, subst expr var name) | (Var name : ps, expr) <- eqs] $ def


matchConstr :: Int -> [Name] -> [Equation] -> Expr Name -> Expr Name
matchConstr n vars@(v : vs) eqs def =
    ECase (EVar v) [matchAlter tag n vars (choose tag eqs) def | tag <- tags]
    where
        -- it's sufficient to take only the head of equations since all of the
        -- constructors in eqs will be constructors of the same type (assuming
        -- that program is typechecked)
        tags = constructors $ getConstr $ head eqs

        choose tag eqs = List.filter (isConstr tag) eqs
        isConstr t1 (Constr t2 arity ps' : ps, expr) | t1 == t2 = True
        isConstr t _ = False


matchAlter :: Int -> Int -> [Name] -> [Equation] -> Expr Name -> Alter Name
matchAlter tag n (v : vs) eqs def =
    (Constr tag n' $ List.map Var vs', match (n' + n) (vs' ++ vs) eqs' def)
    where
        n' = arity tag
        vs' = [makeName (n+i) | i <- [1..n']]
        eqs' = [(ps' ++ ps, expr) | ((Constr tag arity ps' : ps), expr) <- eqs]

