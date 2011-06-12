module DependencyAnalyser where


import Data.Set as Set
import LambdaLifter
import Utils
import Common
import Debug.Trace


dfs :: Ord a => (a -> [a]) -- returns the vertices available from the current vertex
    -> (Set a, [a])        -- current state representing visited vertices and current path
    -> [a]                 -- vertices to visit
    -> (Set a, [a])        -- final state
dfs succ = foldl (dfsHelper succ)


dfsHelper :: Ord a => (a -> [a]) -> (Set a, [a]) -> a -> (Set a, [a])
dfsHelper succ (vis, seq) v =
    case Set.member v vis of
        True -> (vis, seq)  -- vertex has already been visited
        False ->            -- vertex was not visited yet
            (vis', v : seq')
            where (vis', seq') = dfs succ (Set.union vis $ Set.singleton v, seq) (succ v)


spanDfs :: Show a => Ord a => (a -> [a]) -> (Set a, [Set a]) -> [a] -> (Set a, [Set a])
spanDfs succ = foldl (spanDfsHelper succ)


spanDfsHelper :: Show a => Ord a => (a -> [a]) -> (Set a, [Set a]) -> a -> (Set a, [Set a])
spanDfsHelper succ (vis, setSeq) v =
    case Set.member v vis of
        True -> (vis, setSeq)
        False ->
            (vis', Set.fromList (v : seq) : setSeq)
            where (vis', seq) = dfs succ (Set.union vis $ Set.singleton v, []) (succ v)


scc :: Show a => Ord a => (a -> [a]) -> (a -> [a]) -> [a] -> [Set a]
scc ins outs vs = topSortedSccs
    where
        topSortedVs = snd $ dfs outs (Set.empty, []) vs
        topSortedSccs = snd $ spanDfs ins (Set.empty, []) topSortedVs


analyseDeps :: CoreProgram -> CoreProgram
analyseDeps scs = Prelude.map analyseDepsSc $ freeVars scs


analyseDepsSc :: (Name, [AnnPatternFunDef CorePatExpr (Set Name)]) -> CoreScDefn
analyseDepsSc (name, defns) = (name, defns')
    where defns' = [(pattern, analyseExpr expr) | (pattern, expr) <- defns]


analyseExpr :: AnnExpr CorePatExpr (Set Name) -> CoreExpr
analyseExpr (free, ANum n) = ENum n
analyseExpr (free, AVar v) = EVar v
analyseExpr (free, AConstr t a) = EConstr t a
analyseExpr (free, AAp e1 e2) = EAp (analyseExpr e1) (analyseExpr e2)
analyseExpr (free, ACase expr alts) = ECase (analyseExpr expr) [(tag, args, analyseExpr body) | (tag, args, body) <- alts]
analyseExpr (free, ALam args expr) = ELam args $ analyseExpr expr
analyseExpr (free, ALet isRec defns expr) =
    foldr splitLet expr' binderComponents
    where
        binders = getVarNames $ bindersOf defns
        binderSet | isRec = Set.fromList binders
                  | otherwise = Set.empty
        rhss = rhssOf defns
        expr' = analyseExpr expr

        es = foldl getEdges [] defns

        ins v = [a | (a, b) <- es, v == b]
        outs v = [b | (a, b) <- es, v == a]

        getEdges edges (EVar name, (rhsFree, rhs)) =
            edges ++ [(name, v) | v <- (Set.toList $ Set.intersection binderSet rhsFree)]

        binderComponents = scc ins outs binders

        splitLet binderSet letExpr =
            ELet True defns' letExpr
            where
                binders = Set.toList binderSet
                localDefns = [(EVar name, aLookup defns (EVar name) $ error "impossible") | name <- binders]
                freeVars = foldl Set.union Set.empty $ [free | (name, (free, rhs)) <- localDefns]
                defns' = [(name, analyseExpr rhs) | (name, rhs) <- localDefns]
                isRec = Set.intersection freeVars binderSet /= Set.empty
