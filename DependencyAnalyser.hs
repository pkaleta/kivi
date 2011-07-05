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
analyseDeps (adts, scs) = (adts, [(name, args, analyseExpr expr) | (name, args, expr) <- freeVars scs])


analyseExpr :: AnnExpr Name (Set Name) -> CoreExpr
analyseExpr (free, ANum n) = ENum n
analyseExpr (free, AVar v) = EVar v
analyseExpr (free, AConstr t a) = EConstr t a
analyseExpr (free, AAp e1 e2) = EAp (analyseExpr e1) (analyseExpr e2)
analyseExpr (free, ACaseSimple expr alts) =
    ECaseSimple (analyseExpr expr) [(tag, analyseExpr body) | (tag, body) <- alts]
analyseExpr (free, ACaseConstr expr alts) =
    ECaseConstr (analyseExpr expr) [(tag, analyseExpr body) | (tag, body) <- alts]
analyseExpr (free, ALam args expr) = ELam args $ analyseExpr expr
analyseExpr (free, ALet isRec defns expr) =
    foldr splitLet expr' binderComponents
    where
        binders = bindersOf defns
        binderSet | isRec = Set.fromList binders
                  | otherwise = Set.empty
        rhss = rhssOf defns
        expr' = analyseExpr expr

        es = foldl getEdges [] defns

        ins v = [a | (a, b) <- es, v == b]
        outs v = [b | (a, b) <- es, v == a]

        getEdges edges (name, (rhsFree, rhs)) =
            edges ++ [(name, v) | v <- (Set.toList $ Set.intersection binderSet rhsFree)]

        binderComponents = scc ins outs binders

        splitLet binderSet letExpr =
            ELet True defns' letExpr
            where
                binders = Set.toList binderSet
                localDefns = [(name, aLookup defns name $ error "impossible") | name <- binders]
                freeVars = foldl Set.union Set.empty $ [free | (name, (free, rhs)) <- localDefns]
                defns' = [(name, analyseExpr rhs) | (name, rhs) <- localDefns]
                isRec = Set.intersection freeVars binderSet /= Set.empty
analyseExpr (free, ASelect r i v) = ESelect r i v
analyseExpr (free, AError msg) = EError msg

