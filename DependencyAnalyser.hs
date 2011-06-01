module DependencyAnalyser where


import Data.Set as Set


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


spanDfs :: Ord a => (a -> [a]) -> (Set a, [Set a]) -> [a] -> (Set a, [Set a])
spanDfs succ = foldl (spanDfsHelper succ)


spanDfsHelper :: Ord a => (a -> [a]) -> (Set a, [Set a]) -> a -> (Set a, [Set a])
spanDfsHelper succ (vis, setSeq) v =
    case Set.member v vis of
        True -> (vis, setSeq)
        False ->
            (vis', Set.fromList (v : seq) : setSeq)
            where (vis', seq) = dfs succ (Set.union vis $ Set.singleton v, seq) (succ v)


scc :: Ord a => (a -> [a]) -> (a -> [a]) -> [a] -> [Set a]
scc ins outs vs =
    snd topSortedSccs
    where
        topSortedVs = snd $ dfs outs (Set.empty, []) vs
        topSortedSccs = spanDfs ins (Set.empty, []) topSortedVs

