module DependencyAnalyser where


import Data.Set as Set


dfs :: Ord a => (a -> [a]) -> (Set a, [a]) -> [a] -> (Set a, [a])
dfs succ = foldl (dfsHelper succ)


dfsHelper :: Ord a => (a -> [a]) -> (Set a, [a]) -> a -> (Set a, [a])
dfsHelper succ (vis, seq) v =
    case Set.member v vis of
        True -> (vis, seq)  -- vertex has already been visited
        False ->            -- vertex was not visited yet
            (vis', v : seq')
            where (vis', seq') = dfs succ (vis, seq) (succ v)

