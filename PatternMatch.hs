module PatternMatch where


import Common
import Utils
import Data.Map as Map


mergePatterns :: CoreProgram -> CoreProgram
mergePatterns program = foldl mergePattern Map.empty program

mergePattern :: [CoreScDefn] -> CoreScDefn -> [CoreScDefn]
mergePattern defns (name, pattern, expr) =
    Map.alter (update (PatternFunDef pattern expr)) name defns
    where
        update value Nothing = value
        update value (Just list) = list ++ [value]

