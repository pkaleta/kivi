module PatternMatch where


import Common
import Utils
import Data.Map as Map
import Debug.Trace


mergePatterns :: CoreProgram -> CoreProgram
mergePatterns program = Map.toList $ foldl mergePattern Map.empty program

mergePattern :: Map Name ([PatternFunDef Name]) -> CoreScDefn -> Map Name ([PatternFunDef Name])
mergePattern scAcc (name, defns) = -- it would always contain only one definition
    Map.alter update name scAcc
    where
        update Nothing = Just defns
        update (Just oldDefns) = Just (oldDefns ++ defns)

