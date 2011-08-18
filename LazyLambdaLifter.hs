module LazyLambdaLifter where


import Common
import LambdaLifter
import NameSupply
import Utils
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Debug.Trace


type FloatedDefns = [(Level, IsRec, [(Name, Expr Name)])]
type Level = Int


lazyLambdaLift :: CoreProgram -> CoreProgram
lazyLambdaLift (adts, scs) =
    (adts, float . mergeLambdas . renameL . identifyMFEs . annotateLevels . separateLambdas $ scs)


separateLambdas :: [CoreScDefn] -> [CoreScDefn]
separateLambdas [] = []
separateLambdas ((ScDefn name args expr) : scs) = (ScDefn name [] (mkSepArgs args $ separateLambdasExpr expr)) : separateLambdas scs


separateLambdasExpr :: CoreExpr -> CoreExpr
separateLambdasExpr (ENum n) = ENum n
separateLambdasExpr (EChar c) = EChar c
separateLambdasExpr (EVar v) = EVar v
separateLambdasExpr (EConstr t a) = EConstr t a
separateLambdasExpr (EAp e1 e2) = EAp (separateLambdasExpr e1) (separateLambdasExpr e2)
separateLambdasExpr (ECaseSimple expr alts) = separateLambdasExprCase ECaseSimple expr alts
separateLambdasExpr (ECaseConstr expr alts) = separateLambdasExprCase ECaseConstr expr alts
separateLambdasExpr (ELam args body) =
    mkSepArgs args body'
    where body' = separateLambdasExpr body
separateLambdasExpr (ELet isRec defns body) =
    ELet isRec (List.map mkDefn defns) (separateLambdasExpr body)
    where
        mkDefn (name, expr) = (name, separateLambdasExpr expr)
separateLambdasExpr (ESelect r i v) = ESelect r i v
separateLambdasExpr (EError msg) = EError msg


separateLambdasExprCase :: (CoreExpr -> [CoreAlt] -> CoreExpr) -> CoreExpr -> [CoreAlt] -> CoreExpr
separateLambdasExprCase constr expr alts =
    constr (separateLambdasExpr expr) $ List.map mkAlt alts
    where
        mkAlt (t, expr) = (t, separateLambdasExpr expr)


mkSepArgs :: [Name] -> CoreExpr -> CoreExpr
mkSepArgs args expr = foldr mkELam expr args
    where
        mkELam arg expr = ELam [arg] expr


annotateLevels :: [CoreScDefn] -> AnnProgram (Name, Level) Level
annotateLevels = freeToLevel . freeVars


freeToLevel :: AnnProgram Name (Set Name) -> AnnProgram (Name, Level) Level
freeToLevel [] = []
freeToLevel ((AnnScDefn name [] expr) : scs) = (AnnScDefn name [] $ freeToLevelExpr 0 Map.empty expr) : freeToLevel scs


freeToLevelExpr :: Level -> Map Name Level -> AnnExpr Name (Set Name) -> AnnExpr (Name, Level) Level
freeToLevelExpr level env (free, ANum n) = (0, ANum n)
freeToLevelExpr level env (free, AChar c) = (0, AChar c)
freeToLevelExpr level env (free, AVar v) = (varLevel, AVar v)
    where
        varLevel = case Map.lookup v env of
            Just level -> level
            Nothing -> 0
freeToLevelExpr level env (free, AConstr t a) = (0, AConstr t a)
freeToLevelExpr level env (free, AAp e1 e2) = (max e1Level e2Level, AAp e1' e2')
    where
        e1'@(e1Level, _) = freeToLevelExpr level env e1
        e2'@(e2Level, _) = freeToLevelExpr level env e2
freeToLevelExpr level env (free, ALam args expr) =
    (freeSetToLevel env free, ALam args' expr')
    where
        expr' = freeToLevelExpr level' (Map.union (Map.fromList args') env) expr
        args' = [(arg, level') | arg <- args]
        level' = level + 1
freeToLevelExpr level env (free, ALet isRec defns expr) =
    (exprLevel, ALet isRec defns' expr')
    where
        binders = bindersOf defns
        rhss = rhssOf defns

        binders' = [(name, maxRhsLevel) | name <- binders]
        rhss' = [freeToLevelExpr level rhssEnv rhs | rhs <- rhss]
        expr'@(exprLevel, _) = freeToLevelExpr level exprEnv expr
        defns' = zip binders' rhss'

        rhssFreeVars = foldl collectFreeVars Set.empty rhss
        maxRhsLevel = freeSetToLevel rhssLevelEnv rhssFreeVars

        exprEnv = Map.union (Map.fromList binders') env

        rhssEnv | isRec = exprEnv
                | otherwise = env

        rhssLevelEnv | isRec = Map.union (Map.fromList [(name, 0) | name <- binders]) env
                     | otherwise = env

        -- helper function to collect free variables from right had side
        -- expressions in definitions
        collectFreeVars freeVars (free, rhs) = Set.union freeVars free
freeToLevelExpr level env (free, ACaseSimple expr alts) =
    freeToLevelExprCase ACaseSimple level env free expr alts
freeToLevelExpr level env (free, ACaseConstr expr alts) =
    freeToLevelExprCase ACaseConstr level env free expr alts
--TODO: not sure if this is correct
freeToLevelExpr level env (free, expr@(ASelect r i v)) = (varLevel, ASelect r i (v, varLevel))
    where
        varLevel = case Map.lookup v env of
            Just level -> level
            Nothing -> 0
freeToLevelExpr level env (free, AError msg) = (0, AError msg)


freeToLevelExprCase :: ((AnnExpr (Name, Level) Level) -> [AnnAlt (Name, Level) Level] -> (AnnExpr' (Name, Level) Level))
                    -> Level
                    -> Map Name Level
                    -> Set Name
                    -> AnnExpr Name (Set Name)
                    -> [AnnAlt Name (Set Name)]
                    -> AnnExpr (Name, Level) Level
freeToLevelExprCase constr level env free expr alts =
    (freeSetToLevel env free, constr expr' alts')
    where
        expr'@(exprLevel, _) = freeToLevelExpr level env expr
        alts' = List.map mapAlt alts

        mapAlt (tag, altExpr) =
            (tag, altExpr')
            where
                altExpr' = freeToLevelExpr level env altExpr


freeSetToLevel :: Map Name Level -> Set Name -> Level
freeSetToLevel env free =
    foldl max 0 $ [ case Map.lookup var env of
        Just level -> level
        Nothing -> 0 | var <- (Set.toList free)]


identifyMFEs :: AnnProgram (Name, Level) Level -> [ScDefn (Name, Level)]
identifyMFEs scs = [(ScDefn name [] $ identifyMFEsExpr 0 expr) | (AnnScDefn name [] expr) <- scs]


identifyMFEsExpr :: Level -> AnnExpr (Name, Level) Level -> Expr (Name, Level)
identifyMFEsExpr cxtLevel (exprLevel, expr) =
    case exprLevel == cxtLevel || notMFECandidate expr of
        True -> expr'
        False -> transformMFE exprLevel expr'

    where
        expr' = identifyMFEsExpr1 exprLevel expr

        notMFECandidate (ANum n) = True
        notMFECandidate (AVar v) = True
        notMFECandidate (AConstr t a) = True
        notMFECandidate (AError msg) = True
        notMFECandidate (ASelect r i v) = True
        notMFECandidate _ = False

        transformMFE level expr = ELet False [(("v", level), expr)] (EVar "v")


identifyMFEsExpr1 :: Level -> AnnExpr' (Name, Level) Level -> Expr (Name, Level)
identifyMFEsExpr1 level (ANum n) = ENum n
identifyMFEsExpr1 level (AChar c) = EChar c
identifyMFEsExpr1 level (AVar v) = EVar v
identifyMFEsExpr1 level (AConstr t a) = EConstr t a
identifyMFEsExpr1 level (AAp e1 e2) = EAp (identifyMFEsExpr level e1) (identifyMFEsExpr level e2)
identifyMFEsExpr1 level (ALam args@[(name, argLevel)] expr) = ELam args (identifyMFEsExpr argLevel expr)
identifyMFEsExpr1 level (ALet isRec defns expr) =
    ELet isRec defns' expr'
    where
        defns' = [((name, defnLevel), identifyMFEsExpr defnLevel rhs) | ((name, defnLevel), rhs) <- defns]
        expr' = identifyMFEsExpr level expr
identifyMFEsExpr1 level (ACaseSimple expr@(exprLevel, _) alts) = identifyMFEsExpr1Case ECaseSimple level expr exprLevel alts
identifyMFEsExpr1 level (ACaseConstr expr@(exprLevel, _) alts) = identifyMFEsExpr1Case ECaseConstr level expr exprLevel alts
identifyMFEsExpr1 level (ASelect r i (v, lvl)) = ESelect r i v
identifyMFEsExpr1 level (AError msg) = EError msg


identifyMFEsExpr1Case :: (Expr (Name, Level) -> [Alter Int (Name, Level)] -> Expr (Name, Level))
                      -> Level
                      -> AnnExpr (Name, Level) Level
                      -> Level
                      -> [AnnAlt (Name, Level) Level]
                      -> Expr (Name, Level)
identifyMFEsExpr1Case constr level expr exprLevel alts =
    constr expr' alts'
    where
        expr' = identifyMFEsExpr level expr
        alts' = [(tag, identifyMFEsExpr level body) | (tag, body) <- alts]


renameL :: [ScDefn (Name, Level)] -> [ScDefn (Name, Level)]
renameL = renameGen newNamesL


newNamesL :: NameSupply -> [(Name, Level)] -> (NameSupply, [(Name, Level)], Map Name Name)
newNamesL ns names =
    (ns', names2, mapping)
    where
        names0 = List.map fst names
        levels = List.map snd names
        (ns', names1) = getNames ns names0
        names2 = zip names1 levels
        mapping = Map.fromList $ zip names0 names1


mergeLambdas :: [ScDefn (Name, Level)] -> [ScDefn (Name, Level)]
mergeLambdas scs = [(ScDefn name args $ mergeLambdasExpr expr) | (ScDefn name args expr) <- scs]


mergeLambdasExpr :: Expr (Name, Level) -> Expr (Name, Level)
mergeLambdasExpr (ELam args expr) =
    case expr' of
        (ELam args' innerExpr) ->
            ELam (args ++ args') innerExpr
        _ ->
            ELam args expr'
    where
        expr' = mergeLambdasExpr expr
mergeLambdasExpr expr = expr


float :: [ScDefn (Name, Level)] -> [CoreScDefn]
float = foldl collectFloatedSc []


collectFloatedSc :: [CoreScDefn] -> ScDefn (Name, Level) -> [CoreScDefn]
collectFloatedSc scsAcc (ScDefn name [] expr) =
    scsAcc ++ [ScDefn name [] expr'] ++ floatedScs
    where
        (fds, expr') = floatExpr expr
        floatedScs = foldl createScs [] fds

        createScs scs (level, isRec, defns) =
            scs ++ [ScDefn name [] defn | (name, defn) <- defns]


floatExpr :: Expr (Name, Level) -> (FloatedDefns, CoreExpr)
floatExpr (ENum n) = ([], ENum n)
floatExpr (EChar c) = ([], EChar c)
floatExpr (EVar v) = ([], EVar v)
floatExpr (EConstr t a) = ([], EConstr t a)
floatExpr (EAp e1 e2) = (fds1 ++ fds2, EAp e1' e2')
    where
        (fds1, e1') = floatExpr e1
        (fds2, e2') = floatExpr e2
floatExpr (ELam args expr) = (outerFds, ELam args' $ wrap innerFds expr')
    where
        args' = [arg | (arg, level) <- args]
        (arg, curLevel) = head args
        (fdBody, expr') = floatExpr expr
        (innerFds, outerFds) = List.partition checkLevel fdBody

        -- predicate to partition the definitions based on definition level
        checkLevel (level, isRec, defns) = level >= curLevel

        -- helper function which wraps an expr into let binding with given defns
        wrap floatedDefns expr =
            foldr wrapDefn expr floatedDefns
            where
                wrapDefn (level, isRec, defns) expr = ELet isRec defns expr
floatExpr (ELet isRec defns expr) = (outerFds, expr')
    where
        outerFds = defnsFds ++ [localFd] ++ exprFds
        (exprFds, expr') = floatExpr expr
        (defnsFds, defns') = mapAccumL collectDefns [] defns
        localFd = (level, isRec, defns')
        ((name, level), _firstDefn) = head defns

        collectDefns defnsAcc ((name, level), rhs) =
            (rhsFds ++ defnsAcc, (name, rhs'))
            where
                (rhsFds, rhs') = floatExpr rhs
floatExpr (ECaseSimple expr alts) = floatExprCase ECaseSimple expr alts
floatExpr (ECaseConstr expr alts) = floatExprCase ECaseConstr expr alts
floatExpr (ESelect r i v) = ([], ESelect r i v)
floatExpr (EError msg) = ([], EError msg)


floatExprCase :: (CoreExpr -> [CoreAlt] -> CoreExpr)
              -> Expr (Name, Level)
              -> [Alter Int (Name, Level)]
              -> (FloatedDefns, Expr Name)
floatExprCase constr expr alts = (exprFds ++ altsFds, constr expr' alts')
    where
        (exprFds, expr') = floatExpr expr

        (altsFds, alts') = mapAccumL collectAlts [] alts

        collectAlts altsAcc (tag, altExpr) =
            (altFds ++ altsAcc, (tag, altExpr'))
            where
                (altFds, altExpr') = floatExpr altExpr

