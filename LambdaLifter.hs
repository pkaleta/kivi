module LambdaLifter where


import Utils
import Common
import Data.Set (Set)
import qualified Data.Set as Set
import NameSupply
import Data.Map (Map)
import qualified Data.Map as Map
import List
import Debug.Trace


type AnnExpr a b = (b, AnnExpr' a b)

data AnnExpr' a b = AVar Name
                  | ANum Int
                  | AConstr Int Int
                  | AAp (AnnExpr a b) (AnnExpr a b)
                  | ALet IsRec [AnnDefn a b] (AnnExpr a b)
                  | ACase (AnnExpr a b) [AnnAlt a b]
                  | ALam [a] (AnnExpr a b)
    deriving Show

type AnnDefn a b = (a, AnnExpr a b)
type AnnAlt a b = (Int, [a], AnnExpr a b)
type AnnProgram a b = [(Name, [a], AnnExpr a b)]
type FloatedDefns = [(Level, IsRec, [(Name, Expr Name)])]
type Level = Int


lambdaLift :: CoreProgram -> CoreProgram
lambdaLift (adts, scs) = (adts, collectScs . rename . abstract . freeVars $ scs)


freeVars :: [CoreScDefn] -> AnnProgram Name (Set Name)
freeVars [] = []
freeVars ((name, args, expr) : scs) = (name, args, calcFreeVars (Set.fromList args) expr) : (freeVars scs)


calcFreeVars :: (Set Name) -> CoreExpr -> AnnExpr Name (Set Name)
calcFreeVars localVars (ENum n) = (Set.empty, ANum n)
calcFreeVars localVars (EVar v) | Set.member v localVars = (Set.singleton v, AVar v)
                                | otherwise = (Set.empty, AVar v)
calcFreeVars localVars (EAp e1 e2) = (Set.union s1 s2, AAp ae1 ae2)
    where
        ae1@(s1, _) = calcFreeVars localVars e1
        ae2@(s2, _) = calcFreeVars localVars e2
calcFreeVars localVars (ELam args expr) = (Set.difference fvs argsSet, ALam args expr')
    where
        expr'@(fvs, _) = calcFreeVars (Set.union localVars argsSet) expr
        argsSet = Set.fromList args
calcFreeVars localVars (ELet isRec defns expr) =
    (Set.union bodyFvs defnsFvs, ALet isRec defns' expr')
    where
        binders = Set.fromList $ bindersOf defns
        exprLvs = Set.union binders localVars
        rhsLvs | isRec = exprLvs
               | otherwise = localVars
        -- annotated stuff
        rhss' = map (calcFreeVars rhsLvs) $ rhssOf defns
        defns' = zip (Set.toList binders) rhss'
        expr' = calcFreeVars exprLvs expr
        rhssFvs = foldl Set.union Set.empty (map freeVarsOf rhss')
        defnsFvs | isRec = Set.difference rhssFvs binders
                 | otherwise = rhssFvs
        bodyFvs = Set.difference (freeVarsOf expr') binders
calcFreeVars localVars (ECaseSimple expr alts) = calcFreeVarsCase localVars expr alts
calcFreeVars localVars (ECaseConstr expr alts) = calcFreeVarsCase localVars expr alts
calcFreeVars localVars (EConstr t n) =
    (Set.empty, AConstr t n)


calcFreeVarsCase :: (Set Name) -> CoreExpr -> [CoreAlt] -> AnnExpr Name (Set Name)
calcFreeVarsCase localVars expr alts = (fvs, ACase expr' alts')
    where
        expr'@(exprFvs, _) = calcFreeVars localVars expr
        (fvs, alts') = mapAccumL freeVarsAlts exprFvs alts

        freeVarsAlts fvs (t, vars, body) =
            (Set.union fvs (Set.difference bodyFvs varsSet), (t, vars, body'))
            where
                body'@(bodyFvs, _) = calcFreeVars (Set.union varsSet localVars) body
                varsSet = Set.fromList vars


abstract :: AnnProgram Name (Set Name) -> [CoreScDefn]
abstract program = [(name, args, abstractExpr expr) | (name, args, expr) <- program]


abstractExpr :: AnnExpr Name (Set Name) -> CoreExpr
abstractExpr (freeVars, ANum n) = ENum n
abstractExpr (freeVars, AVar v) = EVar v
abstractExpr (freeVars, AAp e1 e2) = EAp (abstractExpr e1) (abstractExpr e2)
abstractExpr (freeVars, ALet isRec defns expr) =
    ELet isRec [(name, abstractExpr body) | (name, body) <- defns] (abstractExpr expr)
abstractExpr (freeVars, ALam args expr) =
    foldl EAp sc $ map EVar freeVarsList
    where
        freeVarsList = Set.toList freeVars
        sc = ELet False [("sc", scBody)] (EVar "sc")
        scBody = ELam (freeVarsList ++ args) (abstractExpr expr)
abstractExpr (freeVars, ACase expr alts) =
    ECase (abstractExpr expr) alts'
    where
        alts' = map abstractAlt alts
        abstractAlt (t, vars, expr) = (t, vars, abstractExpr expr)
abstractExpr (freeVars, AConstr t a) = EConstr t a


renameGen :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
          -> Program a
          -> Program a
renameGen newNamesFun scs = snd $ mapAccumL (renameSc newNamesFun) initialNameSupply scs


rename :: [CoreScDefn] -> [CoreScDefn]
rename = renameGen newNames


newNames :: NameSupply -> [Name] -> (NameSupply, [Name], Map Name Name)
newNames ns names =
    (ns', names', mapping)
    where
        (ns', names') = getNames ns names
        mapping = Map.fromList $ zip names names'


renameSc :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
         -> NameSupply
         -> ScDefn a
         -> (NameSupply, ScDefn a)
renameSc newNamesFun ns (name, args, expr) =
    (ns2, (name, args', expr'))
    where
        (ns1, args', mapping) = newNamesFun ns args
        (ns2, expr') = renameExpr newNamesFun mapping ns1 expr


renameExpr :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name)) -- function used to create new names for variables
           -> Map Name Name
           -> NameSupply
           -> Expr a
           -> (NameSupply, Expr a)
renameExpr newNamesFun mapping ns (ENum n) = (ns, ENum n)
renameExpr newNamesFun mapping ns (EVar v) =
    (ns, EVar v') -- for built-int functions (+,-, etc.) we have to use old name
    where
        v' = case Map.lookup v mapping of
            (Just x) -> x
            Nothing -> v
renameExpr newNamesFun mapping ns (EAp e1 e2) =
    (ns2, EAp e1' e2')
    where
        (ns1, e1') = renameExpr newNamesFun mapping ns e1
        (ns2, e2') = renameExpr newNamesFun mapping ns1 e2
renameExpr newNamesFun mapping ns (ELam args expr) =
    (ns2, ELam args' expr')
    where
        (ns1, args', mapping') = newNamesFun ns args
        (ns2, expr') = renameExpr newNamesFun (Map.union mapping' mapping) ns1 expr
renameExpr newNamesFun mapping ns (ELet isRec defns expr) =
    (ns2, ELet isRec defns' expr')
    where
        binders = bindersOf defns
        rhss = rhssOf defns
        (ns1, binders', mapping') = newNamesFun ns binders
        exprMapping = (Map.union mapping' mapping)
        defnsMapping | isRec = exprMapping
                     | otherwise = mapping
        (ns2, rhss') = mapAccumL (renameExpr newNamesFun exprMapping) ns1 rhss
        (ns3, expr') = renameExpr newNamesFun exprMapping ns2 expr
        defns' = zip binders' rhss'
renameExpr newNamesFun mapping ns (ECase expr alts) =
    (ns2, ECase expr' alts')
    where
        (ns1, expr') = renameExpr newNamesFun mapping ns expr
        (ns2, alts') = mapAccumL (renameAlt mapping) ns1 alts

        renameAlt mapping ns (t, vars, body) =
            (ns2, (t, vars', body'))
            where
                (ns1, vars', mapping') = newNamesFun ns vars
                (ns2, body') = renameExpr newNamesFun (Map.union mapping' mapping) ns1 body
renameExpr newNamesFun mapping ns (EConstr t a) = (ns, EConstr t a)


collectScs :: [CoreScDefn] -> [CoreScDefn]
collectScs scs = foldl collectSc [] scs


collectSc :: [CoreScDefn] -> CoreScDefn -> [CoreScDefn]
collectSc scsAcc (name, args, expr) =
    [(name, args', expr')] ++ scsAcc ++ scs
    where
        (args', (scs, expr')) = case expr of
                                    (ELet isRec [(scName, (ELam lamArgs lamExpr))] letBody) ->
                                        (lamArgs, collectExpr lamExpr)
                                    expr ->
                                        (args, collectExpr expr)


collectExpr :: CoreExpr -> ([CoreScDefn], CoreExpr)
collectExpr (ENum n) = ([], ENum n)
collectExpr (EVar v) = ([], EVar v)
collectExpr (EAp e1 e2) =
    (scs1 ++ scs2, EAp e1' e2')
    where
        (scs1, e1') = collectExpr e1
        (scs2, e2') = collectExpr e2
collectExpr (ELam args expr) = (scs, ELam args expr')
    where (scs, expr') = collectExpr expr
collectExpr (ELet isRec defns expr) =
    (defnsScs ++ localScs ++ exprScs, mkELet isRec varDefns expr')
    where
        (defnsScs, defns') = foldl collectDef ([], []) defns
        (scDefns, varDefns) = List.partition isSc defns'
        -- supercombinators declared locally in defns as lambda expressions
        localScs = [(name, args, expr) | (name, ELam args expr) <- scDefns]
        (exprScs, expr') = collectExpr expr

        -- is supercombinator predicate
        isSc (name, (ELam _ _)) = True
        isSc (name, _) = False

        -- helper to extract supercombinators nested in definitions
        collectDef (scsAcc, defnsAcc) (name, expr) =
            case collectExpr expr of
                ([(scName1, scArgs, scExpr)], (EVar scName2)) | scName1 == scName2 ->
                    (scsAcc ++ [(name, scArgs, scExpr)], defnsAcc)
                (scs, expr') ->
                    (scsAcc ++ scs, (name, expr') : defnsAcc)

        --getting rid of let expressions with empty definitions part
        mkELet isRec varDefns expr =
            case length varDefns > 0 of
                True -> ELet isRec varDefns expr
                False -> expr
collectExpr (ECase expr alts) =
    (exprScs ++ altsScs, ECase expr' alts')
    where
        (exprScs, expr') = collectExpr expr
        (altsScs, alts') = mapAccumL collectAlt [] alts

        collectAlt scs (t, vars, expr) =
            (scs ++ exprScs, (t, vars, expr'))
            where (exprScs, expr') = collectExpr expr
collectExpr (EConstr t a) = ([], EConstr t a)


freeVarsOf :: AnnExpr Name (Set Name) -> Set Name
freeVarsOf (fvs, _) = fvs


------------------ lazy lambda lifter

lazyLambdaLift :: CoreProgram -> CoreProgram
lazyLambdaLift = float . mergeLambdas . renameL . identifyMFEs . annotateLevels . separateLambdas


separateLambdas :: CoreProgram -> CoreProgram
separateLambdas [] = []
separateLambdas ((name, args, expr) : scs) = (name, [], mkSepArgs args $ separateLambdasExpr expr) : separateLambdas scs


separateLambdasExpr :: CoreExpr -> CoreExpr
separateLambdasExpr (ENum n) = (ENum n)
separateLambdasExpr (EVar v) = (EVar v)
separateLambdasExpr (EConstr t a) = (EConstr t a)
separateLambdasExpr (EAp e1 e2) = EAp (separateLambdasExpr e1) (separateLambdasExpr e2)
separateLambdasExpr (ECase expr alts) =
    ECase (separateLambdasExpr expr) $ map mkAlt alts
    where
        mkAlt (t, args, expr) = (t, args, separateLambdasExpr expr)
separateLambdasExpr (ELam args body) =
    mkSepArgs args body'
    where body' = separateLambdasExpr body
separateLambdasExpr (ELet isRec defns body) =
    ELet isRec (map mkDefn defns) (separateLambdasExpr body)
    where
        mkDefn (name, expr) = (name, separateLambdasExpr expr)


mkSepArgs :: [Name] -> CoreExpr -> CoreExpr
mkSepArgs args expr = foldr mkELam expr args
    where
        mkELam arg expr = ELam [arg] expr


annotateLevels :: CoreProgram -> AnnProgram (Name, Level) Level
annotateLevels = freeToLevel . freeVars


freeToLevel :: AnnProgram Name (Set Name) -> AnnProgram (Name, Level) Level
freeToLevel [] = []
freeToLevel ((name, [], expr) : scs) = (name, [], freeToLevelExpr 0 Map.empty expr) : freeToLevel scs


freeToLevelExpr :: Level -> Map Name Level -> AnnExpr Name (Set Name) -> AnnExpr (Name, Level) Level
freeToLevelExpr level env (free, ANum n) = (0, ANum n)
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
freeToLevelExpr level env (free, ACase expr alts) =
    (freeSetToLevel env free, ACase expr' alts')
    where
        expr'@(exprLevel, _) = freeToLevelExpr level env expr
        alts' = map mapAlt alts

        mapAlt (tag, args, altExpr) =
            (tag, args', altExpr')
            where
                args' = [(arg, exprLevel) | arg <- args]
                env' = Map.union (Map.fromList args') env
                altExpr' = freeToLevelExpr level env' altExpr


freeSetToLevel :: Map Name Level -> Set Name -> Level
freeSetToLevel env free =
    foldl max 0 $ [ case Map.lookup var env of
        Just level -> level
        Nothing -> 0 | var <- (Set.toList free)]


identifyMFEs :: AnnProgram (Name, Level) Level -> Program (Name, Level)
identifyMFEs scs = [(name, [], identifyMFEsExpr 0 expr) | (name, [], expr) <- scs]


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
        notMFECandidate _ = False

        transformMFE level expr = ELet False [(("v", level), expr)] (EVar "v")


identifyMFEsExpr1 :: Level -> AnnExpr' (Name, Level) Level -> Expr (Name, Level)
identifyMFEsExpr1 level (ANum n) = ENum n
identifyMFEsExpr1 level (AVar v) = EVar v
identifyMFEsExpr1 level (AConstr t a) = EConstr t a
identifyMFEsExpr1 level (AAp e1 e2) = EAp (identifyMFEsExpr level e1) (identifyMFEsExpr level e2)
identifyMFEsExpr1 level (ALam args@[(name, argLevel)] expr) = ELam args (identifyMFEsExpr argLevel expr)
identifyMFEsExpr1 level (ALet isRec defns expr) =
    ELet isRec defns' expr'
    where
        defns' = [((name, defnLevel), identifyMFEsExpr defnLevel rhs) | ((name, defnLevel), rhs) <- defns]
        expr' = identifyMFEsExpr level expr
identifyMFEsExpr1 level (ACase expr@(exprLevel, _) alts) =
    ECase expr' alts'
    where
        expr' = identifyMFEsExpr level expr
        alts' = [(tag, args, identifyMFEsExpr level body) | (tag, args, body@(bodyLevel, _)) <- alts]


renameL :: Program (Name, Level) -> Program (Name, Level)
renameL = renameGen newNamesL


newNamesL :: NameSupply -> [(Name, Level)] -> (NameSupply, [(Name, Level)], Map Name Name)
newNamesL ns names =
    (ns', names2, mapping)
    where
        names0 = map fst names
        levels = map snd names
        (ns', names1) = getNames ns names0
        names2 = zip names1 levels
        mapping = Map.fromList $ zip names0 names1


mergeLambdas :: Program (Name, Level) -> Program (Name, Level)
mergeLambdas scs = [(name, args, mergeLambdasExpr expr) | (name, args, expr) <- scs]


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


float :: Program (Name, Level) -> CoreProgram
float = foldl collectFloatedSc []


collectFloatedSc :: [CoreScDefn] -> ScDefn (Name, Level) -> [CoreScDefn]
collectFloatedSc scsAcc (name, [], expr) =
    scsAcc ++ [(name, [], expr')] ++ floatedScs
    where
        (fds, expr') = floatExpr expr
        floatedScs = foldl createScs [] fds

        createScs scs (level, isRec, defns) =
            scs ++ map createSc defns

        createSc (name, defn) = (name, [], defn)


floatExpr :: Expr (Name, Level) -> (FloatedDefns, CoreExpr)
floatExpr (ENum n) = ([], ENum n)
floatExpr (EVar v) = ([], EVar v)
floatExpr (EConstr t a) = ([], EConstr t a)
floatExpr (EAp e1 e2) = (fds1 ++ fds2, EAp e1' e2')
    where
        (fds1, e1') = floatExpr e1
        (fds2, e2') = floatExpr e2
floatExpr (ELam args expr) =
    (outerFds, ELam args' $ wrap innerFds expr')
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
floatExpr (ELet isRec defns expr) =
    (defnsFds ++ [localFd] ++ exprFds, expr')
    where
        (exprFds, expr') = floatExpr expr
        (defnsFds, defns') = mapAccumL collectDefns [] defns
        localFd = (level, isRec, defns')
        ((name, level), _firstDefn) = head defns

        collectDefns defnsAcc ((name, level), rhs) =
            (rhsFds ++ defnsAcc, (name, rhs'))
            where
                (rhsFds, rhs') = floatExpr rhs
floatExpr (ECase expr alts) =
    (exprFds ++ altsFds, ECase expr' alts')
    where
        (exprFds, expr') = floatExpr expr

        (altsFds, alts') = mapAccumL collectAlts [] alts

        collectAlts altsAcc (tag, args, altExpr) =
            (altFds ++ altsAcc, (tag, args', altExpr'))
            where
                (altFds, altExpr') = floatExpr altExpr
                args' = map fst args

