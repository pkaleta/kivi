module LambdaLifter where


import Utils
import Common
import Data.Set (Set)
import NameSupply
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
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

type AnnPatternFunDef a b = ([a], AnnExpr a b)
type AnnDefn a b = (a, AnnExpr a b)
type AnnAlt a b = (Int, [a], AnnExpr a b)
type AnnProgram a b = [(Name, [AnnPatternFunDef a b])]
type FloatedDefns = [(Level, IsRec, [(CorePatExpr, Expr CorePatExpr)])]
type Level = Int


lambdaLift :: CoreProgram -> CoreProgram
lambdaLift = collectScs . rename . abstract . freeVars


freeVars :: CoreProgram -> AnnProgram CorePatExpr (Set Name)
freeVars [] = []
freeVars ((name, defns) : rest) = (name, defns') : (freeVars rest)
    where
        defns' = [(pattern, calcFreeVars (Set.fromList $ getVarNames pattern) expr) | (pattern, expr) <- defns]


getVarNames :: [CorePatExpr] -> [Name]
getVarNames pattern = foldl getVarNamesExpr [] pattern


getVarNamesExpr :: [Name] -> CorePatExpr -> [Name]
getVarNamesExpr names (ENum n) = names
getVarNamesExpr names (EVar v) = v : names
getVarNamesExpr names (EAp e1 e2) = (getVarNamesExpr names e1) ++ (getVarNamesExpr names e2) ++ names
getVarNamesExpr names (EConstr t a) = names
getVarNamesExpr names _ = error "Invalid pattern"


calcFreeVars :: (Set Name) -> CoreExpr -> AnnExpr (PatExpr Name) (Set Name)
calcFreeVars localVars (ENum n) = (Set.empty, ANum n)
calcFreeVars localVars (EVar v) | Set.member v localVars = (Set.singleton v, AVar v)
                                | otherwise = (Set.empty, AVar v)
calcFreeVars localVars (EAp e1 e2) = (Set.union s1 s2, AAp ae1 ae2)
    where
        ae1@(s1, _) = calcFreeVars localVars e1
        ae2@(s2, _) = calcFreeVars localVars e2
calcFreeVars localVars (ELam pattern expr) = (Set.difference fvs patternSet, ALam pattern expr')
    where
        expr'@(fvs, _) = calcFreeVars (Set.union localVars patternSet) expr
        patternSet = Set.fromList $ getVarNames pattern
calcFreeVars localVars (ELet isRec defns expr) =
    (Set.union bodyFvs defnsFvs, ALet isRec defns' expr')
    where
        binders = Set.fromList $ getVarNames $ bindersOf defns
        exprLvs = Set.union binders localVars
        rhsLvs | isRec = exprLvs
               | otherwise = localVars
        -- annotated stuff
        rhss' = map (calcFreeVars rhsLvs) $ rhssOf defns
        defns' = zip (bindersOf defns) rhss'
        expr' = calcFreeVars exprLvs expr
        rhssFvs = foldl Set.union Set.empty (map freeVarsOf rhss')
        defnsFvs | isRec = Set.difference rhssFvs binders
                 | otherwise = rhssFvs
        bodyFvs = Set.difference (freeVarsOf expr') binders
calcFreeVars localVars (ECase expr alts) =
    (fvs, ACase expr' alts')
    where
        expr'@(exprFvs, _) = calcFreeVars localVars expr
        (fvs, alts') = mapAccumL freeVarsAlts exprFvs alts

        freeVarsAlts fvs (t, pattern, body) =
            (Set.union fvs (Set.difference bodyFvs varsSet), (t, pattern, body'))
            where
                body'@(bodyFvs, _) = calcFreeVars (Set.union varsSet localVars) body
                varsSet = Set.fromList $ getVarNames pattern
calcFreeVars localVars (EConstr t n) =
    (Set.empty, AConstr t n)


abstract :: AnnProgram (PatExpr Name) (Set Name) -> CoreProgram
abstract [] = []
abstract ((name, defns) : rest) = (name, defns') : (abstract rest)
    where
        defns' = [(pattern, abstractExpr expr) | (pattern, expr) <- defns]


abstractExpr :: AnnExpr (PatExpr Name) (Set Name) -> CoreExpr
abstractExpr (freeVars, ANum n) = ENum n
abstractExpr (freeVars, AVar v) = EVar v
abstractExpr (freeVars, AAp e1 e2) = EAp (abstractExpr e1) (abstractExpr e2)
abstractExpr (freeVars, ALet isRec defns expr) =
    ELet isRec [(name, abstractExpr body) | (name, body) <- defns] (abstractExpr expr)
abstractExpr (freeVars, ALam pattern expr) =
    foldl EAp sc freeVarsList
    where
        freeVarsList = map EVar $ Set.toList freeVars
        sc = ELet False [(EVar "sc", scBody)] (EVar "sc")
        scBody = ELam (freeVarsList ++ pattern) (abstractExpr expr)
abstractExpr (freeVars, ACase expr alts) =
    ECase (abstractExpr expr) alts'
    where
        alts' = map abstractAlt alts
        abstractAlt (t, vars, expr) = (t, vars, abstractExpr expr)
abstractExpr (freeVars, AConstr t a) = EConstr t a


rename :: CoreProgram -> CoreProgram
rename = renameGen newNames


newNames :: NameSupply -> [CorePatExpr] -> (NameSupply, [CorePatExpr], Map Name Name)
newNames ns pattern = (ns, pattern', mapping)
    where ((ns, mapping), pattern') = mapAccumL newNamesExpr (ns, Map.empty) pattern


newNamesExpr :: (NameSupply, Map Name Name) -> CorePatExpr -> ((NameSupply, Map Name Name), CorePatExpr)
newNamesExpr (ns, mapping) (ENum n) = ((ns, mapping), (ENum n))
newNamesExpr (ns, mapping) (EVar v) = ((ns', mapping'), (EVar v'))
    where
        (ns', v') = getName ns v
        mapping' = Map.insert v v' mapping


newNamesExpr (ns, mapping) (EAp e1 e2) =
    ((ns2, mapping2), EAp e1' e2')
    where
        ((ns1, mapping1), e1') = newNamesExpr (ns, mapping) e1
        ((ns2, mapping2), e2') = newNamesExpr (ns1, mapping1) e2
newNamesExpr (ns, mapping) (EConstr t a) = ((ns, mapping), EConstr t a)


-- generic renaming function

renameGen :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
          -> Program a
          -> Program a
renameGen newNamesFun scs = snd $ mapAccumL (renameSc newNamesFun) initialNameSupply scs


renameSc :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
         -> NameSupply
         -> ScDefn a
         -> (NameSupply, ScDefn a)
renameSc newNamesFun ns (name, defns) =
    (ns', (name, defns'))
    where
        (ns', defns') = mapAccumL renameDefn ns defns

--renameDefn :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
--            -> NameSupply
--            -> ([a], Expr Name)
--            -> (NameSupply, ([a], Expr Name))
        renameDefn ns (pattern, expr) =
            (ns2, (pattern', expr'))
            where
                (ns1, pattern', mapping) = newNamesFun ns pattern
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


collectScs :: CoreProgram -> CoreProgram
collectScs scs = foldl collectSc [] scs


collectSc :: [CoreScDefn] -> CoreScDefn -> [CoreScDefn]
collectSc scsAcc (name, defns) =
    [(name, defns')] ++ scsAcc ++ scs
    where
        (scs, defns') = mapAccumL collectScDefn [] defns

        -- eliminating let(rec) bindings in case they define only one lambda abstraction
        collectScDefn scsAcc (pattern, expr) =
            (scs ++ scsAcc, (pattern', expr'))
            where
                (pattern', (scs, expr')) = case expr of
                    (ELet isRec [(scName, (ELam lamPattern lamExpr))] letBody) ->
                        (lamPattern, collectExpr lamExpr)
                    expr ->
                        (pattern, collectExpr expr)


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
        (scDefns, varDefns) = partition isSc defns'
        -- supercombinators declared locally in defns as lambda abstractions
        localScs = [(name, [(pattern, expr)]) | (EVar name, ELam pattern expr) <- scDefns]
        (exprScs, expr') = collectExpr expr

        -- is supercombinator predicate
        isSc (pattern, (ELam _ _)) = True
        isSc (pattern, _) = False

        -- helper to extract supercombinators nested in definitions
        collectDef (scsAcc, defnsAcc) (patExpr, expr) =
            case collectExpr expr of
                ([(scName1, defns)], (EVar scName2)) | scName1 == scName2 ->
                    (scsAcc ++ [(scName1, defns)], defnsAcc)
                (scs, expr') ->
                    (scsAcc ++ scs, (patExpr, expr') : defnsAcc)

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


freeVarsOf :: AnnExpr (PatExpr Name) (Set Name) -> Set Name
freeVarsOf (fvs, _) = fvs


------------------ lazy lambda lifter


lazyLambdaLift :: CoreProgram -> CoreProgram
lazyLambdaLift = float . mergeLambdas . renameL . identifyMFEs . annotateLevels . separateLambdas


separateLambdas :: CoreProgram -> CoreProgram
separateLambdas [] = []
separateLambdas ((name, defns) : rest) =
    (name, defns') : separateLambdas rest
    where
        defns' = [([], mkSepArgs pattern $ separateLambdasExpr expr) | (pattern, expr) <- defns]


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
    ELet isRec defns' (separateLambdasExpr body)
    where
        defns' = [(name, separateLambdasExpr expr) | (name, expr) <- defns]


mkSepArgs :: [CorePatExpr] -> CoreExpr -> CoreExpr
mkSepArgs args expr = foldr mkELam expr args
    where
        mkELam arg expr = ELam [arg] expr


annotateLevels :: CoreProgram -> AnnProgram (CorePatExpr, Level) Level
annotateLevels = freeToLevel . freeVars


freeToLevel :: AnnProgram CorePatExpr (Set Name) -> AnnProgram (CorePatExpr, Level) Level
freeToLevel [] = []
freeToLevel ((name, defns) : scs) =
    (name, defns') : freeToLevel scs
    where
        defns' = [([], freeToLevelExpr 0 Map.empty expr) | ([], expr) <- defns]


freeToLevelExpr :: Level -> Map Name Level -> AnnExpr CorePatExpr (Set Name) -> AnnExpr (CorePatExpr, Level) Level
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
freeToLevelExpr level env (free, ALam pattern expr) =
    (freeSetToLevel env free, ALam pattern' expr')
    where
        expr' = freeToLevelExpr level' (Map.union localEnv env) expr
        localEnv = Map.fromList [(v, level') | v <- getVarNames pattern]
        pattern' = [(patExpr, level') | patExpr <- pattern]
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

        binderNames = [(name, maxRhsLevel) | name <- getVarNames binders]
        exprEnv = Map.union (Map.fromList binderNames) env

        rhssEnv | isRec = exprEnv
                | otherwise = env

        rhssLevelEnv | isRec = Map.union (Map.fromList [(name, 0) | name <- getVarNames binders]) env
                     | otherwise = env

        -- helper function to collect free variables from right had side
        -- expressions in definitions
        collectFreeVars freeVars (free, rhs) = Set.union freeVars free

        -- collect only evars and map them to their var name
        collectVar vars ((EVar v), level) = (v, level) : vars
        collectVar vars _ = vars
freeToLevelExpr level env (free, ACase expr alts) =
    (freeSetToLevel env free, ACase expr' alts')
    where
        expr'@(exprLevel, _) = freeToLevelExpr level env expr
        alts' = map mapAlt alts

        mapAlt (tag, pattern, altExpr) =
            (tag, pattern', altExpr')
            where
                pattern' = [(patExpr, exprLevel) | patExpr <- pattern]
                vars = [(name, exprLevel) | name <- getVarNames pattern]
                env' = Map.union (Map.fromList vars) env
                altExpr' = freeToLevelExpr level env' altExpr


freeSetToLevel :: Map Name Level -> Set Name -> Level
freeSetToLevel env free =
    foldl max 0 $ [case Map.lookup var env of
        Just level -> level
        Nothing -> 0 | var <- (Set.toList free)]


identifyMFEs :: AnnProgram (CorePatExpr, Level) Level -> Program (CorePatExpr, Level)
identifyMFEs [] = []
identifyMFEs ((name, defns) : scs) =
    (name, defns') : identifyMFEs scs
    where
        defns' = [([], identifyMFEsExpr 0 expr) | ([], expr) <- defns]


identifyMFEsExpr :: Level -> AnnExpr (CorePatExpr, Level) Level -> Expr (CorePatExpr, Level)
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

        transformMFE level expr = ELet False [((EVar "v", level), expr)] (EVar "v")


identifyMFEsExpr1 :: Level -> AnnExpr' (CorePatExpr, Level) Level -> Expr (CorePatExpr, Level)
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


renameL :: Program (CorePatExpr, Level) -> Program (CorePatExpr, Level)
renameL = renameGen newNamesL


newNamesL :: NameSupply -> [(CorePatExpr, Level)] -> (NameSupply, [(CorePatExpr, Level)], Map Name Name)
newNamesL ns pattern = (ns', pattern1, mapping)
    where
        (ns', pattern0, mapping) = newNames ns $ map fst pattern
        pattern1 = zip pattern0 $ map snd pattern


mergeLambdas :: Program (CorePatExpr, Level) -> Program (CorePatExpr, Level)
mergeLambdas [] = []
mergeLambdas ((name, defns) : scs) =
    (name, defns') : mergeLambdas scs
    where
        defns' = [(pattern, mergeLambdasExpr expr) | (pattern, expr) <- defns]


mergeLambdasExpr :: Expr (CorePatExpr, Level) -> Expr (CorePatExpr, Level)
mergeLambdasExpr (ELam args expr) =
    case expr' of
        (ELam args' innerExpr) ->
            ELam (args ++ args') innerExpr
        _ ->
            ELam args expr'
    where
        expr' = mergeLambdasExpr expr
mergeLambdasExpr expr = expr


float :: Program (CorePatExpr, Level) -> CoreProgram
float = foldl collectFloatedSc []


collectFloatedSc :: [CoreScDefn] -> ScDefn (CorePatExpr, Level) -> [CoreScDefn]
collectFloatedSc scsAcc (name, defns) = scsAcc ++ [(name, defns')] ++ scs
    where
        (scs, defns') = mapAccumL collectFloatedScDefn [] defns


collectFloatedScDefn :: [CoreScDefn] -> PatternFunDef (CorePatExpr, Level) -> ([CoreScDefn], PatternFunDef CorePatExpr)
collectFloatedScDefn scsAcc ([], expr) =
    (scsAcc ++ floatedScs, ([], expr'))
    where
        (fds, expr') = floatExpr expr
        floatedScs = foldl createScs [] fds

        createScs scs (level, isRec, defns) =
            scs ++ map createSc defns

        createSc (EVar name, defn) = (name, [([], defn)])


floatExpr :: Expr (CorePatExpr, Level) -> (FloatedDefns, CoreExpr)
floatExpr (ENum n) = ([], ENum n)
floatExpr (EVar v) = ([], EVar v)
floatExpr (EConstr t a) = ([], EConstr t a)
floatExpr (EAp e1 e2) = (fds1 ++ fds2, EAp e1' e2')
    where
        (fds1, e1') = floatExpr e1
        (fds2, e2') = floatExpr e2
floatExpr (ELam pattern expr) =
    (outerFds, ELam pattern' $ wrap innerFds expr')
    where
        pattern' = [patExpr | (patExpr, level) <- pattern]
        (patExpr, curLevel) = head pattern
        (fdBody, expr') = floatExpr expr
        (innerFds, outerFds) = partition checkLevel fdBody

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
        ((patExpr, level), _firstDefn) = head defns

        collectDefns defnsAcc ((patExpr, level), rhs) =
            (rhsFds ++ defnsAcc, (patExpr, rhs'))
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

