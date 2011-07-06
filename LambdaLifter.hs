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
                  | ACaseSimple (AnnExpr a b) [AnnAlt a b]
                  | ACaseConstr (AnnExpr a b) [AnnAlt a b]
                  | ALam [a] (AnnExpr a b)
                  | ASelect Int Int a
                  | AError String
    deriving Show

type AnnDefn a b = (a, AnnExpr a b)
type AnnAlt a b = (Int, AnnExpr a b)
type AnnProgram a b = [(Name, [a], AnnExpr a b)]


lambdaLift :: CoreProgram -> CoreProgram
lambdaLift (adts, scs) = (adts, collectScs . rename . abstract . freeVars $ scs)


freeVars :: [CoreScDefn] -> AnnProgram Name (Set Name)
freeVars [] = []
freeVars ((name, args, expr) : scs) = (name, args, calcFreeVars (Set.fromList args) expr) : (freeVars scs)


calcFreeVars :: (Set Name) -> CoreExpr -> AnnExpr Name (Set Name)
calcFreeVars localVars (ENum n) = (Set.empty, ANum n)
calcFreeVars localVars (EVar v) | Set.member v localVars = (Set.singleton v, AVar v)
                                | otherwise              = (Set.empty, AVar v)
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
calcFreeVars localVars (ECaseSimple expr alts) = calcFreeVarsCase ACaseSimple localVars expr alts
calcFreeVars localVars (ECaseConstr expr alts) = calcFreeVarsCase ACaseConstr localVars expr alts
calcFreeVars localVars (EConstr t n) =
    (Set.empty, AConstr t n)
calcFreeVars localVars (ESelect r i name) | Set.member name localVars = (Set.singleton name, ASelect r i name)
                                          | otherwise                 = (Set.empty, ASelect r i name)
calcFreeVars localVars (EError msg) = (Set.empty, AError msg)


calcFreeVarsCase :: ((AnnExpr Name (Set Name)) -> [AnnAlt Name (Set Name)] -> AnnExpr' Name (Set Name))
                 -> (Set Name)
                 -> CoreExpr
                 -> [CoreAlt]
                 -> AnnExpr Name (Set Name)
calcFreeVarsCase constr localVars expr alts = (fvs, constr expr' alts')
    where
        expr'@(exprFvs, _) = calcFreeVars localVars expr
        (fvs, alts') = mapAccumL freeVarsAlts exprFvs alts

        freeVarsAlts fvs (t, body) =
            (Set.union fvs bodyFvs, (t, body'))
            where
                body'@(bodyFvs, _) = calcFreeVars localVars body


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
abstractExpr (freeVars, ACaseSimple expr alts) = abstractExprCase ECaseSimple freeVars expr alts
abstractExpr (freeVars, ACaseConstr expr alts) = abstractExprCase ECaseConstr freeVars expr alts
abstractExpr (freeVars, AConstr t a) = EConstr t a
abstractExpr (freeVars, ASelect r i v) = ESelect r i v
abstractExpr (freeVars, AError msg) = EError msg


abstractExprCase :: (CoreExpr -> [CoreAlt] -> CoreExpr)
                 -> (Set Name)
                 -> (AnnExpr Name (Set Name))
                 -> [(AnnAlt Name (Set Name))]
                 -> CoreExpr
abstractExprCase constr freeVars expr alts = constr (abstractExpr expr) alts'
    where
        alts' = map abstractAlt alts

        abstractAlt (t, expr) = (t, abstractExpr expr)


renameGen :: (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
          -> [ScDefn a]
          -> [ScDefn a]
renameGen newNamesFun scs = snd $ mapAccumL (renameSc newNamesFun) initialNameSupply scs


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
renameExpr newNamesFun mapping ns (ECaseSimple expr alts) = renameExprCase ECaseSimple newNamesFun mapping ns expr alts
renameExpr newNamesFun mapping ns (ECaseConstr expr alts) = renameExprCase ECaseConstr newNamesFun mapping ns expr alts
renameExpr newNamesFun mapping ns (EConstr t a) = (ns, EConstr t a)
renameExpr newNamesFun mapping ns (ESelect r i v) = 
    (ns, ESelect r i v') -- for built-int functions (+,-, etc.) we have to use old name
    where
        v' = case Map.lookup v mapping of
            (Just x) -> x
            Nothing -> v
renameExpr newNamesFun mapping ns (EError msg) = (ns, EError msg)


renameExprCase :: (Expr a -> [Alter Int a] -> Expr a)
               -> (NameSupply -> [a] -> (NameSupply, [a], Map Name Name))
               -> Map Name Name
               -> NameSupply
               -> Expr a
               -> [Alter Int a]
               -> (NameSupply, Expr a)
renameExprCase constr newNamesFun mapping ns expr alts =
    (ns2, constr expr' alts')
    where
        (ns1, expr') = renameExpr newNamesFun mapping ns expr
        (ns2, alts') = mapAccumL (renameAlt mapping) ns1 alts

        renameAlt mapping ns (t, body) =
            (ns', (t, body'))
            where
                (ns', body') = renameExpr newNamesFun mapping ns1 body


rename :: [CoreScDefn] -> [CoreScDefn]
rename = renameGen newNames


newNames :: NameSupply -> [Name] -> (NameSupply, [Name], Map Name Name)
newNames ns names =
    (ns', names', mapping)
    where
        (ns', names') = getNames ns names
        mapping = Map.fromList $ zip names names'


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
collectExpr (ECaseSimple expr alts) = collectExprCase ECaseSimple expr alts
collectExpr (ECaseConstr expr alts) = collectExprCase ECaseConstr expr alts
collectExpr (EConstr t a) = ([], EConstr t a)
collectExpr (ESelect r i v) = ([], ESelect r i v)
collectExpr (EError msg) = ([], EError msg)


collectExprCase :: (CoreExpr -> [CoreAlt] -> CoreExpr)
                -> CoreExpr
                -> [CoreAlt]
                -> ([CoreScDefn], CoreExpr)
collectExprCase constr expr alts =
    (exprScs ++ altsScs, constr expr' alts')
    where
        (exprScs, expr') = collectExpr expr
        (altsScs, alts') = mapAccumL collectAlt [] alts

        collectAlt scs (t, expr) =
            (scs ++ exprScs, (t, expr'))
            where (exprScs, expr') = collectExpr expr


freeVarsOf :: AnnExpr Name (Set Name) -> Set Name
freeVarsOf (fvs, _) = fvs

