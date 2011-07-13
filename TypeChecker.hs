module TypeChecker where


import Common
import Data.Map as Map
import Data.Set as Set
import NameSupply
import Data.List
import Debug.Trace


type TypeVarName = String
type TypeEnv = Map Name TypeExpr
type NonGenericSet = Set TypeVarName
data TypeExpr = TypeVar TypeVarName (Maybe TypeExpr) | TypeOp String [TypeExpr]


instance Show TypeExpr where
    show = showTypeExpr

instance Eq TypeExpr where
    (TypeVar tvn inst) == (TypeVar tvn' inst') = tvn == tvn' && inst == inst'
    (TypeOp ton args) == (TypeOp ton' args') = ton == ton' && args == args'


type TypedExpr a = (TypeExpr, TypedExpr' a)

data TypedExpr' a = TVar Name
                  | TNum Int
                  | TConstr Int Int
                  | TAp (TypedExpr a) (TypedExpr a)
                  | TLet IsRec [TypedDefn a] (TypedExpr a)
                  | TCase (TypedExpr a) [TypedAlt a]
                  | TCaseSimple (TypedExpr a) [TypedAlt a]
                  | TCaseConstr (TypedExpr a) [TypedAlt a]
                  | TLam [a] (TypedExpr a)
                  | TSelect Int Int a
                  | TError String
    deriving Show

type TypedDefn a = (a, TypedExpr a)
type TypedAlt a = (Int, TypedExpr a)
data TypedScDefn a = TypedScDefn Name [a] (TypedExpr a)
    deriving Show
type TypedProgram a = ([DataType], [TypedScDefn a])


showTypeExpr :: TypeExpr -> String
showTypeExpr (TypeVar tvn inst) =
    case inst of
        Just tExpr -> show tExpr
        Nothing    -> tvn
showTypeExpr (TypeOp ton args) =
    case args of
        []       -> ton
        [t1, t2] -> show t1 ++ " " ++ ton ++ " " ++ show t2


arrow :: TypeExpr -> TypeExpr -> TypeExpr
arrow t1 t2 = TypeOp "->" [t1, t2]


int :: TypeExpr
int = TypeOp "int" []


bool :: TypeExpr
bool = TypeOp "bool" []


cross :: TypeExpr -> TypeExpr -> TypeExpr
cross t1 t2 = TypeOp "cross" [t1, t2]


list :: TypeExpr -> TypeExpr
list t = TypeOp "list" [t]


typeCheck :: CoreProgram -> TypedProgram Name
typeCheck (adts, scs) = (adts, scs')
    where ((ns', env', nonGeneric'), scs') = mapAccumL typeCheckSc (initialNameSupply, Map.empty, Set.empty) scs


typeCheckSc :: (NameSupply, TypeEnv, NonGenericSet)
            -> CoreScDefn
            -> ((NameSupply, TypeEnv, NonGenericSet), TypedScDefn Name)
typeCheckSc (ns, env, nonGeneric) (ScDefn name args expr) = (accs, TypedScDefn name args expr')
    where (accs, expr') = typeCheckExpr ns env nonGeneric expr


typeCheckExpr :: NameSupply
              -> TypeEnv
              -> NonGenericSet
              -> CoreExpr
              -> ((NameSupply, TypeEnv, NonGenericSet), TypedExpr Name)
typeCheckExpr ns env nonGeneric (EVar v) = ((ns', env, nonGeneric), (typeExpr, TVar v))
    where (ns', typeExpr) = getType ns env nonGeneric v
typeCheckExpr ns env nonGeneric (ENum n) = ((ns, env, nonGeneric), (int, TNum n))
typeCheckExpr ns env nonGeneric (EAp e1 e2) = ((ns2, env1, nonGeneric1), (resType', TAp (funType', e1') (argType', e2')))
    where
        ((ns0, env0, nonGeneric0), (funType, e1')) = typeCheckExpr ns env nonGeneric e1
        ((ns1, env1, nonGeneric1), (argType, e2')) = typeCheckExpr ns0 env0 nonGeneric0 e2
        (ns2, resType) = newTypeVariable ns
        (TypeOp ton [argType', resType'], funType') = unify (argType `arrow` resType) funType
-- Here we assume that lambdas has already been split and contain one argument only
typeCheckExpr ns env nonGeneric lambda@(ELam [v] expr) = ((ns2, env2, nonGeneric2), (resType, TLam [v] typedExpr))
    where
        (ns1, argType@(TypeVar tvn inst)) = newTypeVariable ns
        env1 = Map.insert v argType env
        nonGeneric1 = Set.insert tvn nonGeneric
        ((ns2, env2, nonGeneric2), typedExpr@(exprType, expr')) = typeCheckExpr ns1 env1 nonGeneric1 expr
        resType = argType `arrow` exprType
typeCheckExpr ns env nonGeneric expr@(ELet False defns body) = typeCheckLet ns env nonGeneric expr
typeCheckExpr ns env nonGeneric expr@(ELet True defns body) = typeCheckLetrec ns env nonGeneric expr


typeCheckLet :: NameSupply
             -> TypeEnv
             -> NonGenericSet
             -> CoreExpr
             -> ((NameSupply, TypeEnv, NonGenericSet), TypedExpr Name)
typeCheckLet ns env nonGeneric (ELet False defns expr) = (accs, (exprType, TLet False defns' typedExpr))
    where
        ((ns1, env1, nonGeneric1), defns') = mapAccumL typeCheckDefn (ns, env, nonGeneric) defns
        (accs, typedExpr@(exprType, expr')) = typeCheckExpr ns1 env1 nonGeneric1 expr


typeCheckLetrec :: NameSupply
                -> TypeEnv
                -> NonGenericSet
                -> CoreExpr
                -> ((NameSupply, TypeEnv, NonGenericSet), TypedExpr Name)
typeCheckLetrec ns env nonGeneric (ELet True defns expr) = (accs, (exprType, TLet True defns' typedExpr))
    where
        (ns1, env1, nonGeneric1) = foldl collectDefn (ns, env, nonGeneric) defns
        ((ns2, env2, nonGeneric2), defns') = mapAccumL typeCheckRecDefn (ns1, env1, nonGeneric1) defns
        (accs, typedExpr@(exprType, expr')) = typeCheckExpr ns2 env2 nonGeneric2 expr

        collectDefn (ns, env, nonGeneric) (v, defn) = (ns', env', nonGeneric')
            where
                (ns', tv@(TypeVar tvn inst)) = newTypeVariable ns
                env' = Map.insert v tv env
                nonGeneric' = Set.insert tvn nonGeneric


typeCheckDefn :: (NameSupply, TypeEnv, NonGenericSet)
              -> CoreDefn
              -> ((NameSupply, TypeEnv, NonGenericSet), TypedDefn Name)
typeCheckDefn (ns, env, nonGeneric) (v, defn) = ((ns', env2, nonGeneric'), (v, typedDefn))
    where
        ((ns', env1, nonGeneric'), typedDefn@(defnType, defn')) = typeCheckExpr ns env nonGeneric defn
        env2 = Map.insert v defnType env1


typeCheckRecDefn :: (NameSupply, TypeEnv, NonGenericSet)
                 -> CoreDefn
                 -> ((NameSupply, TypeEnv, NonGenericSet), TypedDefn Name)
typeCheckRecDefn (ns, env, nonGeneric) (v, defn) = ((ns', env2, nonGeneric'), (v, typedDefn))
    where
        ((ns', env1, nonGeneric'), typedDefn@(defnType, defn')) = typeCheckExpr ns env nonGeneric defn

        (Just varType) = Map.lookup v env
        (varType', defnType') = unify varType defnType

        env2 = Map.insert v varType' env1


getType :: NameSupply
        -> TypeEnv
        -> NonGenericSet
        -> Name
        -> (NameSupply, TypeExpr)
getType ns env nonGeneric v =
    case Map.lookup v env of
        (Just te) -> fresh ns nonGeneric te
        Nothing  -> error $ "Undefined symbol: " ++ v


fresh :: NameSupply -> NonGenericSet -> TypeExpr -> (NameSupply, TypeExpr)
fresh ns nonGeneric te = (ns', te')
    where ((ns', env, _), te') = fresh' (ns, Map.empty, nonGeneric) te


fresh' :: (NameSupply, TypeEnv, NonGenericSet)
       -> TypeExpr
       -> ((NameSupply, TypeEnv, NonGenericSet), TypeExpr)
fresh' (ns, env, nonGeneric) te =
    case prune te of
        typeVar@(TypeVar tvn inst) -> freshVar ns env nonGeneric typeVar
        typeOp@(TypeOp ton args)   -> freshOper ns env nonGeneric typeOp


freshVar :: NameSupply
         -> TypeEnv
         -> NonGenericSet
         -> TypeExpr
         -> ((NameSupply, TypeEnv, NonGenericSet), TypeExpr)
freshVar ns env nonGeneric tv@(TypeVar tvn inst) =
    case isGeneric nonGeneric tvn of
        True  -> ((ns', env', nonGeneric), tv')
        False -> ((ns, env, nonGeneric), tv)
    where
        (ns', tv') = newTypeVariable ns
        env' = Map.insert tvn tv' env


freshOper :: NameSupply
          -> TypeEnv
          -> NonGenericSet
          -> TypeExpr
          -> ((NameSupply, TypeEnv, NonGenericSet), TypeExpr)
freshOper ns env nonGeneric (TypeOp ton args) = (accs, TypeOp ton args')
    where
        (accs, args') = mapAccumL fresh' (ns, env, nonGeneric) args


isGeneric :: NonGenericSet -> TypeVarName -> Bool
isGeneric nonGeneric tvn = not $ Set.member tvn nonGeneric


newTypeVariable :: NameSupply -> (NameSupply, TypeExpr)
newTypeVariable ns = (ns', TypeVar name Nothing)
    where
        (ns', name) = getName ns "t"


-- TODO: prune should also get rid of long instantiated variable chains, thus
-- should update the environment
prune :: TypeExpr -> TypeExpr
prune typeVar@(TypeVar v (Just inst)) = prune inst
prune typeVar@(TypeVar v Nothing)     = typeVar
prune typeOp@(TypeOp op args)         = typeOp


unify :: TypeExpr -> TypeExpr -> (TypeExpr, TypeExpr)
unify te1 te2 = unify' (prune te1) (prune te2)


unify' :: TypeExpr -> TypeExpr -> (TypeExpr, TypeExpr)
unify' tv@(TypeVar tvn inst) te | occursInType tv te = error "Recursive unification"
                                | otherwise          = (TypeVar tvn $ Just te, te)
unify' to@(TypeOp ton args) tv@(TypeVar tvn inst) = unify' tv to
unify' to1@(TypeOp n1 as1) to2@(TypeOp n2 as2) =
    case n1 /= n2 || length as1 /= length as2 of
        True -> error $ "Type mismatch: " ++ show to1 ++ " and " ++ show to2
        False -> (TypeOp n1 a1', TypeOp n2 a2')
            where
                (a1', a2') = unzip [unify' a1 a2 | (a1, a2) <- zip as1 as2]


occursInType :: TypeExpr -> TypeExpr -> Bool
occursInType tv@(TypeVar tvn inst) te =
    case prune te of
        (TypeVar tvn' inst') | tvn == tvn' && inst == inst' -> True
        (TypeOp ton args)                                   -> occursInArgs tv args
        _                                                   -> False


occursInArgs :: TypeExpr -> [TypeExpr] -> Bool
occursInArgs tv@(TypeVar tvn inst) typeExprs = or [occursInType tv te | te <- typeExprs]

