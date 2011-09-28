module TypeChecker(typeCheck) where


import Common
import Data.Map as Map hiding (map)
import Data.Set as Set hiding (map)
import NameSupply
import Data.List
import Debug.Trace
import AbstractDataTypes


type TypeVarName = String
type TypeEnv = Map Name TypeExpr
type TypeInstanceEnv = Map TypeVarName TypeExpr
type NonGeneric = Set TypeVarName
data State = State { nameSupply :: NameSupply
                   , typeInstanceEnv :: TypeInstanceEnv }
    deriving Show

data TypeExpr = TypeVar TypeVarName (Maybe TypeExpr)
              | TypeOp String [TypeExpr]


instance Eq TypeExpr where
    (TypeVar tvn inst) == (TypeVar tvn' inst') = tvn == tvn' && inst == inst'
    (TypeOp ton args) == (TypeOp ton' args') = ton == ton' && args == args'


instance Show TypeExpr where
    show = showTypeExpr


type TypedExpr a = (TypeExpr, TypedExpr' a)


data TypedExpr' a = TVar Name
                  | TNum Int
                  | TChar Int
                  | TConstr Int Int
                  | TAp (TypedExpr a) (TypedExpr a)
                  | TLet IsRec [TypedDefn a] (TypedExpr a)
                  | TCase (TypedExpr a) [TypedAlt a]
                  | TCaseSimple (TypedExpr a) [TypedAlt a]
                  | TCaseConstr (TypedExpr a) [TypedAlt a]
                  | TLam [a] (TypedExpr a)
                  | TSelect Int Int Name
                  | TError String
    deriving Show


type TypedDefn a = (a, TypedExpr a)
type TypedAlt a = (Int, TypedExpr a)
data TypedScDefn a = TypedScDefn Name [TypedExpr a] (TypedExpr a)
    deriving Show
type TypedProgram a = ([DataType], [TypedScDefn a])


showTypeExpr :: TypeExpr -> String
showTypeExpr (TypeVar name inst) =
    case inst of
        Just te -> showTypeExpr te
        Nothing -> name
showTypeExpr (TypeOp name []) = name
showTypeExpr (TypeOp "list" [t]) = "[" ++ showTypeExpr t ++ "]"
showTypeExpr (TypeOp name [t1, t2]) = showTypeExpr t1 ++ " " ++ name ++ " " ++ showTypeExpr t2

showTypeExprDbg :: State -> TypeExpr -> String
showTypeExprDbg state (TypeVar name Nothing) =
    case Map.lookup name $ typeInstanceEnv state of
        Just te -> showTypeExprDbg state te
        Nothing -> name
showTypeExprDbg state (TypeOp name []) = name
showTypeExprDbg state (TypeOp "list" [t]) = "[" ++ showTypeExprDbg state t ++ "]"
showTypeExprDbg state (TypeOp name [t1, t2]) = showTypeExprDbg state t1 ++ " " ++ name ++ " " ++ showTypeExprDbg state t2


arrow :: TypeExpr -> TypeExpr -> TypeExpr
arrow t1 t2 = TypeOp "->" [t1, t2]


int :: TypeExpr
int = TypeOp "int" []


bool :: TypeExpr
bool = TypeOp "bool" []


char :: TypeExpr
char = TypeOp "char" []


cross :: TypeExpr -> TypeExpr -> TypeExpr
cross t1 t2 = TypeOp "cross" [t1, t2]


list :: TypeExpr -> TypeExpr
list t = TypeOp "list" [t]


updateInstances :: State -> [TypedScDefn Name] -> [TypedScDefn Name]
updateInstances state scs =
     [TypedScDefn name (updateArgs state args) $ updateExpr state expr | (TypedScDefn name args expr) <- scs]


updateArgs :: State -> [TypedExpr Name] -> [TypedExpr Name]
updateArgs state args = [(updateType state typeExpr, expr) | (typeExpr, expr) <- args]


updateType :: State -> TypeExpr -> TypeExpr
updateType state tv@(TypeVar name Nothing) =
    case Map.lookup name $ typeInstanceEnv state of
        (Just t) -> updateType state t
        Nothing  -> tv
updateType state (TypeOp name args) = TypeOp name $ map (updateType state) args


updateExpr :: State -> TypedExpr Name -> TypedExpr Name
updateExpr state (te, TVar v) = (updateType state te, TVar v)
updateExpr state (te, TChar c) = (updateType state te, TChar c)
updateExpr state (te, TNum n) = (updateType state te, TNum n)
updateExpr state (te, TAp e1 e2) = (updateType state te, TAp e1' e2')
    where
        e1' = updateExpr state e1
        e2' = updateExpr state e2
updateExpr state (te, TLet isRec defns expr) = (updateType state te, TLet isRec defns' expr')
    where
        defns' = [(name, updateExpr state expr) | (name, expr) <- defns]
        expr' = updateExpr state expr
updateExpr state (te, TCaseSimple expr alts) = (updateType state te, updateCase state TCaseSimple expr alts)
updateExpr state (te, TCaseConstr expr alts) = (updateType state te, updateCase state TCaseConstr expr alts)
updateExpr state (te, expr@(TSelect r i name)) = (updateType state te, expr)
updateExpr state (te, TLam args expr) = (updateType state te, TLam args expr')
    where
        expr' = updateExpr state expr
updateExpr state (te, TConstr nilTag arity) = (updateType state te, TConstr nilTag arity)
updateExpr state expr = error $ "updateExpr: " ++ show expr


updateCase :: State
           -> (TypedExpr Name -> [TypedAlt Name] -> TypedExpr' Name)
           -> TypedExpr Name
           -> [TypedAlt Name]
           -> TypedExpr' Name
updateCase state constr expr alts = constr expr' alts'
    where
        expr' = updateExpr state expr
        alts' = [(t, updateExpr state expr) | (t, expr) <- alts]


typeCheck :: CoreProgram -> TypedProgram Name
typeCheck (adts, scs) =
  (adts, updateInstances state1 scs')
  where
    ((state1, _), scs') = mapAccumL (typeCheckSc initialNonGeneric) initialTypeEnv scs


typeCheckSc :: NonGeneric -> (State, TypeEnv) -> CoreScDefn -> ((State, TypeEnv), TypedScDefn Name)
typeCheckSc nonGeneric (state, env) (ScDefn name args expr) =
  ((state3, env1), TypedScDefn name args' expr')
  where
    -- create a type variable to hold the type of supercombinator
    (state0, tv) = newTypeVariable state
    env0 = Map.insert name tv env
    
    -- create type variables for supercombinator arguments
    ((state1, env1), args') = mapAccumL createTypeVar (state0, env0) args
    
    -- type check supercombinator body
    (state2, expr'@(te, _)) = typeCheckExpr state1 env1 nonGeneric expr
    
    -- unify type for supercombinator
    argTypeVars = map fst args'
    scType = foldr arrow te argTypeVars
    (state3, _, _) = unify state2 tv scType


createTypeVar :: (State, TypeEnv) -> Name -> ((State, TypeEnv), TypedExpr Name)
createTypeVar (state, env) name = ((state', env'), (tv, TVar name))
    where
        (state', tv) = newTypeVariable state
        env' = Map.insert name tv env


typeCheckExpr :: State -> TypeEnv -> NonGeneric -> CoreExpr -> (State, TypedExpr Name)
typeCheckExpr state env nonGeneric (EVar v) = (state', (typeExpr, TVar v))
    where (state', typeExpr) = getType state env nonGeneric v
typeCheckExpr state env nonGeneric (ENum n) = (state, (int, TNum n))
typeCheckExpr state env nonGeneric (EChar c) = (state, (char, TChar c))
typeCheckExpr state env nonGeneric (EAp e1 e2) = (state4, (resType, TAp e1' e2'))
    where
        (state1, e1'@(funType, _)) = typeCheckExpr state env nonGeneric e1
        (state2, e2'@(argType, _)) = typeCheckExpr state1 env nonGeneric e2
        (state3, resType) = newTypeVariable state2

        (state4, _, _) = unify state3 (argType `arrow` resType) funType
typeCheckExpr state env nonGeneric expr@(ELet False defns body) =
    typeCheckLet state env nonGeneric defns body
typeCheckExpr state env nonGeneric expr@(ELet True defns body) =
    typeCheckLetrec state env nonGeneric defns body
typeCheckExpr state env nonGeneric (ECaseConstr expr alts) =
  typeCheckCase state env nonGeneric TCaseConstr expr alts
typeCheckExpr state env nonGeneric (ECaseSimple expr alts) =
  typeCheckCase state env nonGeneric TCaseSimple expr alts
typeCheckExpr state env nonGeneric constr@(EConstr _ _) = typeCheckConstr state env nonGeneric constr
typeCheckExpr state env nonGeneric (ESelect r i name) =
  (state', (typeExpr, TSelect r i name))
  where
    (state', typeExpr) = newTypeVariable state
typeCheckExpr state _ _ expr = error $ "typeCheckExpr: " ++ show expr


typeCheckCase :: State ->
                 TypeEnv ->
                 NonGeneric ->
                 (TypedExpr Name -> [TypedAlt Name] -> TypedExpr' Name) ->
                 CoreExpr ->
                 [CoreAlt] ->
                 (State, TypedExpr Name)
typeCheckCase state env nonGeneric constr expr alts =
  (state3, (firstAltType, constr expr' alts'))
  where
    (_, firstAltExpr) = head alts
    (state1, (firstAltType, _)) = typeCheckExpr state env nonGeneric firstAltExpr
    ((state2, _), alts') = mapAccumL (typeCheckAlt nonGeneric env) (state1, firstAltType) alts
    (state3, expr') = typeCheckExpr state2 env nonGeneric expr



typeCheckConstr :: State -> TypeEnv -> NonGeneric -> CoreExpr -> (State, TypedExpr Name)
typeCheckConstr state env nonGeneric (EConstr tag arity)
    | tag == nilTag =
        let (state', t) = newTypeVariable state
        in (state', (list t, TConstr nilTag arity))
    | tag == consTag =
        let (state', t) = newTypeVariable state
        in (state', (t `arrow` ((list t) `arrow` (list t)), TConstr nilTag arity))
    | tag == falseTag = (state, (bool, TConstr 0 arity))
    | tag == trueTag = (state, (bool, TConstr 0 arity))


typeCheckLet :: State -> TypeEnv -> NonGeneric -> [CoreDefn] -> CoreExpr -> (State, TypedExpr Name)
typeCheckLet state env nonGeneric defns expr = (state2, (exprType, TLet False defns' typedExpr))
    where
        ((state1, _), defns') = mapAccumL (typeCheckDefn nonGeneric) (state, env) defns
        (state2, typedExpr@(exprType, expr')) = typeCheckExpr state1 env nonGeneric expr


typeCheckDefn :: NonGeneric -> (State, TypeEnv) -> CoreDefn -> ((State, TypeEnv), TypedDefn Name)
typeCheckDefn nonGeneric (state, env) (v, defn) = ((state', env'), (v, typedDefn))
    where
        (state', typedDefn@(defnType, defn')) = typeCheckExpr state env nonGeneric defn
        env' = Map.insert v defnType env


typeCheckLetrec :: State -> TypeEnv -> NonGeneric -> [CoreDefn] -> CoreExpr -> (State, TypedExpr Name)
typeCheckLetrec state env nonGeneric defns expr = (state3, (exprType, TLet True defns' typedExpr))
   where
       (env1, nonGeneric', state1) = foldl collectDefn (env, nonGeneric, state) defns
       ((state2, env2), defns') = mapAccumL (typeCheckRecDefn nonGeneric') (state1, env1) defns
       (state3, typedExpr@(exprType, expr')) = typeCheckExpr state2 env2 nonGeneric' expr

       collectDefn (env, nonGeneric, state) (v, defn) = (env', nonGeneric', state')
           where
               (state', tv@(TypeVar name Nothing)) = newTypeVariable state
               nonGeneric' = Set.insert name nonGeneric
               env' = Map.insert v tv env


typeCheckRecDefn :: NonGeneric -> (State, TypeEnv) -> CoreDefn -> ((State, TypeEnv), TypedDefn Name)
typeCheckRecDefn nonGeneric (state, env) (v, defn) = ((state2, env), (v, typedDefn))
   where
       (state1, typedDefn@(defnType, defn')) = typeCheckExpr state env nonGeneric defn

       (Just varType) = Map.lookup v env
       (state2, _, _) = unify state1 varType defnType


typeCheckAlt :: NonGeneric -> TypeEnv -> (State, TypeExpr) -> CoreAlt -> ((State, TypeExpr), TypedAlt Name)
typeCheckAlt nonGeneric env (state, accType) (v, expr) =
  ((state2, accType), (v, typedAlt))
  where
    (state1, typedAlt@(altType, expr')) = typeCheckExpr state env nonGeneric expr
    (state2, _, _) = unify state1 accType altType


getType :: State -> TypeEnv -> NonGeneric -> Name -> (State, TypeExpr)
getType state env nonGeneric v =
  case Map.lookup v env of
    (Just te) -> (state', te)
      where
        (state', te') = fresh state nonGeneric te
    Nothing ->
      error $ "Undefined symbol: " ++ v


fresh :: State -> NonGeneric -> TypeExpr -> (State, TypeExpr)
fresh state nonGeneric te =
  (state', te')
  where
    (_, env) = initialTypeEnv
    ((state', _), te') = fresh' nonGeneric (state, env) te


fresh' :: NonGeneric -> (State, TypeEnv) -> TypeExpr -> ((State, TypeEnv), TypeExpr)
fresh' nonGeneric (state, env) te = freshType nonGeneric (state0, env) te0
    where (state0, te0) = prune state te


freshType :: NonGeneric -> (State, TypeEnv) -> TypeExpr -> ((State, TypeEnv), TypeExpr)
freshType nonGeneric (state, env) tv@(TypeVar name Nothing) =
  case isGeneric nonGeneric name of
    True  ->
      case Map.lookup name env of
        (Just tv') -> ((state, env), tv')
        Nothing    -> ((state', env'), tv')
          where
            (state', tv') = newTypeVariable state
            env' = Map.insert name tv' env
    False -> ((state, env), tv)
freshType nonGeneric (state, env) (TypeOp name args) =
  ((state', env'), TypeOp name args')
  where
    ((state', env'), args') = mapAccumL (fresh' nonGeneric) (state, env) args


isGeneric :: NonGeneric -> TypeVarName -> Bool
isGeneric nonGeneric name = not $ Set.member name nonGeneric


newTypeVariable :: State -> (State, TypeExpr)
newTypeVariable state = (state', TypeVar name Nothing)
    where
        (ns', name) = getName (nameSupply state) "t"
        state' = state { nameSupply = ns' }


prune :: State -> TypeExpr -> (State, TypeExpr)
prune state typeVar@(TypeVar name Nothing) =
    case Map.lookup name $ typeInstanceEnv state of
        (Just inst) -> (state1, inst')
            where
                (state0, inst') = prune state inst
                state1 = state0 { typeInstanceEnv = Map.insert name inst' $ typeInstanceEnv state0 }
        Nothing -> (state, typeVar)
prune state te = (state, te)


unify :: State -> TypeExpr -> TypeExpr -> (State, TypeExpr, TypeExpr)
unify state te1 te2 = unify' state2 te1' te2'
    where
        (state1, te1') = prune state te1
        (state2, te2') = prune state1 te2


unify' :: State -> TypeExpr -> TypeExpr -> (State, TypeExpr, TypeExpr)
unify' state tv@(TypeVar name Nothing) te =
    case occurs of
        True -> error "Recursive unification"
        False -> (state2, tv, te)
            where
                state2 = state1 { typeInstanceEnv = Map.insert name te $ typeInstanceEnv state1 }
    where
        (state1, occurs) = occursInType state tv te
unify' state to@(TypeOp ton args) tv@(TypeVar name Nothing) = unify' state tv to
unify' state to1@(TypeOp n1 as1) to2@(TypeOp n2 as2) =
    case n1 /= n2 || length as1 /= length as2 of
        True ->
            error $ "Type mismatch: " ++ showTypeExprDbg state to1 ++ " and " ++ showTypeExprDbg state to2
        False ->
            (state', TypeOp n1 a1', TypeOp n2 a2')
            where
                (state', a1', a2') = foldl' unifyArgs (state, [], []) $ zip as1 as2


unifyArgs :: (State, [TypeExpr], [TypeExpr])
          -> (TypeExpr, TypeExpr)
          -> (State, [TypeExpr], [TypeExpr])
unifyArgs (state, tacc1, tacc2) (te1, te2) =
    (state', tacc1 ++ [te1'], tacc2 ++ [te2'])
    where
        (state', te1', te2') = unify state te1 te2


occursInType :: State -> TypeExpr -> TypeExpr -> (State, Bool)
occursInType state tv@(TypeVar name Nothing) te =
    case pruned of
        TypeVar name' Nothing | name == name' -> (state', True)
        TypeOp ton args                       -> occursInArgs state' tv args
        _                                     -> (state', False)
    where
        (state', pruned) = prune state te


occursInArgs :: State -> TypeExpr -> [TypeExpr] -> (State, Bool)
occursInArgs state tv@(TypeVar name Nothing) typeExprs = foldl occursInArg (state, False) typeExprs
    where
        occursInArg (state, occurs) te = (state', occurs || oc)
            where
                (state', oc) = occursInType state tv te


----------------------------- local helper functions

binaryArithOp :: TypeExpr
binaryArithOp = int `arrow` (int `arrow` int)


binaryLogicalOp :: TypeExpr
binaryLogicalOp = int `arrow` (int `arrow` bool)


initialTypeInstanceEnv :: TypeInstanceEnv
initialTypeInstanceEnv = Map.empty


initialState :: State
initialState = State initialNameSupply initialTypeInstanceEnv


initialTypeEnv :: (State, TypeEnv)
initialTypeEnv =
  (state2,
   Map.fromList [("+", binaryArithOp),
                 ("-", binaryArithOp),
                 ("*", binaryArithOp),
                 ("/", binaryArithOp),
                 ("if", bool `arrow` (v1 `arrow` (v2 `arrow` v3))),
                 ("==", binaryLogicalOp),
                 ("<=", binaryLogicalOp),
                 (">=", binaryLogicalOp),
                 (">", binaryLogicalOp),
                 ("<", binaryLogicalOp)])
  where
    (state1, v1) = newTypeVariable initialState
    (state2, v2) = newTypeVariable state1
    (state3, v3) = newTypeVariable state2



initialNonGeneric :: NonGeneric
initialNonGeneric = Set.empty

