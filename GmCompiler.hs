module GmCompiler where


import Common
import Parser
import Utils
import List
import Core
import Debug.Trace
import AbstractDataTypes


type GmCompiledSc = (Name, Int, GmCode)
type GmCompiler = CoreExpr -> GmEnvironment -> GmCode
type GmEnvironment = Assoc Name Int


primitiveScs :: [CoreScDefn]
primitiveScs = [(ScDefn "+" ["x", "y"] (EAp (EAp (EVar "+") (EVar "x")) (EVar "y"))),
                (ScDefn "-" ["x", "y"] (EAp (EAp (EVar "-") (EVar "x")) (EVar "y"))),
                (ScDefn "*" ["x", "y"] (EAp (EAp (EVar "*") (EVar "x")) (EVar "y"))),
                (ScDefn "/" ["x", "y"] (EAp (EAp (EVar "/") (EVar "x")) (EVar "y"))),
                (ScDefn "negate" ["x"] (EAp (EVar "negate") (EVar "x"))),
                (ScDefn "==" ["x", "y"] (EAp (EAp (EVar "==") (EVar "x")) (EVar "y"))),
                (ScDefn "!=" ["x", "y"] (EAp (EAp (EVar "!=") (EVar "x")) (EVar "y"))),
                (ScDefn "<" ["x", "y"] (EAp (EAp (EVar "<") (EVar "x")) (EVar "y"))),
                (ScDefn "<=" ["x", "y"] (EAp (EAp (EVar "<=") (EVar "x")) (EVar "y"))),
                (ScDefn ">" ["x", "y"] (EAp (EAp (EVar ">=") (EVar "x")) (EVar "y"))),
                (ScDefn ">=" ["x", "y"] (EAp (EAp (EVar ">=") (EVar "x")) (EVar "y")))]


selFunName :: Int -> Int -> String
selFunName r i = "select-" ++ show r ++ "-" ++ show i


precompiledScs :: [GmCompiledSc]
precompiledScs = []--foldl genSelFuns [] [0..5]


genSelFuns :: [GmCompiledSc] -> Int -> [GmCompiledSc]
genSelFuns acc r = acc ++ foldl (genSelFun r) [] [0..r-1]


genSelFun :: Int -> [GmCompiledSc] -> Int -> [GmCompiledSc]
genSelFun r acc i = (selFunName r i, 1, [Push 0, Eval, Select r i, Update 1, Pop 1, Unwind]) : acc


builtinDyadicBool :: Assoc Name Instruction
builtinDyadicBool = [("==", Eq),
                     ("!=", Ne),
                     ("<", Lt),
                     ("<=", Le),
                     (">", Gt),
                     (">=", Ge)]


builtinDyadicInt :: Assoc Name Instruction
builtinDyadicInt = [("+", Add),
                    ("-", Sub),
                    ("*", Mul),
                    ("/", Div)]


builtinDyadic :: Assoc Name Instruction
builtinDyadic = builtinDyadicBool ++ builtinDyadicInt


getCompiledCode :: CoreProgram -> String
getCompiledCode program@(adts, scs) =
    foldl stringify "" compiled
    where
        state = compile program
        globals = getGlobals state
        heap = getHeap state
        compiled = foldl getCode [] globals

        stringify acc (name, expr, code) =
            acc ++ show expr ++ "\n\n" ++ show code ++ "\n\n"

        getCode acc (name, addr) =
            (name, find name scs, code) : acc
            where
                (NGlobal arity code) = hLookup heap addr

        find n1 (sc@(ScDefn n2 args expr) : rest) | n1 == n2  = sc
                                                  | otherwise = find n1 rest
        find n1 [] = (ScDefn n1 [] (EError "Built-in function: code not available"))


compile :: CoreProgram -> GmState
compile (dts, scs) = ([], initialCode, [], [], [], heap, globals, initialStats)
    where
        (heap, globals) = buildInitialHeap scs


initialCode :: GmCode
initialCode = [Pushglobal "main", Eval, Print]


buildInitialHeap :: [CoreScDefn] -> (GmHeap, GmGlobals)
buildInitialHeap program =
    mapAccumL allocateSc hInitial $ compiled ++ precompiledScs
    where
        compiled = map compileSc $ preludeDefs ++ program ++ primitiveScs


allocateSc :: GmHeap -> GmCompiledSc -> (GmHeap, (Name, Addr))
allocateSc heap (name, argc, code) = (heap', (name, addr))
    where
        (heap', addr) = hAlloc heap $ NGlobal argc code


compileSc :: CoreScDefn -> GmCompiledSc
compileSc (ScDefn name args expr) =
    (name, n, compileR n expr $ zip args [0..])
    where
        n = length args


compileR :: Int -> GmCompiler
compileR d (ELet isRec defs body) env | isRec = compileLetrec [] (compileR $ d + n) defs body env
                                      | otherwise = compileLet [] (compileR $ d + n) defs body env
    where n = length defs
compileR d (EAp (EAp (EAp (EVar "if") cond) et) ef) env =
    compileE cond env ++ [CasejumpConstr [(trueTag, compileR d et env), (falseTag, compileR d ef env)]]
compileR d (ECaseSimple expr alts) env =
    compileE expr env ++ [CasejumpSimple $ compileD (compileR $ d + 1) alts $ argOffset 1 env]
compileR d (ECaseConstr expr alts) env =
    compileE expr env ++ [CasejumpConstr $ compileD (compileR $ d + 1) alts $ argOffset 1 env]
compileR d expr env = compileE expr env ++ [Update d, Pop d, Unwind]


compileB :: GmCompiler
compileB (ENum n) env = [Pushbasic n]
compileB (ELet isRec defs body) env | isRec = compileLetrec [Pop $ length defs] compileB defs body env
                                    | otherwise = compileLet [Pop $ length defs] compileB defs body env
compileB (EAp (EVar "negate") expr) env =
    compileB expr env ++ [Neg]
compileB (EAp (EAp (EAp (EVar "if") cond) et) ef) env =
    compileE cond env ++ [CasejumpConstr [(trueTag, compileB et env), (falseTag, compileB ef env)]]
compileB expr@(EAp (EAp (EVar name) e1) e2) env =
    compileB e2 env ++
    compileB e1 env ++
    case aHasKey builtinDyadic name of
        True -> [aLookup builtinDyadic name $ error "This is not possible"]
        False -> compileE expr env ++ [Get]
compileB expr env =
    compileE expr env ++ [Get]


compileE :: GmCompiler
compileE (ENum n) env = [Pushint n]
compileE (ELet isRec defs body) env | isRec = compileLetrec [Slide $ length defs] compileE defs body env
                                    | otherwise = compileLet [Slide $ length defs] compileE defs body env
compileE (ECaseSimple expr alts) env =
    compileE expr env ++ [CasejumpSimple $ compileD compileE alts $ argOffset 1 env]
compileE (ECaseConstr expr alts) env =
    compileE expr env ++ [CasejumpConstr $ compileD compileE alts $ argOffset 1 env]
compileE (EAp (EVar "negate") expr) env =
    compileB expr env ++ [MkInt]
compileE (EAp (EAp (EAp (EVar "if") cond) et) ef) env =
    compileE cond env ++ [CasejumpConstr [(trueTag, compileE et env), (falseTag, compileE ef env)]]
compileE expr@(EAp (EAp (EVar name) e1) e2) env =
    case aHasKey builtinDyadic name of
        True -> compileB expr env ++ [intOrBool name]
        False -> compileC expr env ++ [Eval]
compileE expr env =
    compileC expr env ++ [Eval]


intOrBool :: Name -> Instruction
intOrBool name =
    case aHasKey builtinDyadicInt name of
        True -> MkInt
        False ->
            case aHasKey builtinDyadicBool name of
                True -> MkBool
                False -> error $ "Name: " ++ name ++ " is not a built-in operator"


compileD :: GmCompiler -> [CoreAlt] -> Assoc Name Addr -> Assoc Int GmCode
compileD comp alts env = [compileA comp alt env | alt <- alts]


compileA :: GmCompiler -> CoreAlt -> Assoc Name Addr -> (Int, GmCode)
compileA comp (num, expr) env = (num, comp expr env)
-- TODO: shouldn't we use env' here instead of env?
--    where
--        n = length args
--        env' = zip args [0..] ++ argOffset n env


compileC :: GmCompiler
compileC (ENum n) env = [Pushint n]
compileC (EVar v) env =
    case aHasKey env v of
        True -> [Push $ aLookup env v $ error "This is not possible"]
        False -> [Pushglobal v]
compileC (EConstr t n) env = [Pushglobal $ constrFunctionName t n]
compileC (EAp e1 e2) env =
    compileC e2 env ++
    compileC e1 (argOffset 1 env) ++
    [Mkap]
compileC (ESelect r i v) env =
    case aHasKey env v of
        True -> [Push $ aLookup env v $ error "This cannot happen", Pushglobal $ selFunName r i, Mkap]
        False -> [Pushglobal v, Pushglobal $ selFunName r i, Mkap]
compileC (ELet isRec defs body) env | isRec = compileLetrec [Slide $ length defs] compileC defs body env
                                    | otherwise = compileLet [Slide $ length defs] compileC defs body env
compileC (ECaseSimple expr alts) env =
    compileE expr env ++ [CasejumpSimple $ compileD compileE alts $ argOffset 1 env]
compileC (ECaseConstr expr alts) env =
    compileE expr env ++ [CasejumpConstr $ compileD compileE alts $ argOffset 1 env]
compileC (EError msg) env = [Error msg]
compileC x env = error $ "Compilation scheme for the following expression does not exist: " ++ show x


constrFunctionName t n = "Pack{" ++ show t ++ "," ++ show n ++ "}"


compileLet :: [Instruction] -> GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLet finalInstrs comp defs body env =
    compileDefs defs env ++ comp body env' ++ finalInstrs
    where
        env' = compileArgs defs env


compileDefs :: [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileDefs [] env = []
compileDefs ((name, expr) : defs) env =
    compileC expr env ++ (compileDefs defs $ argOffset 1 env)

compileArgs :: [(Name, CoreExpr)] -> GmEnvironment -> GmEnvironment
compileArgs defs env =
    zip (map fst defs) [n-1, n-2 .. 0] ++ argOffset n env
    where
        n = length defs


compileLetrec :: [Instruction] -> GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLetrec finalInstrs comp defs body env =
    --trace ("################" ++ show env') 
    [Alloc n] ++ compileRecDefs n defs env' ++ comp body env' ++ finalInstrs
    where
        n = length defs
        env' = compileArgs defs env


compileRecDefs :: Int -> [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileRecDefs 0 [] env = []
compileRecDefs n ((name, expr) : defs) env =
    compileC expr env ++ [Update $ n - 1] ++ compileRecDefs (n - 1) defs env


argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = map (\(name, pos) -> (name, pos + n)) env

