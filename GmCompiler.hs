module GmCompiler where

import Common
import Parser
import Utils
import List
import Core
import Debug.Trace

type GmCompiledSc = (Name, Int, GmCode)
type GmCompiler = CoreExpr -> GmEnvironment -> GmCode
type GmEnvironment = Assoc Name Int

primitives :: [(Name, [Name], CoreExpr)]
primitives = [("+", ["x", "y"], EAp (EAp (EVar "+") (EVar "x")) (EVar "y")),
              ("-", ["x", "y"], EAp (EAp (EVar "-") (EVar "x")) (EVar "y")),
              ("*", ["x", "y"], EAp (EAp (EVar "*") (EVar "x")) (EVar "y")),
              ("/", ["x", "y"], EAp (EAp (EVar "/") (EVar "x")) (EVar "y")),
              ("negate", ["x"], EAp (EVar "negate") (EVar "x")),
              ("==", ["x", "y"], EAp (EAp (EVar "==") (EVar "x")) (EVar "y")),
              ("!=", ["x", "y"], EAp (EAp (EVar "!=") (EVar "x")) (EVar "y")),
              ("<", ["x", "y"], EAp (EAp (EVar "<") (EVar "x")) (EVar "y")),
              ("<=", ["x", "y"], EAp (EAp (EVar "<=") (EVar "x")) (EVar "y")),
              (">", ["x", "y"], EAp (EAp (EVar ">=") (EVar "x")) (EVar "y")),
              (">=", ["x", "y"], EAp (EAp (EVar ">=") (EVar "x")) (EVar "y")),
              ("if", ["c", "t", "f"], EAp (EAp (EAp (EVar "if") (EVar "c")) (EVar "t")) (EVar "y")),
              ("True", [], EConstr 2 0),
              ("False", [], EConstr 1 0)]

builtinDyadic :: Assoc Name Instruction
builtinDyadic = [("+", Add),
                 ("-", Sub),
                 ("*", Mul),
                 ("/", Div),
                 ("==", Eq),
                 ("!=", Ne),
                 ("<", Lt),
                 ("<=", Le),
                 (">", Gt),
                 (">=", Ge)]

compile :: CoreProgram -> GmState
compile program = ([], initialCode, [], [], [], heap, globals, initialStats)
    where
        (heap, globals) = buildInitialHeap program

initialCode :: GmCode
initialCode = [Pushglobal "main", Eval, Print]

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program =
    mapAccumL allocateSc hInitial (compiled ++ compiledPrimitives)
    where
        compiled = map compileSc $ preludeDefs ++ program ++ primitives

allocateSc :: GmHeap -> GmCompiledSc -> (GmHeap, (Name, Addr))
allocateSc heap (name, argc, code) = (heap', (name, addr))
    where
        (heap', addr) = hAlloc heap $ NGlobal argc code

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSc
compileSc (name, args, expr) =
    (name, length args, compileR expr $ zip args [0..])

compileR :: GmCompiler
compileR expr env = compileE expr env ++ [Update n, Pop n, Unwind]
    where
        n = length env

compileB :: GmCompiler
compileB (NNum n) env = [Pushbasic n]
compileB (ELet isRec defs body) env | isRec = compileLetrec compileB defs body env
                                    | otherwise = compileLet compileB defs body env
compileB (EAp (EVar "negate") expr) env =
    compileB expr env ++ [Neg]
compileB (EAp (EAp (EAp (EVar "if") cond) et) ef) env =
    compileB cond env ++ [Cond (compileB et env) (compileB ef env)]
compileB expr env =
    case expr of
        (EAp (EAp (EVar name) e1) e2) ->
            compileB e2 env ++
            compileB e1 (argOffset 1 env) ++ -- nie wiem czy tu ma byc argoffset
            case aHasKey builtinDyadic name of
                True -> [aLookup builtinDyadic name $ error "This is not possible"]
                False -> compileE expr env ++ [Get]
        expr ->
            compileE expr env ++ [Get]

compileE :: GmCompiler
compileE (ENum n) env = [Pushint n]
compileE (ELet isRec defs body) env | isRec = compileLetrec compileE defs body env
                                    | otherwise = compileLet compileE defs body env
compileE (ECase expr alts) env =
    compileE expr env ++ [Casejump $ compileD alts env]
--compileE (EIf cond et ef) env =
--    (compileE cond env) ++ [Cond (compileE et env) (compileE ef env)]
compileE (EAp (EAp (EVar name) e1) e2) env =
    compileE e2 env ++
    compileE e1 (argOffset 1 env) ++
    case aHasKey builtinDyadic name of
        True -> [aLookup builtinDyadic name $ error "This is not possible"]
        False -> [Pushglobal name, Mkap, Mkap]
compileE expr env = compileC expr env ++ [Eval]

compileD :: [CoreAlt] -> Assoc Name Addr -> Assoc Int GmCode
compileD alts env = [compileA alt env | alt <- alts]

compileA :: CoreAlt -> Assoc Name Addr -> (Int, GmCode)
compileA (t, args, expr) env =
    (t, [Split n] ++ compileE expr env' ++ [Slide n])
    where
        n = length args
        env' = zip args [0..] ++ argOffset n env

compileC :: GmCompiler
compileC (EVar v) env =
    case aHasKey env v of
        True -> [Push $ aLookup env v $ error "This is not possible"]
        False -> [Pushglobal v]
compileC (EConstr t n) env = [Pushglobal $ constrFunctionName t n]
compileC (ENum n) env = [Pushint n]
compileC (EAp e1 e2) env =
--fst $ compileAp (EAp e1 e2) env
    compileC e2 env ++
    compileC e1 (argOffset 1 env) ++
    [Mkap]
compileC (ELet isRec defs body) env | isRec = compileLetrec compileC defs body env
                                    | otherwise = compileLet compileC defs body env

constrFunctionName t n = "Pack{" ++ show t ++ "," ++ show n ++ "}"

compileAp :: CoreExpr -> GmEnvironment -> (GmCode, Int)
compileAp (EConstr t n) env = ([Pack t n], n)
compileAp (EAp e1 e2) env =
    case n > 0 of
        True ->
            (codeE2 ++ codeE1, n - 1)
        False ->
            (codeE2 ++ codeE1 ++ [Mkap], 0)
    where
        (codeE2, _) = compileAp e2 env
        (codeE1, n) = compileAp e1 (argOffset 1 env)
compileAp node env = (compileC node env, 0)

compileLet :: GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLet comp defs body env =
    compileDefs defs env ++ comp body env' ++ [Slide $ length defs]
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

compileLetrec :: GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLetrec comp defs body env =
    [Alloc n] ++ compileRecDefs n defs env' ++ comp body env' ++ [Slide n]
    where
        n = length defs
        env' = compileArgs defs env

compileRecDefs :: Int -> [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileRecDefs 0 [] env = []
compileRecDefs n ((name, expr) : defs) env =
        compileC expr env ++ [Update $ n - 1] ++ compileRecDefs (n - 1) defs env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = map (\(name, pos) -> (name, pos + n)) env

