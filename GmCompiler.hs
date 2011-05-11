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

compiledPrimitives :: [GmCompiledSc]
compiledPrimitives = [("+", 2, [Push 1, Eval, Push 1, Eval, Add, Update 2, Pop 2, Unwind]),
                      ("-", 2, [Push 1, Eval, Push 1, Eval, Sub, Update 2, Pop 2, Unwind]),
                      ("*", 2, [Push 1, Eval, Push 1, Eval, Mul, Update 2, Pop 2, Unwind]),
                      ("/", 2, [Push 1, Eval, Push 1, Eval, Div, Update 2, Pop 2, Unwind]),
                      ("negate", 1, [Push 0, Eval, Neg, Update 1, Pop 1, Unwind]),
                      ("==", 2, [Push 1, Eval, Push 1, Eval, Eq, Update 2, Pop 2, Unwind]),
                      ("!=", 2, [Push 1, Eval, Push 1, Eval, Ne, Update 2, Pop 2, Unwind]),
                      ("<", 2, [Push 1, Eval, Push 1, Eval, Lt, Update 2, Pop 2, Unwind]),
                      ("<=", 2, [Push 1, Eval, Push 1, Eval, Le, Update 2, Pop 2, Unwind]),
                      (">", 2, [Push 1, Eval, Push 1, Eval, Gt, Update 2, Pop 2, Unwind]),
                      (">=", 2, [Push 1, Eval, Push 1, Eval, Ge, Update 2, Pop 2, Unwind]),
                      ("if", 3, [Push 0, Eval, Cond [Push 1] [Push 2], Update 3, Pop 3, Unwind])]

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
                 (">=", Ge),
                 ("negate", Neg)]

compile :: CoreProgram -> GmState
compile program = ([], initialCode, [], [], heap, globals, initialStats)
    where
        (heap, globals) = buildInitialHeap program

initialCode :: GmCode
initialCode = [Pushglobal "main", Eval]

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program =
    mapAccumL allocateSc hInitial (compiled ++ compiledPrimitives)
    where
        compiled = map compileSc $ program ++ preludeDefs

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

compileE :: GmCompiler
compileE (ENum n) env = [Pushint n]
compileE (ELet isRec defs body) env | isRec = compileLetrec defs body env
                                    | otherwise = compileLet defs body env
compileE (EAp (EAp (EAp (EVar "if") cond) et) ef) env =
    (compileE cond env) ++ [Cond (compileE et env) (compileE ef env)]
compileE (EAp (EAp (EVar name) e1) e2) env =
    compileE e2 env ++
    compileE e1 env ++
    case aHasKey builtinDyadic name of
        True -> [aLookup builtinDyadic name $ error "This is not possible"]
        False -> [Pushglobal name, Mkap]
compileE (EAp e1 e2) env =
    compileE e2 env ++
    compileE e1 (argOffset 1 env) ++
    [Mkap]
compileE expr env = compileC expr env ++ [Eval]

compileC :: GmCompiler
compileC (EVar v) env =
    case aHasKey env v of
        True -> [Push $ aLookup env v $ error "This is not possible"]
        False -> [Pushglobal v]
compileC (ENum n) env = [Pushint n]
compileC (EAp e1 e2) env =
    compileC e2 env ++
    compileC e1 (argOffset 1 env) ++
    [Mkap]
compileC (ELet isRec defs body) env | isRec = compileLetrec defs body env
                                    | otherwise = compileLet defs body env

compileLet :: [(Name, CoreExpr)] -> GmCompiler
compileLet defs body env =
    compileDefs defs env ++ compileE body env' ++ [Slide $ length defs]
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

compileLetrec :: [(Name, CoreExpr)] -> GmCompiler
compileLetrec defs body env =
    [Alloc n] ++ compileRecDefs n defs env' ++ compileE body env' ++ [Slide n]
    where
        n = length defs
        env' = compileArgs defs env

compileRecDefs :: Int -> [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileRecDefs 0 [] env = []
compileRecDefs n ((name, expr) : defs) env =
        compileC expr env ++ [Update $ n - 1] ++ compileRecDefs (n - 1) defs env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = map (\(name, pos) -> (name, pos + n)) env

