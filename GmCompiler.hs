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

compile :: CoreProgram -> GmState
compile program = (initialCode, [], heap, globals, initialStats)
    where
        (heap, globals) = buildInitialHeap program

initialCode :: GmCode
initialCode = [Pushglobal "main", Unwind]

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program =
    mapAccumL allocateSc hInitial compiled
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
compileR expr env = compileC expr env ++ [Update n, Pop n, Unwind]
    where
        n = length env

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
--compileC (ELet true defs body) env = compileLetrec defs body env
compileC (ELet false defs body) env = compileLet defs body env

compileLet :: [(Name, CoreExpr)] -> GmCompiler
compileLet defs body env =
    trace ("**********************" ++ show (env')) compileDefs defs env ++ compileC body env' ++ [Slide $ length defs]
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

--compileLetrec :: [(Name, Expr)] -> GmCompiler
--compileLetrec defs body env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = map (\(name, pos) -> (name, pos + n)) env

