module GmCompiler where

import Common
import Parser
import Utils
import List
import Core

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

argOffset :: Int -> Assoc Name Int -> Assoc Name Int
argOffset n env = map (\(name, pos) -> (name, pos + n)) env

