module Template where

import Lexer
import Parser
import Utils
import List

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)
type TiStack = [Addr]
type TiHeap = Heap Node
type TiGlobals = Assoc Name Addr
type TiStats = Int

data TiDump = DummyTiDump
data Node
    = NAp Addr Addr
    | NSc Name [Name] CoreExpr
    | NNum Int

tiDumpInitial :: TiDump
tiDumpInitial = DummyTiDump

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s + 1

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps s = s

extraPreludeDefs :: [CoreScDefn]
extraPreludeDefs = []

preludeDefs :: [CoreScDefn]
preludeDefs = []

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (stack, dump, heap, globals, stats) =
    (stack, dump, heap, globals, f stats)

--runProg :: String -> String
--runProg = showResults . eval . compile . parse

compile :: CoreProgram -> TiState
compile program = (stack, tiDumpInitial, heap, globals, tiStatInitial)
    where
        scDefs = program ++ preludeDefs ++ extraPreludeDefs
        (heap, globals) = buildInitialHeap scDefs
        mainAddress = aLookup globals "main" (error "Undefined function main.")
        stack = [mainAddress]

eval :: TiState -> [TiState]
eval state = state : restStates
    where
        restStates | tiFinal state = []
                   | otherwise = eval nextState
        nextState = doAdmin $ step state
        doAdmin = applyToStats tiStatIncSteps

step :: TiState -> TiState
step state = dispatch $ hLookup heap top
    where
        (top : rest, dump, heap, globals, stats) = state
        dispatch (NNum n) = numStep state n
        dispatch (NSc name args body) = scStep state name args body
        dispatch (NAp a1 a2) = apStep state a1 a2

numStep :: TiState -> Int -> TiState
numStep state n = error "Number at the top of the stack."

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 a2 =
    (a1 : stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats)  name argNames body =
    (stack1, dump, heap1, globals, stats)
    where
        stack1 = resultAddr : (drop (length argNames) stack)
        (heap1, resultAddr) = instantiate body heap env
        env = argBindings ++ globals
        argBindings = zip argNames $ getArgs heap stack

getArgs :: TiHeap -> TiStack -> [Addr]
getArgs heap (sc : stack) =
    map (getArg heap) stack

getArg :: TiHeap -> Addr -> Addr
getArg heap addr = arg
    where
        (NAp f arg) = hLookup heap addr
--    [arg | (NAp f arg) = hLookup heap addr, addr <- stack]

instantiate :: CoreExpr -> TiHeap -> Assoc Name Addr  -> (TiHeap, Addr)
instantiate (ENum n) heap env = hAlloc heap (NNum n)
instantiate (EAp e1 e2) heap env =
    hAlloc heap2 $ NAp a1 a2
    where
        (heap1, a1) = instantiate e1 heap env
        (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env =
    (heap, aLookup env v $ error $ "Undefined name: " ++ show v)
instantiate (EConstr tag arity) heap env =
    error "Could not instantiate constructors for the time being."
instantiate (ELet isRec defns body)  heap env =
    error "Could not instantiate let expressions for the time being."
instantiate (ECase expr alts)  heap env =
    error "Could not instantiate case expressions for the time being."

tiFinal :: TiState -> Bool
tiFinal ([addr], _, heap, _, _) = isDataNode (hLookup heap addr)

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode _ = False

--showResults :: [TiState] -> String


-- local helper functions

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs = mapAccumL allocateSc hInitial scDefs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap1, (name, addr))
    where
        (heap1, addr) = hAlloc heap $ NSc name args body

