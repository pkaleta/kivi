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
step (addr : restAddrs, _, heap, _, _) = dispatch $ hLookup heap addr
    where
        dispatch (NNum n) = numStep state n
        dispatch (NSc name args body) = scStep state name args body
        dispatch (nAp a1 a2) = apStep state a1 a2

numStep :: TiState -> Int -> TiState
numStep state n = error "Number at the top of the stack."

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 a2 =
    (a1 : stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr
scStep (stack0, dump, heap0, globals, stats)  name argNames body =
    (stack1, dump, heap1, globals, stats)
    where
        stack1 = resultAddr : stack0
        (heap1, resultAddr) = instantiate body heap env
        env = argBindings ++ globals
        argBindings = zip argNames getArgAddrs

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

