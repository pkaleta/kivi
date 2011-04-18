module Template where

import Lexer
import Parser
import Utils
import List
import Core
import Debug.Trace

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)
type TiStack = [Addr]
type TiHeap = Heap Node
type TiGlobals = Assoc Name Addr
type TiStats = Int

data TiDump = DummyTiDump
    deriving Show
data Node
    = NAp Addr Addr
    | NSc Name [Name] CoreExpr
    | NNum Int
    deriving Show

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

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (stack, dump, heap, globals, stats) =
    (stack, dump, heap, globals, f stats)

run :: String -> String
run = showResults . eval . compile . parse

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
step state =
    trace ("************* " ++ show top ++ ": " ++ (show $ hLookup heap top)) (dispatch $ hLookup heap top)
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
scStep (stack, dump, heap, globals, stats) name argNames body =
    case (length argNames + 1) <= length stack of
        True ->
            (stack1, dump, heap1, globals, stats)
            where
                stack1 = resultAddr : (drop (length argNames + 1) stack)
                (heap1, resultAddr) = instantiate body heap env
                env = argBindings ++ globals
                argBindings = zip argNames $ getArgs heap stack
        _ ->
            error "Not enough arguments on the stack"

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
instantiate (ELet isRec defns body) heap env =
    instantiate body heap1 env1
    where
        (heap1, env1) = foldl accumulate (heap, env) defns
instantiate (EConstr tag arity) heap env =
    error "Could not instantiate constructors for the time being."
instantiate (ECase expr alts)  heap env =
    error "Could not instantiate case expressions for the time being."

accumulate :: (TiHeap, Assoc Name Addr) -> (Name, CoreExpr) -> (TiHeap, Assoc Name Addr)
accumulate (heap, env) (name, expr) =
    (heap1, (name, addr) : env)
    where
        (heap1, addr) = instantiate expr heap env

tiFinal :: TiState -> Bool
tiFinal ([addr], dump, heap, globals, stats) = isDataNode (hLookup heap addr)
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode _ = False

showResults :: [TiState] -> String
showResults [] = ""
showResults ((stack, dump, heap, globals, stats) : rest) = 
    -- show ([hLookup heap addr | addr <- (hAddresses heap)]) ++ "\n" ++ 
    show (hLookup heap (head stack)) ++ showResults rest

-- local helper functions

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs = mapAccumL allocateSc hInitial scDefs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap1, (name, addr))
    where
        (heap1, addr) = hAlloc heap $ NSc name args body

