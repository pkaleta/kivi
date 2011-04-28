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

type TiDump = [TiStack]
data Node
    = NAp Addr Addr
    | NSc Name [Name] CoreExpr
    | NNum Int
    | NInd Addr
    | NPrim Name Primitive
    deriving Show
data Primitive = Neg | Add | Sub | Mul | Div
    deriving Show

primitives :: Assoc Name Primitive
primitives = [("negate", Neg),
              ("+", Add),
              ("-", Sub),
              ("*", Mul),
              ("/", Div)]

tiDumpInitial :: TiDump
tiDumpInitial = []

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
    trace ("************* " ++ show topAddr ++ ": " ++ (show top)) (dispatch top)
    where
        top = hLookup heap topAddr
        (topAddr : rest, dump, heap, globals, stats) = state
        dispatch (NNum n) = numStep state n
        dispatch (NSc name args body) = scStep state name args body
        dispatch (NAp a1 a2) = apStep state a1 a2
        dispatch (NPrim name primitive) = primStep state name primitive
        dispatch (NInd addr) = (addr : rest, dump, heap, globals, stats)

numStep :: TiState -> Int -> TiState
numStep (stack, (head : dump), heap, globals, stats) n = trace ("jestem " ++ (show head)) (head, dump, heap, globals, stats)
numStep state n = error "Number at the top of the stack."

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 a2 =
    case hLookup heap a2 of
        (NInd addr) ->
            (stack, dump, heap', globals, stats)
            where
                heap' = hUpdate heap topAddr $ NAp a1 addr
                (topAddr : addrs) = stack
        _ ->
            --trace ("stack top: " ++ show a1)
            (a1 : stack, dump, heap, globals, stats)

primStep :: TiState -> Name -> Primitive -> TiState
primStep state name Neg = primNeg state
primStep state name Add = primArith state (+)
primStep state name Sub = primArith state (-)
primStep state name Mul = primArith state (*)
primStep state name Div = primArith state (div)

primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state op =
    case node1 of
        (NNum v1) ->
            case node2 of
                (NNum v2) ->
                    (stack', dump, heap', globals, stats)
                    where
                        stack' = drop 2 stack
                        heap' = hUpdate heap ap2 (NNum $ op v1 v2)
                _ ->
                    (stack', dump', heap, globals, stats)
                    where
                        stack' = [addr2]
                        dump' = stack : dump
        _ ->
            (stack', dump', heap, globals, stats)
            where
                stack' = [addr1]
                dump' = stack : dump
    where
        (stack, dump, heap, globals, stats) = state
        node1 = hLookup heap addr1
        node2 = hLookup heap addr2
        addr1 = getArg heap ap1
        addr2 = getArg heap ap2
        ap1 = stack !! 1
        ap2 = stack !! 2

primNeg :: TiState -> TiState
primNeg (stack, dump, heap, globals, stats) =
    case trace ("primneg arg: " ++ (show node)) node of
        (NNum v) ->
            (stack', dump, heap', globals, stats)
            where
                heap' = hUpdate heap root (NNum $ -v)
                stack' = tail stack
        _ ->
            (stack', dump', heap, globals, stats)
            where
                stack' = [addr]
                dump' = (tail stack) : dump
    where
        node = hLookup heap addr
        addr = getArg heap root
        root = stack !! 1

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) name argNames body =
    case (n + 1) <= length stack of
        True ->
            (stack1, dump, heap2, globals, stats)
            where
                an = stack !! n
                stack1 = resultAddr : (drop (n + 1) stack)
                (heap1, resultAddr) = instantiate body heap env
                heap2 = hUpdate heap1 an (NInd resultAddr)
                env = argBindings ++ globals
                argBindings = zip argNames $ getArgs heap stack
        _ ->
            error "Not enough arguments on the stack"
    where
        n = length argNames

getArgs :: TiHeap -> TiStack -> [Addr]
getArgs heap (sc : stack) =
    map (getArg heap) stack

getArg :: TiHeap -> Addr -> Addr
getArg heap addr = arg
    where
        (NAp f arg) = hLookup heap addr

--instantiateAndUpdate :: CoreExpr -> Addr -> TiHeap -> Assoc Name Addr -> TiHeap
--instantiateAndUpdate (ENum n) toUpdate heap env =
--    hUpdate heap toUpdate (NNum n)
--instantiateAndUpdate (EAp e1 e2) toUpdate heap env =
--    hUpdate heap2 toUpdate (NAp a1 a2)
--    where
--        (heap1, a1) = instantiate e1 heap env
--        (heap2, a2) = instantiate e2 heap1 env
--instantiateAndUpdate (EVar v) toUpdate heap env =
--    hUpdate heap toUpdate (NInd $ aLookup env v $ error $ "Undefined name: " ++ show v)
--instantiateAndUpdate (ELet False defns body) heap env
--    hUpdate heap2 toUpdate (NInd addr)
--    where
--        (heap2, addr) = instantiate body heap1 env1
--        (heap1, env1) = foldl (accumulate env) (heap, env) defns

instantiate :: CoreExpr -> TiHeap -> Assoc Name Addr  -> (TiHeap, Addr)
-- numbers
instantiate (ENum n) heap env = hAlloc heap (NNum n)
-- applications
instantiate (EAp e1 e2) heap env =
    hAlloc heap2 $ NAp a1 a2
    where
        (heap1, a1) = instantiate e1 heap env
        (heap2, a2) = instantiate e2 heap1 env
-- variables
instantiate (EVar v) heap env =
    (heap, aLookup env v $ error $ "Undefined name: " ++ show v)
-- let expressions
instantiate (ELet False defns body) heap env =
    instantiate body heap1 env1
    where
        (heap1, env1) = foldl (accumulate env) (heap, env) defns
-- letrec expressions
instantiate (ELet True defns body) heap env =
    instantiate body heap1 env1
    where
        (heap1, env1) = foldl (accumulate env1) (heap, env) defns
-- constructors
instantiate (EConstr tag arity) heap env =
    error "Could not instantiate constructors for the time being."
-- case expressions
instantiate (ECase expr alts)  heap env =
    error "Could not instantiate case expressions for the time being."

accumulate :: Assoc Name Addr -> (TiHeap, Assoc Name Addr) -> (Name, CoreExpr) -> (TiHeap, Assoc Name Addr)
accumulate env (heap, env1) (name, expr) =
    (heap1, (name, addr) : env1)
    where
        (heap1, addr) = instantiate expr heap env

tiFinal :: TiState -> Bool
tiFinal ([addr], [], heap, globals, stats) = isDataNode (hLookup heap addr)
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode _ = False

showResults :: [TiState] -> String
showResults [] = ""
showResults ((stack, dump, heap, globals, stats) : rest) = "showresults: " ++ (show $ head stack) ++ ": " ++ show (hLookup heap $ head stack) ++ showResults rest

-- local helper functions

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap scDefs =
    (heap2, scAddrs ++ primAddrs)
    where
        (heap1, scAddrs) = mapAccumL allocateSc hInitial scDefs
        (heap2, primAddrs) = mapAccumL allocatePrim heap1 primitives

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (heap', (name, addr))
    where
        (heap', addr) = hAlloc heap $ NSc name args body

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, primitive) = (heap', (name, addr))
    where
        (heap', addr) = hAlloc heap $ NPrim name primitive

