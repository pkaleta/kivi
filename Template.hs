module Template where

import Lexer
import Parser
import Utils
import List
import Core
import Debug.Trace

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats, TiOutput)
type TiStack = [Addr]
type TiHeap = Heap Node
type TiGlobals = Assoc Name Addr
type TiStats = Int
type TiOutput = [Int]

type TiDump = [TiStack]

data Node
    = NAp Addr Addr
    | NSc Name [Name] CoreExpr
    | NNum Int
    | NInd Addr
    | NPrim Name Primitive
    | NData Int [Addr]
    | NIf Addr Addr Addr
    deriving Show

data Primitive = Neg
               | Add
               | Sub
               | Mul
               | Div
               | PrimConstr Int Int
               | If
               | Greater
               | GreaterEq
               | Less
               | LessEq
               | Eq
               | NotEq
               | PrimCasePair
               | PrimCaseList
               | PrimCons
               | Print
               | Stop
    deriving Show

primitives :: Assoc Name Primitive
primitives = [("negate", Neg),
              ("+", Add),
              ("-", Sub),
              ("*", Mul),
              ("/", Div),
              (">", Greater),
              (">=", GreaterEq),
              ("<", Less),
              ("<=", LessEq),
              ("==", Eq),
              ("!=", NotEq),
              ("if", If),
              ("False", PrimConstr 1 0),
              ("True", PrimConstr 2 0),
              ("CasePair", PrimCasePair),
              ("MkPair", PrimConstr 3 2),
              ("Nil", PrimConstr 4 0),
              ("Cons", PrimCons),
              ("CaseList", PrimCaseList),
              ("abort", error "Calling head/tail on empty list"),
              ("print", Print),
              ("stop", Stop)]

tiDumpInitial :: TiDump
tiDumpInitial = []

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s + 1

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps s = s

tiOutputInitial :: TiOutput
tiOutputInitial = []

extraPreludeDefs :: [CoreScDefn]
extraPreludeDefs = [("and", ["x", "y"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "y")) (EVar "False")),
                    ("or", ["x", "y"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "True")) (EVar "y")),
                    ("xor", ["x", "y"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EAp (EVar "not") (EVar "y"))) (EVar "y")),
                    ("not", ["x"], EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "False")) (EVar "True")),
                    ("fst", ["p"], EAp (EAp (EVar "CasePair") (EVar "p")) (EVar "K")),
                    ("snd", ["p"], EAp (EAp (EVar "CasePair") (EVar "p")) (EVar "K1")),
                    ("head", ["l"], EAp (EAp (EAp (EVar "CaseList") (EVar "l")) (EVar "abort")) (EVar "K")),
                    ("tail", ["l"], EAp (EAp (EAp (EVar "CaseList") (EVar "l")) (EVar "abort")) (EVar "K1")),
                    ("printList", ["l"], EAp (EAp (EAp (EVar "CaseList") (EVar "l")) (EVar "stop")) (EVar "printCons")),
                    ("printCons", ["x", "xs"], EAp (EAp (EVar "print") (EVar "x")) (EAp (EVar "printList") (EVar "xs")))]

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (stack, dump, heap, globals, stats, output) =
    (stack, dump, heap, globals, f stats, output)

run :: String -> String
run = showResults . eval . compile . parse

compile :: CoreProgram -> TiState
compile program = (stack, tiDumpInitial, heap, globals, tiStatInitial, tiOutputInitial)
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
        (topAddr : rest, dump, heap, globals, stats, output) = state
        dispatch (NNum n) = numStep state n
        dispatch (NSc name args body) = scStep state name args body
        dispatch (NAp a1 a2) = apStep state a1 a2
        dispatch (NPrim name primitive) = primStep state name primitive
        dispatch (NInd addr) = (addr : rest, dump, heap, globals, stats, output)
        dispatch (NData tag args) = dataStep state tag args

numStep :: TiState -> Int -> TiState
numStep (stack, (head : dump), heap, globals, stats, output) n = trace ("jestem " ++ (show head)) (head, dump, heap, globals, stats, output)
numStep state n = error "Number at the top of the stack."

dataStep :: TiState -> Int -> [Addr] -> TiState
dataStep (stack, (head : dump), heap, globals, stats, output) tag args = (head, dump, heap, globals, stats, output)
dataStep state tag args = error "Data object at the top of the stack."

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats, output) a1 a2 =
    case hLookup heap a2 of
        (NInd addr) ->
            (stack, dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap topAddr $ NAp a1 addr
                (topAddr : addrs) = stack
        _ ->
            (a1 : stack, dump, heap, globals, stats, output)

primStep :: TiState -> Name -> Primitive -> TiState
primStep state name Neg = primNeg state
primStep state name Add = primArith state (+)
primStep state name Sub = primArith state (-)
primStep state name Mul = primArith state (*)
primStep state name Div = primArith state (div)
primStep state name (PrimConstr tag arity) = primConstr state tag arity
primStep state name If = primIf state
primStep state name Less = primComp state (<)
primStep state name LessEq = primComp state (<=)
primStep state name Eq = primComp state (==)
primStep state name Greater = primComp state (>)
primStep state name GreaterEq = primComp state (>=)
primStep state name PrimCasePair = primCasePair state
primStep state name PrimCons = primCons state
primStep state name PrimCaseList = primCaseList state
primStep state name Print = primPrint state
primStep state name Stop = primStop state


primStop :: TiState -> TiState
primStop (stack, [], heap, globals, stats, output) = ([], [], heap, globals, stats, output)
primStop (stack, dump, heap, globals, stats, output) = error "Dump not empty when calling Stop"

primPrint :: TiState -> TiState
primPrint (stack, dump, heap, globals, stats, output) =
    case argNode of
        (NNum n) ->
            (stack', dump, heap, globals, stats, output')
            where
                output' = output ++ [n]
                stack' = nextAddr : (drop 3 stack)
                nextAddr = getArg heap a2
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [argAddr]
                dump' = stack : dump
    where
        [a0, a1, a2] = take 3 stack
        argAddr = getArg heap a1
        argNode = hLookup heap argAddr

primCons :: TiState -> TiState
primCons (stack, dump, heap, globals, stats, output) =
    case restNode of
        (NData 4 _) ->
            (stack', dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap a2 $ NData 4 [elemAddr, restAddr]
                stack' = drop 2 stack
        (NNum _) ->
            error "Second argument to cons mustn't be a number"
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [restAddr]
                dump' = stack : dump
    where
        [a0, a1, a2] = take 3 stack
        elemAddr = getArg heap a1
        restAddr = getArg heap a2
        restNode = hLookup heap restAddr

primCaseList :: TiState -> TiState
primCaseList (stack, dump, heap, globals, stats, output) =
    case listNode of
        (NData 4 []) ->
            (stack', dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap a3 $ hLookup heap cnAddr
                stack' = drop 3 stack
        (NData 4 [x, xs]) ->
            (stack', dump, heap3, globals, stats, output)
            where
                heap1 = hUpdate heap a1 $ hLookup heap ccAddr
                heap2 = hUpdate heap1 a2 $ NAp a1 x
                heap3 = hUpdate heap2 a3 $ NAp a2 xs
                stack' = tail stack
        (NNum _) ->
            error "Second argument to cons mustn't be a number"
        (NInd addr) ->
            (stack, dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap listAddr $ hLookup heap addr
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [listAddr]
                dump' = stack : dump
    where
        [a0, a1, a2, a3] = take 4 stack
        listAddr = getArg heap a1
        cnAddr = getArg heap a2
        ccAddr = getArg heap a3
        listNode = hLookup heap listAddr

primCasePair :: TiState -> TiState
primCasePair (stack, dump, heap, globals, stats, output) =
    case pairNode of
        (NData 3 [arg1, arg2]) ->
            (stack', dump, heap2, globals, stats, output)
            where
                heap1 = hUpdate heap a1 $ NAp a0 arg1
                heap2 = hUpdate heap1 a2 $ NAp a1 arg2
                stack' = funAddr : (tail stack)
        (NInd addr) ->
            (stack, dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap pairAddr $ hLookup heap addr
        (NNum _) ->
            error "CasePair's first argument should be a pair"
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [pairAddr]
                dump' = stack : dump
    where
        [a0, a1, a2] = take 3 stack
        pairNode = hLookup heap pairAddr
        pairAddr = getArg heap a1
        funAddr = getArg heap a2

primIf :: TiState -> TiState
primIf (stack, dump, heap, globals, stats, output) =
    case condNode of
        (NData 1 []) -> -- False
            branch efAddr
        (NData 2 []) -> -- True
            branch etAddr
        (NInd addr) ->
            (stack', dump, heap', globals, stats, output)
            where
                stack' = tail stack
                heap' = hUpdate heap condAddr $ hLookup heap addr
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [condAddr]
                dump' = stack : dump
    where
        [a0, a1, a2, a3] = take 4 stack
        condAddr = getArg heap a1
        etAddr = getArg heap a2
        efAddr = getArg heap a3
        condNode = hLookup heap condAddr

        branch addr = (stack', dump, heap', globals, stats, output)
            where
                stack' = drop 3 stack
                heap' = hUpdate heap a3 $ NInd addr

primConstr :: TiState -> Int -> Int -> TiState
primConstr (stack, dump, heap, globals, stats, output) tag arity =
    trace ("**********" ++ show stack) (stack', dump, heap', globals, stats, output)
    where
        args = map (getArg heap) $ take arity $ tail stack
        heap' = hUpdate heap (stack !! arity) $ NData tag args
        stack' = drop arity stack

primDyadic :: TiState -> (Node -> Node -> Node) -> TiState
primDyadic (stack, dump, heap, globals, stats, output) comb =
    case node1 of
        (NNum v1) ->
            case trace ("jestem" ++ (show node1)) node2 of
                (NNum v2) ->
                    trace ("jestem" ++ (show node2)) (stack', dump, heap', globals, stats, output)
                    where
                        stack' = drop 2 stack
                        heap' = hUpdate heap root2 $ comb node1 node2
                (NInd a2) ->
                    (stack, dump, heap', globals, stats, output)
                    where
                        heap' = hUpdate heap addr2 (hLookup heap a2)
                _ ->
                    (stack', dump', heap, globals, stats, output)
                    where
                        stack' = [addr2]
                        dump' = stack : dump
                where
                    node2 = hLookup heap addr2
                    addr2 = getArg heap root2
                    root2 = stack !! 2
        (NInd a1) ->
            (stack, dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap addr1 (hLookup heap a1)
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [addr1]
                dump' = stack : dump
    where
        node1 = hLookup heap addr1
        addr1 = getArg heap root1
        root1 = stack !! 1

primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state op = primDyadic state nComb
    where
        nComb n1 n2 =
            NNum $ op v1 v2
            where
                (NNum v1) = n1
                (NNum v2) = n2

primComp :: TiState -> (Int -> Int -> Bool) -> TiState
primComp state op = primDyadic state nComb
    where
        nComb n1 n2 =
            case op v1 v2 of
                True ->
                    NData 2 []
                False ->
                    NData 1 []
            where
                (NNum v1) = n1
                (NNum v2) = n2

primNeg :: TiState -> TiState
primNeg (stack, dump, heap, globals, stats, output) =
    case trace ("primneg arg: " ++ (show node)) node of
        (NNum v) ->
            (stack', dump, heap', globals, stats, output)
            where
                heap' = hUpdate heap root (NNum $ -v)
                stack' = tail stack
        _ ->
            (stack', dump', heap, globals, stats, output)
            where
                stack' = [addr]
                dump' = (tail stack) : dump
    where
        node = hLookup heap addr
        addr = getArg heap root
        root = stack !! 1

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats, output) name argNames body =
    case (n + 1) <= length stack of
        True ->
            (stack', dump, heap2, globals, stats, output)
            where
                an = stack !! n
                stack' = resultAddr : (drop (n + 1) stack)
                (heap1, resultAddr) = instantiate body heap env
                heap2 = trace ("update: " ++ (show an) ++ ", " ++ (show resultAddr)) hUpdate heap1 an (NInd resultAddr)
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
    hAlloc heap $ NPrim "Pack" $ PrimConstr tag arity
--instantiate (EIf cond et ef) heap env =
--    hAlloc heap3 $ NIf condAddr etAddr efAddr
--    where
--        (heap1, condAddr) = instantiate cond heap env
--        (heap2, etAddr) = instantiate et heap1 env
--        (heap3, efAddr) = instantiate ef heap2 env
-- case expressions
instantiate (ECase expr alts)  heap env =
    error "Could not instantiate case expressions for the time being."

accumulate :: Assoc Name Addr -> (TiHeap, Assoc Name Addr) -> (Name, CoreExpr) -> (TiHeap, Assoc Name Addr)
accumulate env (heap, env1) (name, expr) =
    (heap1, (name, addr) : env1)
    where
        (heap1, addr) = instantiate expr heap env

tiFinal :: TiState -> Bool
tiFinal ([], [], heap, globals, stats, output) = True
tiFinal ([addr], [], heap, globals, stats, output) = isDataNode (hLookup heap addr)
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode (NData _ _) = True
isDataNode _ = False

showResults :: [TiState] -> String
showResults [] = ""
showResults ((stack, dump, heap, globals, stats, output) : rest) = "showresults: " ++ (show stack) ++ "output: " ++ (show output) ++ ": "  ++ showResults rest

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

