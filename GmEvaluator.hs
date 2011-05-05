module GmEvaluator where

--import Lexer
import Parser
import Utils
import List
--import Core
import Common
import Debug.Trace
import GmCompiler
--import Gc


compiledPrimitives :: [GmCompiledSc]
compiledPrimitives = []

run :: [Char] -> [Char]
run = showResults . eval . compile . parse

showResults :: [GmState] -> [Char]
showResults [] = ""
showResults (state : states) =
    case length stack > 0 of
        True ->
            show code ++ ", " ++ show stack ++ ", " ++ show topNode ++ "\n\n" ++ showResults states
            where
                topNode = (hLookup heap topAddr)
                topAddr = head $ getStack state
        False ->
            show code ++ ", " ++ show stack ++ "\n\n" ++ showResults states
    where
        code = getCode state
        stack = getStack state
        heap = getHeap state

eval :: GmState -> [GmState]
eval state = state : restStates
    where
        restStates | gmFinal state = []
                   | otherwise = eval nextState
        nextState = doAdmin $ step state

doAdmin :: GmState -> GmState
doAdmin state = putStats (statIncSteps $ getStats state) state

gmFinal :: GmState -> Bool
gmFinal state =
    case getCode state of
        [] -> True
        _ -> False

step :: GmState -> GmState
step state =
    dispatch i $ putCode is state
    where
        (i : is) = getCode state

dispatch :: Instruction -> GmState -> GmState
dispatch Unwind         = unwind
dispatch (Pushglobal f) = pushglobal f
dispatch (Pushint n)    = pushint n
dispatch (Push n)       = push n
dispatch Mkap           = mkap
dispatch (Slide n)      = slide n

pushglobal :: Name -> GmState -> GmState
pushglobal name state =
    putStack (addr : getStack state) state
    where
        addr = aLookup (getGlobals state) name $ error $ "Undeclared global identifier: " ++ name

pushint :: Int -> GmState -> GmState
pushint n state =
    putStack stack' $ putHeap heap' state
    where
        (heap', addr) = hAlloc (getHeap state) $ NNum n
        stack' = addr : getStack state

mkap :: GmState -> GmState
mkap state =
    putStack (addr : addrs) $ putHeap heap' state
    where
        (heap', addr) = hAlloc (getHeap state) $ NAp a1 a2
        (a1 : a2 : addrs) = getStack state

push :: Int -> GmState -> GmState
push n state =
    putStack stack' state
    where
        stack' = argAddr : stack
        argAddr = getArg $ hLookup (getHeap state) (stack !! (n + 1))
        stack = getStack state

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2

slide :: Int -> GmState -> GmState
slide n state = putStack (a : drop n as) state
    where
        (a : as) = getStack state

unwind :: GmState -> GmState
unwind state = newState (hLookup heap addr) state
    where
        heap = getHeap state
        addr = head $ getStack state

newState :: Node -> GmState -> GmState
newState (NNum n) state = state
newState (NAp a1 a2) state = putCode [Unwind] $ putStack (a1 : getStack state) state
newState (NGlobal argc code) state =
    case argc > length args of
        True -> error "Not enought arguments on the stack"
        False -> putCode code state
    where
        (a : args) = getStack state

