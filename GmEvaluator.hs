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


run :: [Char] -> [Char]
run = showResults . eval . compile . parse

showResults :: [GmState] -> [Char]
showResults [] = ""
showResults (state : states) =
    case length stack > 0 of
        True ->
            show stats ++ ": " ++ show code ++ ", " ++ show stack ++ ", " ++ show topNode ++ "\n\n" ++ showResults states
            where
                topNode = (hLookup heap topAddr)
                topAddr = head $ getStack state
        False ->
            show code ++ ", " ++ show stack ++ "\n\n" ++ showResults states
    where
        code = getCode state
        stack = getStack state
        heap = getHeap state
        stats = getStats state

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
dispatch (Update n)     = update n
dispatch (Pop n)        = pop n
dispatch (Slide n)      = slide n
dispatch (Alloc n)      = alloc n
dispatch Eval           = eval2
dispatch Add            = add
dispatch Sub            = sub
dispatch Mul            = mul
dispatch Div            = div2
dispatch Neg            = neg
dispatch Eq             = eq
dispatch Ne             = ne
dispatch Lt             = lt
dispatch Le             = le
dispatch Gt             = gt
dispatch Ge             = ge
dispatch (Cond i1 i2)   = cond i1 i2

unwind :: GmState -> GmState
unwind state = newState (hLookup heap addr) state
    where
        heap = getHeap state
        addr = head $ getStack state

newState :: Node -> GmState -> GmState
newState (NNum n) state =
    putCode code $ putStack (addr : stack) $ putDump ds state
    where
        d : ds = getDump state
        (code, stack) = d
        addr = head $ getStack state
newState (NAp a1 a2) state = putCode [Unwind] $ putStack (a1 : getStack state) state
newState (NGlobal argc code) state =
    case argc > length stack - 1 of
        True ->
            case dump of
                [] ->
                    error "Not enough arguments on the stack"
                ((is, as) : dump') ->
                    putCode is $ putStack (head stack : as) state
        False ->
            putCode code $ putStack (rearrange argc heap stack) state
    where
        stack = getStack state
        heap = getHeap state
        dump = getDump state
newState (NInd addr) state = putCode [Unwind] $ putStack stack' state
    where
        stack' = addr : (tail $ getStack state)

pushglobal :: Name -> GmState -> GmState
pushglobal name state =
    putStack (addr : getStack state) state
    where
        addr = aLookup (getGlobals state) name $ error $ "Undeclared global identifier: " ++ name

pushint :: Int -> GmState -> GmState
pushint n state =
    case aLookup globals numStr (-1) of
        -1 ->
            putStack stack' $ putHeap heap' $ putGlobals globals' state
            where
                (heap', addr) = hAlloc heap $ NNum n
                stack' = addr : stack
                globals' = (numStr, addr) : globals
        addr ->
            putStack stack' state
            where
                stack' = addr : stack
    where
        heap = getHeap state
        stack = getStack state
        globals = getGlobals state
        numStr = show n

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
        argAddr = stack !! n
        stack = getStack state

update :: Int -> GmState -> GmState
update n state = putStack as $ putHeap heap' state
    where
        heap' = hUpdate (getHeap state) redexRoot $ NInd a
        redexRoot = as !! n
        a : as = getStack state

pop :: Int -> GmState -> GmState
pop n state = putStack (drop n $ getStack state) state

slide :: Int -> GmState -> GmState
slide n state = putStack (a : drop n as) state
    where
        (a : as) = getStack state

alloc :: Int -> GmState -> GmState
alloc n state = putStack stack' $ putHeap heap' state
    where
        (heap', as) = allocNodes n $ getHeap state
        stack' = as ++ (getStack state)

allocNodes :: Int -> GmHeap -> (GmHeap, [Addr])
allocNodes 0 heap = (heap, [])
allocNodes n heap = (heap1, a : as)
    where
        (heap0, as) = allocNodes (n - 1) heap
        (heap1, a) = hAlloc heap0 $ NInd hNull

eval2 :: GmState -> GmState
eval2 state =
    putCode [Unwind] $ putStack [a] $ putDump dump' state
    where
        dump' = (code, as) : getDump state
        code = getCode state
        (a : as) = getStack state

add :: GmState -> GmState
add = arithmetic2 (+)

sub :: GmState -> GmState
sub = arithmetic2 (-)

mul :: GmState -> GmState
mul = arithmetic2 (*)

div2 :: GmState -> GmState
div2 = arithmetic2 (div)

neg :: GmState -> GmState
neg = arithmetic1 negate

eq :: GmState -> GmState
eq = relational2 (==)

ne :: GmState -> GmState
ne = relational2 (/=)

lt :: GmState -> GmState
lt = relational2 (<)

le :: GmState -> GmState
le = relational2 (<=)

gt :: GmState -> GmState
gt = relational2 (>)

ge :: GmState -> GmState
ge = relational2 (>=)

cond :: GmCode -> GmCode -> GmState -> GmState
cond i1 i2 state =
    putCode code' $ putStack as state
    where
        code = getCode state
        (a : as) = getStack state
        code' = case hLookup (getHeap state) a of
            (NNum 1) -> i1 ++ code
            (NNum 0) -> i2 ++ code

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2

rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap stack =
    addrs ++ drop n stack
    where
        addrs = map (getArg . hLookup heap) (take n $ tail stack)

boxInteger :: Int -> GmState -> GmState
boxInteger n state =
    putStack (addr : stack) $ putHeap heap state
    where
        (heap, addr) = hAlloc (getHeap state) $ NNum n
        stack = getStack state

unboxInteger :: Addr -> GmState -> Int
unboxInteger addr state =
    case hLookup (getHeap state) addr of
        (NNum n) -> n
        _ -> error "Trying to unbox value other than integer"

boxBoolean :: Bool -> GmState -> GmState
boxBoolean b state =
    putStack (addr : stack) $ putHeap heap state
    where
        stack = getStack state
        (heap, addr) = hAlloc (getHeap state) $ NNum b'
        b' | b = 1
           | otherwise = 0

unboxBoolean :: Addr -> GmState -> Bool
unboxBoolean addr state =
    case hLookup (getHeap state) addr of
        (NNum 0) -> False
        (NNum 1) -> True
        _ -> error "Trying to unbox value other than boolean"

primitive1 :: (b -> GmState -> GmState) ->
              (Addr -> GmState -> a) ->
              (a -> b) ->
              (GmState -> GmState)
primitive1 box unbox op state =
    box (op (unbox a state)) (putStack as state)
    where
        (a : as) = getStack state

primitive2 :: (b -> GmState -> GmState) ->
              (Addr -> GmState -> a) ->
              (a -> a -> b) ->
              (GmState -> GmState)
primitive2 box unbox op state =
    box (op a1 a2) (putStack as state)
    where
        a1 = unbox addr1 state
        a2 = unbox addr2 state
        (addr1 : addr2 : as) = getStack state

arithmetic1 :: (Int -> Int) -> (GmState -> GmState)
arithmetic1 = primitive1 boxInteger unboxInteger

arithmetic2 :: (Int -> Int -> Int) -> (GmState -> GmState)
arithmetic2 = primitive2 boxInteger unboxInteger

relational2 :: (Int -> Int -> Bool) -> (GmState -> GmState)
relational2 = primitive2 boxBoolean unboxInteger

