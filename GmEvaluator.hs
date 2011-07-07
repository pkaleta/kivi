module GmEvaluator where

--import Lexer
import Parser
import Utils
import List
--import Core
import Common
import Debug.Trace
import GmCompiler
import Text.Regex.Posix
import Data.List.Utils
import PatternMatching
import AbstractDataTypes
import LambdaLifter
import LazyLambdaLifter
import DependencyAnalyser
import LambdaCalculusTransformer
--import DependencyAnalyser
--import Gc


--run :: [Char] -> [Char]
--run = showResults . eval . compile . lambdaLift . lazyLambdaLift . analyseDeps . parse
--
--runS :: [Char] -> [Char]
--runS = show . lambdaLift . parse
--
--runF :: [Char] -> [Char]
--runF = show . lambdaLift . lazyLambdaLift . parse
--
--runD :: [Char] -> [Char]
--runD = show . analyseDeps . parse

runTest :: String -> CoreProgram
runTest = lambdaLift . lazyLambdaLift . analyseDeps . transformToLambdaCalculus . mergePatterns . tag . parse

run :: String -> String
run = showResults . eval . compile . lambdaLift . lazyLambdaLift . analyseDeps . transformToLambdaCalculus . mergePatterns . tag . parse

makeStr :: GmHeap -> Node -> String
makeStr heap (NNum n) = show n
makeStr heap (NAp a1 a2) = "(" ++ makeStr heap n1 ++ " " ++ makeStr heap n2 ++ ")"
    where
        n1 = hLookup heap a1
        n2 = hLookup heap a2
makeStr heap (NGlobal addr code) = "<fun " ++ show addr ++ ">"
makeStr heap (NInd addr) =
    case addr == hNull of
        True -> "NULL"
        False -> makeStr heap $ hLookup heap addr
makeStr heap (NConstr tag as) = "CONSTR " ++ show tag

showResults :: [GmState] -> [Char]
showResults [] = ""
showResults (state : states) =
    case length stack > 0 of
        True ->
            show stats ++ ": " ++ show output ++ "\ncode:" ++ show code ++ "\nstack: " ++ show stack ++ "\nvstack: " ++ show vstack ++ "\n" ++ show topNode ++ " (" ++ makeStr heap topNode ++ ")\n\n" ++ showResults states
            where
                topNode = (hLookup heap topAddr)
                topAddr = head $ getStack state
        False ->
            "output: " ++ show output ++ "\ncode" ++ show code ++ "\nstack: " ++ show stack ++ "\nvstack: " ++ show vstack ++ "\n\n" ++ showResults states
    where
        code = getCode state
        stack = getStack state
        heap = getHeap state
        vstack = getVStack state
        stats = getStats state
        output = getOutput state

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
dispatch Unwind              = unwind
dispatch (Pushglobal f)      = pushglobal f
dispatch (Pushint n)         = pushint n
dispatch (Push n)            = push n
dispatch Mkap                = mkap
dispatch (Update n)          = update n
dispatch (Pop n)             = pop n
dispatch (Slide n)           = slide n
dispatch (Alloc n)           = alloc n
dispatch Eval                = eval2
dispatch Add                 = add
dispatch Sub                 = sub
dispatch Mul                 = mul
dispatch Div                 = div2
dispatch Neg                 = neg
dispatch Eq                  = eq
dispatch Ne                  = ne
dispatch Lt                  = lt
dispatch Le                  = le
dispatch Gt                  = gt
dispatch Ge                  = ge
dispatch (Cond ist isf)      = cond ist isf
dispatch (Pack t n)          = pack t n
dispatch (CasejumpSimple bs) = casejumpSimple bs
dispatch (CasejumpConstr bs) = casejumpConstr bs
dispatch (Split n)           = split2 n
dispatch (Print)             = print2
dispatch (Pushbasic n)       = pushbasic n
dispatch (MkBool)            = mkbool
dispatch (MkInt)             = mkint
dispatch (Get)               = get
dispatch (Select r i)        = select r i
dispatch (Error msg)         = error2 msg

unwind :: GmState -> GmState
unwind state = newState (hLookup heap addr) state
    where
        heap = getHeap state
        addr = head $ getStack state

newState :: Node -> GmState -> GmState
newState (NNum n) state = unwindDump state
newState (NConstr t as) state = unwindDump state
newState (NAp a1 a2) state = putCode [Unwind] $ putStack (a1 : getStack state) state
newState (NGlobal argc code) state =
    case argc > length stack - 1 of -- if the number of arguments on the stack is not sufficient for this supercombinator
        True ->
            case dump of
                [] ->
                    error "Not enough arguments on the stack"
                ((is, as, vs) : dump') ->
                    putCode is $ putStack (last stack : as) $ putVStack vs state
        False ->
            putCode code $ putStack (rearrange argc heap stack) state
    where
        stack = getStack state
        heap = getHeap state
        dump = getDump state
newState (NInd addr) state = putCode [Unwind] $ putStack stack' state
    where
        stack' = addr : (tail $ getStack state)

unwindDump state =
    putCode code $ putStack (addr : stack) $ putVStack vstack $ putDump ds state
    where
        (code, stack, vstack) : ds = getDump state
        addr = head $ getStack state

pushglobal :: Name -> GmState -> GmState
pushglobal name state =
    case take 4 name == "Pack" of
        True -> pushglobalPack name state
        False -> pushglobalNormal name state

pushglobalPack :: Name -> GmState -> GmState
pushglobalPack name state =
    case aHasKey globals name of
        True ->
            putStack (addr : stack) state
            where
                addr = aLookup globals name $ error "This is not possible"
        False ->
            putStack (addr : stack) $ putHeap heap' state
            where
                (heap', addr) = hAlloc heap $ NGlobal n [Pack t n, Update 0, Unwind]
                [t, n] = map read $ Data.List.Utils.split "," (name =~ "[0-9]+,[0-9]+" :: String)
    where
        globals = getGlobals state
        stack = getStack state
        heap = getHeap state

pushglobalNormal :: Name -> GmState -> GmState
pushglobalNormal name state =
    putStack stack' state
    where
        addr = aLookup (getGlobals state) name $ error $ "Undeclared global identifier: " ++ name
        stack' = addr : getStack state

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
        dump' = (code, as, vstack) : getDump state
        code = getCode state
        (a : as) = getStack state
        vstack = getVStack state


select :: Int -> Int -> GmState -> GmState
select r i state = putStack stack' state
    where
        (a : as) = getStack state
        NConstr t args = hLookup heap a
        stack' = (args !! i) : as
        heap = getHeap state


error2 :: String -> GmState -> GmState
error2 = error


add :: GmState -> GmState
add = arithmetic2 (+)

sub :: GmState -> GmState
sub = arithmetic2 (-)

mul :: GmState -> GmState
mul = arithmetic2 (*)

div2 :: GmState -> GmState
div2 = arithmetic2 (div)

neg :: GmState -> GmState
neg = unaryOp negate

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
cond ist isf state =
    putCode code' $ putVStack vs state
    where
        (v : vs) = getVStack state
        code' = case v of
            0 -> ist ++ code
            1 -> isf ++ code
        code = getCode state

pack :: Int -> Int -> GmState -> GmState
pack t n state =
    putStack stack' $ putHeap heap' state
    where
        stack' = addr : (drop n stack)
        (heap', addr) = hAlloc (getHeap state) (NConstr t $ take n stack)
        stack = getStack state


casejumpSimple :: Assoc Int GmCode -> GmState -> GmState
casejumpSimple = casejump


casejumpConstr :: Assoc Int GmCode -> GmState -> GmState
casejumpConstr = casejump


casejump :: Assoc Int GmCode -> GmState -> GmState
casejump branches state =
    case findMatchingBranch branches node of
        (Just code') -> putCode (code' ++ code) state
        Nothing -> error "No suitable case branch found! This should not happen in a typechecked implementation!"
    where
        heap = getHeap state
        stack = getStack state
        node = hLookup heap $ head stack
        code = getCode state


findMatchingBranch :: Assoc Int GmCode -> Node -> Maybe GmCode
findMatchingBranch ([(-1, code)]) node = Just code
findMatchingBranch ((n, code) : bs) node@(NNum n')
    | n == n'   = Just code
    | otherwise = findMatchingBranch bs node
findMatchingBranch ((n, code) : bs) node@(NConstr tag args)
    | n == tag  = Just code
    | otherwise = findMatchingBranch bs node
findMatchingBranch ((n, code) : bs) node@(NGlobal r [Pack tag arity, _, _])
    | n == tag  = Just code
    | otherwise = findMatchingBranch bs node
findMatchingBranch branches node = Nothing


split2 :: Int -> GmState -> GmState
split2 n state =
    putStack stack' state
    where
        stack' = case n == length args of
            True -> args ++ as
            False -> error "Incorrect number of constructor parameters."
        (NConstr t args) = hLookup (getHeap state) a
        (a : as) = getStack state

print2 :: GmState -> GmState
print2 state =
    case hLookup (getHeap state) a of
        (NNum n) -> putOutput (output ++ show n ++ ", ") $ putStack as state
        (NConstr t as) -> putOutput output' $ putCode code' $ putStack stack' state
            where
                code' = (foldl (\acc arg -> acc ++ [Eval, Print]) [] as) ++ (getCode state)
                stack' = as ++ (getStack state)
                output' = output ++ "(NConstr " ++ show t ++ " ["
    where
        (a : as) = getStack state
        output = getOutput state

pushbasic :: Int -> GmState -> GmState
pushbasic v state = putVStack (v : vstack) state
    where
        vstack = getVStack state

mkint :: GmState -> GmState
mkint = mkobj (\v -> NNum v)

mkbool :: GmState -> GmState
mkbool = mkobj (\v -> NConstr v [])

mkobj :: (Int -> Node) -> GmState -> GmState
mkobj cn state = putStack (addr : stack) $ putHeap heap' $ putVStack vs state
    where
        (heap', addr) = hAlloc (getHeap state) $ cn v
        stack = getStack state
        (v : vs) = getVStack state

get :: GmState -> GmState
get state = putStack as $ putVStack vstack' state
    where
        (a : as) = getStack state
        vstack' = case hLookup (getHeap state) a of
            (NNum n) ->
                n : vstack
            (NConstr t []) ->
                t : vstack
        vstack = getVStack state

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
        (heap, addr) = hAlloc (getHeap state) $ NConstr b' []
        b' | b = 2
           | otherwise = 1

--not needed for the time being
--unboxBoolean :: Addr -> GmState -> Bool
--unboxBoolean addr state =
--    case hLookup (getHeap state) addr of
--        (NNum 0) -> False
--        (NNum 1) -> True
--        _ -> error "Trying to unbox value other than boolean"

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
--arithmetic2 = primitive2 boxInteger unboxInteger
arithmetic2 op = binOp op

relational2 :: (Int -> Int -> Bool) -> (GmState -> GmState)
--relational2 = primitive2 boxBoolean unboxInteger
relational2 op = binOp fun
    where
        fun x y = case (op x y) of
            True -> 0
            False -> 1

binOp :: (Int -> Int -> Int) -> GmState -> GmState
binOp op state = putVStack vstack' state
    where
        vstack' = (op v1 v2) : vs
        (v1 : v2 : vs) = getVStack state

unaryOp :: (Int -> Int) -> GmState -> GmState
unaryOp op state = putVStack ((op v) : vs) state
    where
        (v : vs) = getVStack state


