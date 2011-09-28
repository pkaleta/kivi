module GmEvaluator where

import Parser
import Utils
import List
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
import TypeChecker
import Data.Char


--runTest :: String -> CoreProgram
runTest = typeCheck
        . analyseDeps
        . lambdaLift
        . lazyLambdaLift
        . transformToLambdaCalculus
        . mergePatterns
        . tag
        . parse

run :: String -> String
run = concat
      . intersperse "\n\n"
      . map show
      . eval
      . compile
      . analyseDeps
      . lambdaLift
      . lazyLambdaLift
      . transformToLambdaCalculus
      . mergePatterns
      . tag
      . parse


eval :: GmState -> [GmState]
eval state = state : restStates
    where
        restStates | gmFinal state = []
                   | otherwise = eval nextState
        nextState = doAdmin $ step state

doAdmin :: GmState -> GmState
doAdmin state = state { gmstats = statIncSteps $ gmstats state }


gmFinal :: GmState -> Bool
gmFinal state =
    case gmcode state of
        [] -> True
        _ -> False

step :: GmState -> GmState
step state =
    dispatch i $ state { gmcode = is }
    where
        (i : is) = gmcode state

dispatch :: Instruction -> GmState -> GmState
dispatch Unwind              = unwind
dispatch (Pushglobal f)      = pushglobal f
dispatch (Pushconstr t a)    = pushconstr t a
dispatch (Pushint n)         = pushint n
dispatch (Pushchar c)        = pushchar c
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
dispatch Mod                 = mod2
dispatch Neg                 = neg
dispatch Eq                  = eq
dispatch Ne                  = ne
dispatch Lt                  = lt
dispatch Le                  = le
dispatch Gt                  = gt
dispatch Ge                  = ge
dispatch (Pack t n)          = pack t n
dispatch (CasejumpSimple bs) = casejump bs
dispatch (CasejumpConstr bs) = casejump bs
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
        heap = gmheap state
        addr = head $ gmstack state

newState :: Node -> GmState -> GmState
newState (NNum n) state = unwindDump state
newState (NChar c) state = unwindDump state
newState (NConstr t as) state = unwindDump state
newState (NAp a1 a2) state = state { gmcode = [Unwind], gmstack = (a1 : gmstack state) }
newState (NGlobal argc code) state =
    case argc > length stack - 1 of -- if the number of arguments on the stack is not sufficient for this supercombinator
        True ->
            case dump of
                [] ->
                    error "Not enough arguments on the stack"
                ((is, as, vs) : dump') ->
                    state { gmcode = is, gmstack = last stack : as, gmvstack = vs }
        False ->
            state { gmcode = code, gmstack = (rearrange argc heap stack) }
    where
        stack = gmstack state
        heap = gmheap state
        dump = gmdump state
newState (NInd addr) state = state { gmcode = [Unwind], gmstack = stack' }
    where
        stack' = addr : (tail $ gmstack state)

unwindDump state =
    state { gmcode = code, gmstack = (addr : stack), gmvstack = vstack, gmdump = ds }
    where
        (code, stack, vstack) : ds = gmdump state
        addr = head $ gmstack state


pushglobal :: Name -> GmState -> GmState
pushglobal name state =
  state { gmstack = stack' }
  where
    addr = aLookup (gmglobals state) name $ error $ "Undeclared global identifier: " ++ name
    stack' = addr : gmstack state


pushconstr :: Int -> Int -> GmState -> GmState
pushconstr tag arity state =
    case aHasKey globals name of
        True ->
            state { gmstack = addr : stack }
            where
                addr = aLookup globals name $ error "This is not possible"
        False ->
            state { gmstack = stack', gmheap = heap', gmglobals = globals' }
            where
                globals' = (name, addr) : globals
                stack' = addr : stack
                (heap', addr) = hAlloc heap $ NGlobal arity [Pack tag arity, Update 0, Unwind]
    where
        name = "Pack{" ++ show tag ++ "," ++ show arity ++ "}"
        globals = gmglobals state
        stack = gmstack state
        heap = gmheap state


pushgen :: Int -> (Int -> String) -> (Int -> Node) -> GmState -> GmState
pushgen v mkStr mkNode state =
    case aLookup globals str (-1) of
        -1 ->
            state { gmstack = stack', gmheap = heap', gmglobals = globals' }
            where
                (heap', addr) = hAlloc heap $ mkNode v
                stack' = addr : stack
                globals' = (str, addr) : globals
        addr ->
            state { gmstack = stack' }
            where
                stack' = addr : stack
    where
        heap = gmheap state
        stack = gmstack state
        globals = gmglobals state
        str = mkStr v


pushint :: Int -> GmState -> GmState
pushint n = pushgen n show NNum

pushchar :: Int -> GmState -> GmState
pushchar c = pushgen c (show . chr) NChar


mkap :: GmState -> GmState
mkap state =
    state { gmstack = addr : addrs, gmheap = heap' }
    where
        (heap', addr) = hAlloc (gmheap state) $ NAp a1 a2
        (a1 : a2 : addrs) = gmstack state

push :: Int -> GmState -> GmState
push n state =
    state { gmstack = stack' }
    where
        stack' = argAddr : stack
        argAddr = stack !! n
        stack = gmstack state

update :: Int -> GmState -> GmState
update n state = state { gmstack = as, gmheap = heap' }
    where
        heap' = hUpdate (gmheap state) redexRoot $ NInd a
        redexRoot = as !! n
        a : as = gmstack state

pop :: Int -> GmState -> GmState
pop n state = state { gmstack = drop n $ gmstack state }

slide :: Int -> GmState -> GmState
slide n state = state { gmstack = a : drop n as }
    where
        (a : as) = gmstack state

alloc :: Int -> GmState -> GmState
alloc n state = state { gmstack = stack', gmheap = heap' }
    where
        (heap', as) = allocNodes n $ gmheap state
        stack' = as ++ (gmstack state)

allocNodes :: Int -> GmHeap -> (GmHeap, [Addr])
allocNodes 0 heap = (heap, [])
allocNodes n heap = (heap1, a : as)
    where
        (heap0, as) = allocNodes (n - 1) heap
        (heap1, a) = hAlloc heap0 $ NInd hNull

eval2 :: GmState -> GmState
eval2 state =
    state { gmcode = [Unwind], gmstack = [a], gmdump = dump' }
    where
        dump' = (code, as, vstack) : gmdump state
        code = gmcode state
        (a : as) = gmstack state
        vstack = gmvstack state


select :: Int -> Int -> GmState -> GmState
select r i state = state { gmstack = stack' }
    where
        (a : as) = gmstack state
        NConstr t args = hLookup heap a
        stack' = (args !! i) : as
        heap = gmheap state


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

mod2 :: GmState -> GmState
mod2 = arithmetic2 (rem)

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


pack :: Int -> Int -> GmState -> GmState
pack t n state =
    state { gmstack = stack', gmheap = heap' }
    where
        stack' = addr : (drop n stack)
        (heap', addr) = hAlloc (gmheap state) (NConstr t $ take n stack)
        stack = gmstack state


casejump :: Assoc Int GmCode -> GmState -> GmState
casejump branches state =
    case findMatchingBranch branches node of
        (Just code') -> state { gmcode = (code' ++ code) }
        Nothing -> error "No suitable case branch found! This should not happen in a typechecked implementation!"
    where
        heap = gmheap state
        stack = gmstack state
        node = hLookup heap $ head stack
        code = gmcode state


findMatchingBranch :: Assoc Int GmCode -> Node -> Maybe GmCode
findMatchingBranch ([(-1, code)]) node = Just code
findMatchingBranch ((n, code) : bs) node@(NNum n')
    | n == n'   = Just code
    | otherwise = findMatchingBranch bs node
findMatchingBranch ((n, code) : bs) node@(NChar n')
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
    state { gmstack = stack' }
    where
        stack' = case n == length args of
            True -> args ++ as
            False -> error "Incorrect number of constructor parameters."
        (NConstr t args) = hLookup (gmheap state) a
        (a : as) = gmstack state

print2 :: GmState -> GmState
print2 state =
    case hLookup (gmheap state) a of
        (NNum n) -> state { gmoutput = (output ++ show n ++ ", "), gmstack = as }
        (NChar c) -> state { gmoutput = (output ++ (show . chr $ c) ++ ", "), gmstack = as }
        (NConstr t as) -> state { gmoutput = output', gmcode = code', gmstack = stack' }
            where
                code' = (foldl (\acc arg -> acc ++ [Eval, Print]) [] as) ++ (gmcode state)
                stack' = as ++ stack
                output' = output ++ "(NConstr " ++ show t ++ " ["
    where
        stack@(a : as) = gmstack state
        output = gmoutput state

pushbasic :: Int -> GmState -> GmState
pushbasic v state = state { gmvstack = (v : vstack) }
    where
        vstack = gmvstack state

mkint :: GmState -> GmState
mkint = mkobj (\v -> NNum v)

mkbool :: GmState -> GmState
mkbool = mkobj (\v -> NConstr v [])

mkobj :: (Int -> Node) -> GmState -> GmState
mkobj cn state = state { gmstack = (addr : stack), gmheap = heap', gmvstack = vs }
    where
        (heap', addr) = hAlloc (gmheap state) $ cn v
        stack = gmstack state
        (v : vs) = gmvstack state

get :: GmState -> GmState
get state = state { gmstack = as, gmvstack = vstack' }
    where
        (a : as) = gmstack state
        vstack' = case hLookup (gmheap state) a of
            (NNum n) ->
                n : vstack
            (NConstr t []) ->
                t : vstack
        vstack = gmvstack state

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2

rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap stack =
    addrs ++ drop n stack
    where
        addrs = map (getArg . hLookup heap) (take n $ tail stack)

boxInteger :: Int -> GmState -> GmState
boxInteger n state =
    state { gmstack = (addr : stack), gmheap = heap }
    where
        (heap, addr) = hAlloc (gmheap state) $ NNum n
        stack = gmstack state

unboxInteger :: Addr -> GmState -> Int
unboxInteger addr state =
    case hLookup (gmheap state) addr of
        (NNum n) -> n
        _ -> error "Trying to unbox value other than integer"

boxBoolean :: Bool -> GmState -> GmState
boxBoolean b state =
    state { gmstack = (addr : stack), gmheap = heap }
    where
        stack = gmstack state
        (heap, addr) = hAlloc (gmheap state) $ NConstr b' []
        b' | b = 2
           | otherwise = 1

--not needed for the time being
--unboxBoolean :: Addr -> GmState -> Bool
--unboxBoolean addr state =
--    case hLookup (gmheap state) addr of
--        (NNum 0) -> False
--        (NNum 1) -> True
--        _ -> error "Trying to unbox value other than boolean"

primitive1 :: (b -> GmState -> GmState) ->
              (Addr -> GmState -> a) ->
              (a -> b) ->
              (GmState -> GmState)
primitive1 box unbox op state =
    box (op (unbox a state)) (state { gmstack = as })
    where
        (a : as) = gmstack state

primitive2 :: (b -> GmState -> GmState) ->
              (Addr -> GmState -> a) ->
              (a -> a -> b) ->
              (GmState -> GmState)
primitive2 box unbox op state =
    box (op a1 a2) (state { gmstack = as })
    where
        a1 = unbox addr1 state
        a2 = unbox addr2 state
        (addr1 : addr2 : as) = gmstack state

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
            True -> trueTag
            False -> falseTag

binOp :: (Int -> Int -> Int) -> GmState -> GmState
binOp op state = state { gmvstack = vstack' }
    where
        vstack' = (op v1 v2) : vs
        (v1 : v2 : vs) = gmvstack state

unaryOp :: (Int -> Int) -> GmState -> GmState
unaryOp op state = state { gmvstack = ((op v) : vs) }
    where
        (v : vs) = gmvstack state


