module Common where

-- Utils
type Addr = Int
type Assoc a b = [(a, b)]
type Heap a = (Int, [Addr], Assoc Addr a)

-- Parser
data Expr a
    = EVar Name                             -- variables
    | ENum Int                              -- numbers
    | EConstr Int Int                       -- constructor (tag, arity)
    | EAp (Expr a) (Expr a)                 -- applications
    | ELet IsRec [(a, Expr a)] (Expr a)     -- let(rec) expressions (is recursive, definitions, body)
    | ECase (Expr a) [Alter a]              -- case expression (expression, alternatives)
    | ELam [a] (Expr a)                     -- lambda abstractions
    deriving (Show)

type CoreExpr = Expr Name
type IsRec = Bool
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name
type Program a = [ScDefn a]
type CoreProgram = Program Name
type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name
type Defn a = (a, Expr a)
type CoreDefn = Defn Name

type Name = String

-- GmEvaluator
type GmState = (GmCode,
                GmStack,
                GmHeap,
                GmGlobals,
                GmStats)

type GmCode = [Instruction]

data Instruction = Unwind
                 | Pushglobal Name
                 | Pushint Int
                 | Push Int
                 | Mkap
                 | Update Int
                 | Pop Int
    deriving Show

instance Eq Instruction
    where
        Unwind == Unwind = True
        Pushglobal a == Pushglobal b = a == b
        Pushint a == Pushint b = a == b
        Push a == Push b = a == b
        Mkap == Mkap = True
        Update a == Update b = a == b
        Pop a == Pop b = a == b
        _ == _ = False

type GmStack = [Addr]

type GmHeap = Heap Node

data Node = NNum Int            -- numbers
          | NAp Addr Addr       -- applications
          | NGlobal Int GmCode  -- global names (functions, numbers, variables, etc.)
          | NInd Addr           -- indirection nodes (updating the root of redex)
    deriving Show

type GmGlobals = Assoc Name Addr

type GmStats = Int

getCode :: GmState -> GmCode
getCode (code, stack, heap, globals, stats) = code

putCode :: GmCode -> GmState -> GmState
putCode code' (code, stack, heap, globals, stats) = (code', stack, heap, globals, stats)

getStack :: GmState -> GmStack
getStack (code, stack, heap, globals, stats) = stack

putStack :: GmStack -> GmState -> GmState
putStack stack' (code, stack, heap, globals, stats) = (code, stack', heap, globals, stats)

getHeap :: GmState -> GmHeap
getHeap (code, stack, heap, globals, stats) = heap

putHeap :: GmHeap -> GmState -> GmState
putHeap heap' (code, stack, heap, globals, stats) = (code, stack, heap', globals, stats)

getGlobals :: GmState -> GmGlobals
getGlobals (code, stack, heap, globals, stats) = globals

putGlobals :: GmGlobals -> GmState -> GmState
putGlobals globals' (code, stack, heap, globals, stats) = (code, stack, heap, globals', stats)

getStats :: GmState -> GmStats
getStats (code, stack, heap, globals, stats) = stats

putStats :: GmStats -> GmState -> GmState
putStats stats' (code, stack, heap, globals, stats) = (code, stack, heap, globals, stats')

initialStats :: GmStats
initialStats = 0

statGetSteps :: GmStats -> Int
statGetSteps s = s

statIncSteps :: GmStats -> GmStats
statIncSteps s = s+1

