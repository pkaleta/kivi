module Common where


import Utils


-- Parser
data Expr a
    = EVar Name                             -- variables
    | ENum Int                              -- numbers
    | EConstrName Name
    | EConstr Int Int                       -- constructor (tag, arity)
    | EAp (Expr a) (Expr a)                 -- applications
    | ELet IsRec [Defn a] (Expr a)          -- let(rec) expressions (is recursive, definitions, body)
    | ECase (Expr a) [Alter a]              -- case expression (expression, alternatives)
    | ELam [a] (Expr a)                     -- lambda abstractions
--    | Fatbar (Expr a) (Expr a)
    | EError String
    | ESelect Int Int Name
    deriving (Show)


data ProgramElement a = ScDefn Name [a] (Expr a)
                      | DataType Name [Constructor]
    deriving (Show)

type Constructor = (Name, Int, Int)
type CoreExpr = Expr Name
type IsRec = Bool
type Alter a = (Pattern, Expr a)
type CoreAlt = Alter Name
type Program a = ([ProgramElement a], [ProgramElement a])
type CoreProgram = ([ProgramElement Name], [ProgramElement Name])
type Defn a = (a, Expr a)
type CoreDefn = Defn Name
type Name = String


data Pattern = PNum Int
             | PVar Name
             | PConstrName Name [Pattern]
             | PConstr Int Int [Pattern]
             | PDefault
    deriving (Show)


-- GmEvaluator
type GmState = (GmOutput,
                GmCode,
                GmStack,
                GmDump,
                GmVStack,
                GmHeap,
                GmGlobals,
                GmStats)

type GmVStack = [Int]

type GmOutput = [Char]

type GmCode = [Instruction]

data Instruction = Unwind
                 | Pushglobal Name
                 | Pushint Int
                 | Push Int
                 | Mkap
                 | Update Int
                 | Pop Int
                 | Slide Int
                 | Alloc Int
                 | Eval
                 | Add | Sub | Mul | Div | Neg
                 | Eq | Ne | Lt | Le | Gt | Ge
                 | Cond GmCode GmCode
                 | Pack Int Int
                 | Casejump (Assoc Pattern GmCode)
                 | Select Int Int
                 | Error String
                 | Split Int
                 | Print
                 | Pushbasic Int
                 | MkBool
                 | MkInt
                 | Get
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
        Slide a == Slide b = a == b
        Alloc a == Alloc b = a == b
        _ == _ = False

type GmStack = [Addr]

type GmDump = [GmDumpItem]

type GmDumpItem = (GmCode, GmStack, GmVStack)

type GmHeap = Heap Node

data Node = NNum Int            -- numbers
          | NAp Addr Addr       -- applications
          | NGlobal Int GmCode  -- global names (functions, numbers, variables, etc.)
          | NInd Addr           -- indirection nodes (updating the root of redex)
          | NConstr Int [Addr]  -- constructor nodes
    deriving Show
instance Eq Node
    where
        NNum a == NNum b = a == b
        NAp a b == NAp c d = a == b && c == d
        NGlobal a b == NGlobal c d = False
        NInd a == NInd b = a == b
        NConstr a b == NConstr c d = False

type GmGlobals = Assoc Name Addr

type GmStats = Int

getOutput :: GmState -> GmOutput
getOutput (output, code, stack, dump, vstack, heap, globals, stats) = output

putOutput :: GmOutput -> GmState -> GmState
putOutput output' (output, code, stack, dump, vstack, heap, globals, stats) = (output', code, stack, dump, vstack, heap, globals, stats)

getCode :: GmState -> GmCode
getCode (output, code, stack, dump, vstack, heap, globals, stats) = code

putCode :: GmCode -> GmState -> GmState
putCode code' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code', stack, dump, vstack, heap, globals, stats)

getStack :: GmState -> GmStack
getStack (output, code, stack, dump, vstack, heap, globals, stats) = stack

putStack :: GmStack -> GmState -> GmState
putStack stack' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code, stack', dump, vstack, heap, globals, stats)

getDump :: GmState -> GmDump
getDump (output, code, stack, dump, vstack, heap, globals, stats) = dump

putDump :: GmDump -> GmState -> GmState
putDump dump' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code, stack, dump', vstack, heap, globals, stats)

getVStack:: GmState -> GmVStack
getVStack (output, code, stack, dump, vstack, heap, globals, stats) = vstack

putVStack :: GmVStack-> GmState -> GmState
putVStack vstack' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code, stack, dump, vstack', heap, globals, stats)

getHeap :: GmState -> GmHeap
getHeap (output, code, stack, dump, vstack, heap, globals, stats) = heap

putHeap :: GmHeap -> GmState -> GmState
putHeap heap' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code, stack, dump, vstack, heap', globals, stats)

getGlobals :: GmState -> GmGlobals
getGlobals (output, code, stack, dump, vstack, heap, globals, stats) = globals

putGlobals :: GmGlobals -> GmState -> GmState
putGlobals globals' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code, stack, dump, vstack, heap, globals', stats)

getStats :: GmState -> GmStats
getStats (output, code, stack, dump, vstack, heap, globals, stats) = stats

putStats :: GmStats -> GmState -> GmState
putStats stats' (output, code, stack, dump, vstack, heap, globals, stats) = (output, code, stack, dump, vstack, heap, globals, stats')

initialStats :: GmStats
initialStats = 0

statGetSteps :: GmStats -> Int
statGetSteps s = s

statIncSteps :: GmStats -> GmStats
statIncSteps s = s+1

