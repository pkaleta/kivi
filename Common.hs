module Common where


import Utils
import Data.String.Utils
import Data.Char


-- Parser
data Expr a
    = EVar Name                             -- variables
    | ENum Int                              -- numbers
    | EChar Int
    | EConstrName Name
    | EConstr Int Int                       -- constructor (tag, arity)
    | EAp (Expr a) (Expr a)                 -- applications
    | ELet IsRec [Defn a] (Expr a)          -- let(rec) expressions (is recursive, definitions, body)
    | ECase (Expr a) [Alter Pattern a]      -- case expression (expression, alternatives)
    | ECaseSimple (Expr a) [Alter Int a]
    | ECaseConstr (Expr a) [Alter Int a]
    | ELam [a] (Expr a)                     -- lambda abstractions
--    | Fatbar (Expr a) (Expr a)
    | EError String
    | ESelect Int Int Name


instance Show a => Show (Expr a) where
    show = showExpr


type CoreScDefn = ScDefn Name
data ScDefn a = ScDefn Name [a] (Expr a)
type DataType = (Name, [Constructor])
type Constructor = (Name, Int, Int)
type CoreExpr = Expr Name
type IsRec = Bool
type Alter b a = (b, Expr a)
type CoreAlt = Alter Int Name
type Program a = ([DataType], [ScDefn a])
type CoreProgram = ([DataType], [CoreScDefn])
type Defn a = (a, Expr a)
type CoreDefn = Defn Name
type Name = String


instance Show a => Show (ScDefn a) where
    show = showScDefn


data Pattern = PNum Int
             | PVar Name
             | PChar Int
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
                 | Pushconstr Int Int
                 | Pushint Int
                 | Pushchar Int
                 | Push Int
                 | Mkap
                 | Update Int
                 | Pop Int
                 | Slide Int
                 | Alloc Int
                 | Eval
                 | Add | Sub | Mul | Div | Neg | Mod
                 | Eq | Ne | Lt | Le | Gt | Ge
                 | Pack Int Int
                 | CasejumpSimple (Assoc Int GmCode)
                 | CasejumpConstr (Assoc Int GmCode)
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
        Pushchar a == Pushchar b = a == b
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
          | NChar Int
          | NAp Addr Addr       -- applications
          | NGlobal Int GmCode  -- global names (functions, numbers, variables, etc.)
          | NInd Addr           -- indirection nodes (updating the root of redex)
          | NConstr Int [Addr]  -- constructor nodes
          | NMarked Node
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


showExpr :: Show a => Expr a -> String
showExpr = showExpr' 0


showExpr' :: Show a => Int -> Expr a -> String
showExpr' indent (EVar v) = v
showExpr' indent (ENum n) = show n
showExpr' indent (EChar c) = show . chr $ c
showExpr' indent (EConstrName name) = name
--TODO: retrieve the name of constructor
showExpr' indent (EConstr t a) = "CONSTR" ++ show t
showExpr' indent (EAp e1 e2) = "(" ++ showExpr' indent e1 ++ " " ++ showExpr' indent e2 ++ ")"
showExpr' indent (ELet isRec defns expr) =
    letKeyword ++ defnsStr ++ "\n" ++ getIndent indent ++ "in\n" ++ getIndent (indent+1) ++ showExpr' (indent+1) expr
    where
        letKeyword | isRec     = "letrec"
                   | otherwise = "let"
        defnsStr = foldl (++) "" ["\n" ++ getIndent (indent+1) ++ show v ++ " = " ++ showExpr' (indent+1) expr | (v, expr) <- defns]

showExpr' indent (ELam args expr) =
    "lambda " ++ argsStr ++ " . " ++ showExpr' indent expr
    where
        argsStr = join "," [show v | v <- args]
showExpr' indent (ECaseSimple expr alts) = showExprCase indent "Simple" expr alts
showExpr' indent (ECaseConstr expr alts) = showExprCase indent "Constr" expr alts
showExpr' indent (ECase expr alts) = showCase indent expr alts
showExpr' indent (EError msg) = "Error " ++ msg
showExpr' indent (ESelect r i v) = "Select " ++ show r ++ " " ++ show i ++ " " ++ show v


showExprCase :: Show a => Int -> String -> Expr a -> [Alter Int a] -> String
showExprCase indent t expr alts =
    "Case" ++ t ++ " " ++ showExpr' indent expr ++ " of" ++ altsStr
    where
        altsStr = concat ["\n" ++ getIndent (indent+1) ++ show n ++ " = " ++ showExpr' (indent+1) expr | (n, expr) <- alts]


showCase :: Show a => Int -> Expr a -> [Alter Pattern a] -> String
showCase indent expr alts =
    "Case " ++ showExpr' indent expr ++ " of" ++ altsStr
    where
        altsStr = concat ["\n" ++ getIndent (indent+1) ++ show pat ++ " = " ++ showExpr' (indent+1) expr | (pat, expr) <- alts]


defaultIndent :: String
defaultIndent = "  "


getIndent :: Int -> String
getIndent n = join "" [defaultIndent | i <- [0..n-1]]


showScDefn :: Show a => ScDefn a -> String
showScDefn (ScDefn name args expr) =
    "\n\n********* " ++ name ++ "(" ++ join "," [show arg | arg <- args] ++ ") *********\n" ++ show expr ++ "\n\n"

