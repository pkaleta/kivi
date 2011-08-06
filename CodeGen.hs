module CodeGen where


import Parser
import Utils
import Common
import Debug.Trace
import GmCompiler
import PatternMatching
import AbstractDataTypes
import LambdaLifter
import LazyLambdaLifter
import DependencyAnalyser
import LambdaCalculusTransformer
import TypeChecker
import Data.Map as Map hiding (map, filter)
import Data.List
--import Data.String.Lazy (String)
import Text.StringTemplate


type Reg = Int
type LLVMIR = StringTemplate String
type LLVMStack = [LLVMValue]
type NameArityCodeMapping = Map Name (Arity, GmCode)
type NInstr = Int
data LLVMValue = LLVMNum Int
               | LLVMReg Reg
               | LLVMStackAddr Int
    deriving Show


nameMapping = Map.fromList [("+", "add"),
                            ("-", "sub"),
                            ("*", "mul"),
                            ("/", "div"),
                            ("negate", "negate"),
                            ("==", "eq"),
                            ("!=", "ne"),
                            ("<", "l"),
                            ("<=", "le"),
                            (">", "g"),
                            (">=", "ge")]


funPrefix :: String
funPrefix = "_"

numTag :: Int
numTag = 1

globalTag :: Int
globalTag = 2

apTag :: Int
apTag = 3


initialReg :: Reg
initialReg = 1


initialInstructionNum :: Int
initialInstructionNum = 1


nextReg :: Reg -> Reg
nextReg reg = reg + 1


templatesPath :: String
templatesPath = "templates/"


codegenPath :: String
codegenPath = "codegen/"


createNameArityCodeMapping :: GmHeap -> GmGlobals -> NameArityCodeMapping
createNameArityCodeMapping heap globals = Map.fromList [createEntry heap name addr | (name, addr) <- globals]

createEntry :: GmHeap -> Name -> Addr -> (Name, (Arity, GmCode))
createEntry heap name addr = (name, (arity, code))
    where (NGlobal arity code) = hLookup heap addr



saveLLVMIR :: IO (LLVMIR) -> IO ()
saveLLVMIR ir = do
    content <- ir
    let filePath = "codegen/test.ll"
--    putStrLn . render $ content
    writeFile filePath $ render content


genLLVMIR :: String -> IO (LLVMIR)
genLLVMIR program = do
    templates <- directoryGroup templatesPath :: IO (STGroup String)
    return $ (genProgramLLVMIR templates) . lambdaLift . lazyLambdaLift . analyseDeps . transformToLambdaCalculus . mergePatterns . tag . parse $ program


genProgramLLVMIR :: STGroup String -> CoreProgram -> LLVMIR
genProgramLLVMIR templates program@(adts, scs) =
    setAttribute "scs" (renderTemplates scsTemplates) template
    where
        state = compile program
        globals = getGlobals state
        heap = getHeap state
        Just template = getStringTemplate "program" templates
        mapping = createNameArityCodeMapping heap globals
        scsTemplates = genScsLLVMIR mapping templates globals


genScsLLVMIR :: NameArityCodeMapping -> STGroup String -> Assoc Name Addr -> [LLVMIR]
genScsLLVMIR mapping templates globals =
    map (mapScDefn mapping template templates) globals
    where
        Just template = getStringTemplate "sc" templates


mapScDefn :: NameArityCodeMapping -> LLVMIR -> STGroup String -> (Name, Addr) -> LLVMIR
mapScDefn mapping template templates (name, addr) =
    setAttribute "body" body $ setAttribute "name" (mkFunName name) template
    where
        Just (arity, code) = Map.lookup name mapping
        body = trace ("\n\n" ++ show code ++ "\n\n") renderTemplates $ genScLLVMIR mapping templates code


genScLLVMIR :: NameArityCodeMapping -> STGroup String -> GmCode -> [LLVMIR]
genScLLVMIR mapping templates code = ir
    where
        (reg, stack, ir, ninstr) = foldl (\state@(reg, stack, ir, ninstr) instr -> trace ("instr: " ++ show instr ++ "\nstack: " ++ show stack ++ "\n\n") (translateToLLVMIR mapping templates state instr)) (initialReg, [], [], initialInstructionNum) code


translateToLLVMIR :: NameArityCodeMapping
                  -> STGroup String
                  -> (Reg, LLVMStack, [LLVMIR], NInstr)
                  -> Instruction
                  -> (Reg, LLVMStack, [LLVMIR], NInstr)
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Update n) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "update" templates
        template' = setManyAttrib [("n", show n), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Push n) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "push" templates
        template' = setManyAttrib [("n", show n), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Pop n) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "pop" templates
        template' = setManyAttrib [("n", show n), ("ninstr", show ninstr)] template
-- TODO: change this not to allocate numbers on mapping
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Pushint n) = (nextReg reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "pushint" templates
        template' = setManyAttrib [("n", show n), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Pushglobal v) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "pushglobal" templates
        template' = setManyAttrib [("arity", show arity), ("name", mkFunName v), ("ninstr", show ninstr)] template
        Just (arity, code) = trace ("********** " ++ show v)Map.lookup v mapping
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Mkap) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "mkap" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Unwind) =  (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "unwind" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Eval) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "eval" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Pushbasic n) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "pushbasic" templates
        template' = setManyAttrib [("n", show n), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Get) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "get" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Add) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "add" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Sub) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "sub" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Mul) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "mul" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Div) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "div" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (MkInt) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "mkint" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (CasejumpSimple alts) = (reg, stack, ir ++ [caseTmpl'], ninstr')
    where
        (ninstr', alts') = mapAccumL (translateAlt mapping templates) ninstr alts
        tags = filter (>= 0) $ map fst alts'
        Just caseTmpl = getStringTemplate "casejumpsimple" templates
        caseTmpl' = setAttribute "alts" (renderTemplates altsIR) $ setAttribute "tags" (tags::[Int]) $ setAttribute "ninstr" (show ninstr) caseTmpl
        Just altTmpl = getStringTemplate "alt" templates
        altsIR = foldl (translateAlts altTmpl) [] alts'
translateToLLVMIR mapping templates state (Error msg) = state


translateAlts :: StringTemplate String -> [LLVMIR] -> (Int, [LLVMIR]) -> [LLVMIR]
translateAlts altTmpl irAcc (tag, ir) = irAcc ++ [altTmpl']
    where
        altTmpl' = setAttribute "tag" (show tag) $ setAttribute "code" (renderTemplates ir) $ altTmpl


translateAlt :: NameArityCodeMapping
             -> STGroup String
             -> NInstr
             -> (Int, GmCode)
             -> (NInstr, (Int, [LLVMIR]))
translateAlt mapping templates ninstr (tag, code) = (ninstr', (tag, ir))
    where
        initialState = (initialReg, [], [], ninstr)
        (reg, stack, ir, ninstr') = foldl (translateToLLVMIR mapping templates) initialState code


mkFunName :: String -> String
mkFunName name =
    case Map.lookup name nameMapping of
        Just name' -> funPrefix ++ name'
        Nothing    -> funPrefix ++ name


renderTemplates :: [LLVMIR] -> [String]
renderTemplates templates = [render template | template <- templates]

