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
import Data.Map as Map
--import Data.String.Lazy (String)
import Text.StringTemplate


type Reg = Int
type LLVMIR = StringTemplate String
type LLVMStack = [LLVMValue]
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

nextReg :: Reg -> Reg
nextReg reg = reg + 1


templatesPath :: String
templatesPath = "templates/"


codegenPath :: String
codegenPath = "codegen/"


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
    setAttribute "scs" (renderTemplates scsTemplates) t
    where
        state = compile program
        globals = getGlobals state
        heap = getHeap state
        Just t = getStringTemplate "program" templates
        scsTemplates = genScsLLVMIR heap templates globals


genScsLLVMIR :: GmHeap -> STGroup String -> Assoc Name Addr -> [LLVMIR]
genScsLLVMIR heap templates globals =
    Prelude.map (mapScDefn heap template templates) globals
    where
        Just template = getStringTemplate "sc" templates


mapScDefn :: GmHeap -> LLVMIR -> STGroup String -> (Name, Addr) -> LLVMIR
mapScDefn heap template templates (name, addr) =
    setAttribute "body" body $ setAttribute "name" (mkFunName name) template
    where
        (NGlobal arity code) = hLookup heap addr
        body = trace ("\n\n" ++ show code ++ "\n\n") renderTemplates $ genScLLVMIR templates arity code


genScLLVMIR :: STGroup String -> Int -> GmCode -> [LLVMIR]
genScLLVMIR templates arity code = ir
    where
        (reg, stack, ir) = foldl (\state@(reg, stack, ir) instr -> trace ("instr: " ++ show instr ++ "\nstack: " ++ show stack ++ "\n\n") (collectInstrLLVMIR templates arity state instr)) (initialReg, [], []) code


collectInstrLLVMIR :: STGroup String
                   -> Int
                   -> (Reg, LLVMStack, [LLVMIR])
                   -> Instruction
                   -> (Reg, LLVMStack, [LLVMIR])
collectInstrLLVMIR templates arity (reg, stack, ir) (Update n) = (reg, stack, ir ++ [template'])
    where
        Just template = getStringTemplate "update" templates
        template' = setManyAttrib [("n", show n)] template
collectInstrLLVMIR templates arity (reg, stack, ir) (Push n) = (reg, stack, ir ++ [template'])
    where
        Just template = getStringTemplate "push" templates
        template' = setManyAttrib [("n", show n)] template
collectInstrLLVMIR templates arity (reg, stack, ir) (Pop n) = (reg, stack, ir ++ [template'])
    where
        Just template = getStringTemplate "pop" templates
        template' = setManyAttrib [("n", show n)] template
-- TODO: change this not to allocate numbers on heap
collectInstrLLVMIR templates arity (reg, stack, ir) (Pushint n) = (nextReg reg, stack, ir ++ [template'])
    where
        Just template = getStringTemplate "pushint" templates
        template' = setManyAttrib [("n", show n)] template
collectInstrLLVMIR templates arity (reg, stack, ir) (Pushglobal v) = (reg, stack, ir ++ [template'])
    where
        Just template = getStringTemplate "pushglobal" templates
        template' = setManyAttrib [("arity", show arity), ("name", mkFunName v)] template
collectInstrLLVMIR templates arity (reg, stack, ir) (Mkap) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "mkap" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Unwind) =  (reg, stack, ir)
    where
        Just template = getStringTemplate "unwind" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Eval) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "eval" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Pushbasic n) = (reg, stack, ir ++ [template'])
    where
        Just template = getStringTemplate "pushbasic" templates
        template' = setManyAttrib [("n", show n)] template
collectInstrLLVMIR templates arity (reg, stack, ir) (Get) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "get" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Add) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "add" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Sub) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "sub" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Mul) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "mul" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (Div) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "div" templates
collectInstrLLVMIR templates arity (reg, stack, ir) (MkInt) = (reg, stack, ir ++ [template])
    where
        Just template = getStringTemplate "mkint" templates
collectInstrLLVMIR templates arity state _ = state


mkFunName :: String -> String
mkFunName name =
    case Map.lookup name nameMapping of
        Just name' -> funPrefix ++ name'
        Nothing    -> funPrefix ++ name

--updateNumLLVMIR :: STGroup String -> Name -> [LLVMIR]
--updateNumLLVMIR templates name =
--    setManyAttrib [("intTag", show intTag), ("value", show n)] template
--    where Just template = getStringTemplate "update_int" templates
--
--updateGlobalLLVMIR :: STGroup String -> Name -> [LLVMIR]
--updateGlobalLLVMIR templates name =
--    setManyAttrib [("intTag", show globalTag), ("globalPtr", show n)] template
--    where Just template = getStringTemplate "update_global" templates


renderTemplates :: [LLVMIR] -> [String]
renderTemplates templates = [render template | template <- templates]

