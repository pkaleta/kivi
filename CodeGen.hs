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
import Data.Char
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


nameMapping :: Map String String
nameMapping = Map.fromList [("+", "add"),
                            ("-", "sub"),
                            ("*", "mul"),
                            ("/", "div"),
                            ("%", "mod"),
                            ("negate", "negate"),
                            ("==", "eq"),
                            ("!=", "ne"),
                            ("<", "lt"),
                            ("<=", "le"),
                            (">", "gt"),
                            (">=", "ge")]

relationalMapping :: Map String String
relationalMapping = Map.fromList [("eq", "eq"),
                                  ("ne", "ne"),
                                  ("lt", "ult"),
                                  ("le", "ule"),
                                  ("gt", "ugt"),
                                  ("ge", "uge"),
                                  ("add", "add"),
                                  ("sub", "sub"),
                                  ("mul", "mul"),
                                  ("div", "udiv"),
                                  ("mod", "urem")]


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
createNameArityCodeMapping heap globals = Map.union globalMapping builtinMapping
    where
        globalMapping = Map.fromList [createEntry heap name addr | (name, addr) <- globals]
        builtinMapping = Map.fromList [("connect", (0, [])),
                                       ("send", (1, []))]


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
    setManyAttrib [("scs", renderTemplates scsTemplates), ("constrFuns", renderTemplates constrs')] template
    where
        state = compile program
        globals = getGlobals state
        heap = getHeap state
        Just template = getStringTemplate "program" templates
        mapping = createNameArityCodeMapping heap globals
        scsTemplates = genScsLLVMIR mapping templates globals
        constrs = concat $ map snd adts
        constrs' = foldl (createConstr templates) [] constrs


createConstr :: STGroup String -> [StringTemplate String] -> Constructor -> [StringTemplate String]
createConstr templates constrs (name, tag, arity) = constrTmpl' : constrs
    where
        Just packTmpl = getStringTemplate "pack" templates
        packTmpl' = setManyAttrib [("tag", show tag), ("arity", show arity), ("ninstr", "0")] packTmpl

        Just updateTmpl = getStringTemplate "update" templates
        updateTmpl' = setManyAttrib [("n", "0"), ("ninstr", "1")] updateTmpl

        Just constrTmpl = getStringTemplate "constr" templates
        constrTmpl' = setManyAttrib [("tag", show tag), ("arity", show arity), ("update", render updateTmpl'), ("pack", render packTmpl')] constrTmpl


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
        template' = setManyAttrib [("arity", show arity), ("name", mkFunName v), ("ninstr", show ninstr)] template
        Just (arity, code) = Map.lookup v mapping
        Just template = getStringTemplate "pushglobal" templates
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
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (MkInt) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "mkint" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (MkBool) = (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "mkbool" templates
        template' = setManyAttrib [("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (CasejumpSimple alts) =
    (reg, stack, ir ++ [caseTmpl], ninstr')
    where
        (caseTmpl, ninstr') = translateCase mapping templates alts tagChooser ninstr "casejumpsimple"
        tagChooser = filter (>= 0) . (map fst)
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (CasejumpConstr alts) =
    (reg, stack, ir ++ [caseTmpl], ninstr')
    where
        (caseTmpl, ninstr') = translateCase mapping templates alts tagChooser ninstr "casejumpconstr"
        tagChooser = map fst
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Pushconstr tag arity) =
    (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "pushconstr" templates
        template' = setManyAttrib [("tag", show tag), ("arity", show arity), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Alloc n) =
    (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "alloc" templates
        template' = setManyAttrib [("n", show n), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates (reg, stack, ir, ninstr) (Select n k) =
    (reg, stack, ir ++ [template'], ninstr + 1)
    where
        Just template = getStringTemplate "select" templates
        template' = setManyAttrib [("n", show n), ("k", show k), ("ninstr", show ninstr)] template
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Add) =
    translateBinOp (mkArithTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Sub) =
    translateBinOp (mkArithTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Mul) =
    translateBinOp (mkArithTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Div) =
    translateBinOp (mkArithTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Mod) =
    translateBinOp (mkArithTmpl templates instr) state

translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Eq) =
    translateBinOp (mkRelationalTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Ne) =
    translateBinOp (mkRelationalTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Lt) =
    translateBinOp (mkRelationalTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Le) =
    translateBinOp (mkRelationalTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Gt) =
    translateBinOp (mkRelationalTmpl templates instr) state
translateToLLVMIR mapping templates state@(reg, stack, ir, ninstr) instr@(Ge) =
    translateBinOp (mkRelationalTmpl templates instr) state
translateToLLVMIR mapping templates state (Error msg) = state


translateBinOp :: (NInstr -> LLVMIR) -> (Reg, LLVMStack, [LLVMIR], NInstr) -> (Reg, LLVMStack, [LLVMIR], NInstr)
translateBinOp mkTmpl (reg, stack, ir, ninstr) =
    (reg, stack, ir ++ [mkTmpl ninstr], ninstr + 1)


mkRelationalTmpl :: STGroup String -> Instruction -> NInstr -> LLVMIR
mkRelationalTmpl templates instr ninstr = template'
    where
        template' = setManyAttrib [("trueTag", show trueTag),
            ("falseTag", show falseTag),
            ("ninstr", show ninstr),
            ("instr", llvmName)] template
        Just llvmName = Map.lookup (map toLower . show $ instr) relationalMapping
        Just template = getStringTemplate "relational" templates


mkArithTmpl :: STGroup String -> Instruction -> NInstr -> LLVMIR
mkArithTmpl templates instr ninstr = template'
    where
        template' = setManyAttrib [ ("ninstr", show ninstr), ("instr", llvmName)] template
        Just llvmName = Map.lookup (map toLower . show $ instr) relationalMapping
        Just template = getStringTemplate "arith" templates


translateCase :: NameArityCodeMapping
              -> STGroup String
              -> [(Int, GmCode)]
              -> ([(Int, [LLVMIR])] -> [Int])
              -> NInstr
              -> String
              -> (LLVMIR, NInstr)
translateCase mapping templates alts tagChooser ninstr tmplName = (caseTmpl', ninstr' + 1)
    where
        (ninstr', alts') = mapAccumL (translateAlt mapping templates) ninstr alts
        Just caseTmpl = getStringTemplate tmplName templates
        caseTmpl' = setManyAttrib [("alts", renderTemplates altsIR), ("branches", renderTemplates branches)]
            $ setAttribute "tags" (tags::[Int])
            $ setAttribute "ninstr" (show ninstr') caseTmpl
        branches = foldl (translateBranch ninstr' branchTmpl) [] tags
        Just branchTmpl = getStringTemplate "branch" templates
        altsIR = foldl (translateAlts ninstr' altTmpl) [] alts'
        Just altTmpl = getStringTemplate "alt" templates
        tags = tagChooser alts'


translateBranch :: NInstr -> StringTemplate String -> [LLVMIR] -> Int -> [LLVMIR]
translateBranch ninstr branchTmpl irAcc tag = irAcc ++ [branchTmpl']
    where branchTmpl' = setManyAttrib [("ninstr", show ninstr), ("tag", show tag)] branchTmpl

translateAlts :: NInstr -> StringTemplate String -> [LLVMIR] -> (Int, [LLVMIR]) -> [LLVMIR]
translateAlts ninstr altTmpl irAcc (tag, ir) = irAcc ++ [altTmpl']
    where
        altTmpl' = setManyAttrib [("ninstr", show ninstr), ("tag", show tag)]
            $ setAttribute "code" (renderTemplates ir) altTmpl


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

