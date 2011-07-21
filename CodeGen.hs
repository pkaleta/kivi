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
--import Data.String.Lazy (String)
import Text.StringTemplate


type IR = [String]
type Stack = [StackItem]
type StackPointer = Int
data StackItem = SNum Int
               | SStack Int
               | SHeap Int


intTag :: Int
intTag = 1


templatesPath :: String
templatesPath = "templates/"


--genCode :: String -> StringTemplate String
genCode = genIR . lambdaLift . lazyLambdaLift . analyseDeps . transformToLambdaCalculus . mergePatterns . tag . parse


genIR :: CoreProgram -> IO (StringTemplate String)
genIR program@(adts, scs) = do
    let state = compile program
    let globals = getGlobals state
    let heap = getHeap state
    templates <- directoryGroup templatesPath :: IO (STGroup String)
    let Just t = getStringTemplate "program" templates
    let scsTemplates = genScsIR heap templates globals
    return $ setAttribute "scs" (renderTemplates scsTemplates) t


genScsIR :: GmHeap -> STGroup String -> Assoc Name Addr -> [StringTemplate String]
genScsIR heap templates globals =
    map (mapScDefn heap template templates) globals
    where
        Just template = getStringTemplate "sc" templates


mapScDefn :: GmHeap -> StringTemplate String -> STGroup String -> (Name, Addr) -> StringTemplate String
mapScDefn heap template templates (name, addr) =
    setAttribute "body" body $ setAttribute "name" name template
    where
        (NGlobal arity code) = hLookup heap addr
        body = renderTemplates $ genScIR templates code


genScIR :: STGroup String -> GmCode -> [StringTemplate String]
genScIR templates code = ir
    where
        (stack, ir) = foldl (collectInstrIR templates) ([], []) code


collectInstrIR :: STGroup String
               -> (Stack, [StringTemplate String])
               -> Instruction
               -> (Stack, [StringTemplate String])
collectInstrIR templates (stack, ir) (Update n) = (stack', ir ++ [template'])
    where
        (SNum n : stack') = stack
        template' = setManyAttrib [("intTag", show intTag), ("value", show n)] template
        Just template = getStringTemplate "update" templates
collectInstrIR templates acc@(stack, ir) (Pop n) = acc
collectInstrIR templates (stack, ir) (Unwind) =  (stack, ir ++ [template])
    where
        Just template = getStringTemplate "unwind" templates
collectInstrIR templates (stack, ir) (Push n) = (stack, ir ++ [template])
    where
        Just template = getStringTemplate "push" templates
collectInstrIR templates (stack, ir) (Pushint n) = (SNum n : stack, ir)
collectInstrIR templates acc@(stack, ir) _ = acc


renderTemplates :: (Stringable a) => [StringTemplate a] -> [a]
renderTemplates templates = [render template | template <- templates]

--        ir = [(name, ["define i32* @" ++ name ++ "() {"] ++ genScIR heap name addr ++ ["}"]) | (name, addr) <- globals]
--
--        stringify acc (name, ir) =
--            acc ++ name ++ ": " ++ foldl makeStr "" ir ++ "\n\n"
--
--        makeStr acc line = acc ++ "\n" ++ line
--
--
--genScIR :: GmHeap -> Name -> Addr -> IR
--genScIR heap name addr = trace ("************** " ++ name ++ ": " ++ show code) ir
--    where
--        (NGlobal arity code) = hLookup heap addr
--        (ir, stack, sp) = foldl collectIR ([], [], 0) code
--
--
--
----collectIR :: (IR, Stack, StackPointer) -> Instruction -> (IR, Stack, StackPointer)
----collectIR (ir, stack, sp) (Push i) = (ir, SStack i : stack, sp)
----collectIR (ir, stack, sp) (Pushint n) = (ir, SNum n : stack, sp)
--collectIR (ir, stack, sp) (Update i) = do
--    let (item : stack') = stack
--    let SNum n = item
--    templates <- directoryGroup templatesPath :: IO (STGroup String)
--    let Just t = getStringTemplate "update" templates
--    setManyAttrib [("intTag", show intTag), ("value", show n)]
----collectIR (ir, stack, sp) (Pop n) = (ir, stack, sp-n)
----collectIR (ir, stack, sp) Unwind = (ir', stack, sp+1)
----    where
----        ir' = ir ++ ["switch i32 %tag, label %NO_MATCH [" ++ switchBranch intTag "NUM_UNWIND" ++ "]",
----                     "NO_MATCH:",
----                     "; there should be error call i32 (i8 *, ...)* @printf(i8* %ps, i32 %num)",
----                     "NUM_UNWIND:",
----                     "call i32* "]
----collectIR (ir, stack, sp) instr = (ir ++ [show instr], stack, sp)
--
--switchBranch :: Int -> String -> String
--switchBranch tag label = "i32 " ++ show tag ++ ", label " ++ label
--
