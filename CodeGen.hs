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


saveIR :: IO (StringTemplate String) -> IO ()
saveIR ir = do
    content <- ir
    let filePath = "codegen/test.ll"
    writeFile filePath $ render content


genIR :: String -> IO (StringTemplate String)
genIR program = do
    templates <- directoryGroup templatesPath :: IO (STGroup String)
    return $ (genProgramIR templates) . lambdaLift . lazyLambdaLift . analyseDeps . transformToLambdaCalculus . mergePatterns . tag . parse $ program


genProgramIR :: STGroup String -> CoreProgram -> StringTemplate String
genProgramIR templates program@(adts, scs) =
    setAttribute "scs" (renderTemplates scsTemplates) t
    where
        state = compile program
        globals = getGlobals state
        heap = getHeap state
        Just t = getStringTemplate "program" templates
        scsTemplates = genScsIR heap templates globals


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

