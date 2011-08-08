module Main where


import GmEvaluator
import CodeGen
import System (getArgs)
import System.Console.GetOpt


data Flag = Eval
    deriving (Eq, Show)


main = do
    args <- getArgs
    let (flags, nonOpts, msgs) = getOpt RequireOrder options args
    let [fileName] = nonOpts
    content <- readFile fileName
    putStrLn . show $ flags
    putStrLn . show $ nonOpts
    case length msgs > 0 of
        True ->
            putStrLn . concat $ msgs
        False ->
            case Eval `elem` flags of
                True ->
                    putStrLn . run $ content
                False ->
                    saveLLVMIR . genLLVMIR $ content


options :: [OptDescr Flag]
options = [ Option ['e'] ["eval"] (NoArg Eval) "performs interpretation rather than compile to LLVM bytecode." ]

