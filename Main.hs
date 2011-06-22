module Main where


import GmEvaluator
import System (getArgs)
import System.Console.GetOpt


main = do
    args <- getArgs
    let (flags, nonOpts, msgs) = getOpt RequireOrder [] args
    let [fileName] = nonOpts
    content <- readFile fileName
    putStrLn . runTest $ content

