module ParserTypes where


import Common
import Lexer


data PartialExpr = NoOp | FoundOp Name (Expr Pattern)
type Parser a = [Token] -> [(a, [Token])]
type Equation = ([Pattern], Expr Pattern)

data PatProgramElement = PatScDefn Name [Equation]
                       | PatDataType Name [Constructor]
    deriving (Show)

type PatProgram = [PatProgramElement]
type PatTypeScPair = ([PatProgramElement], [PatProgramElement])

