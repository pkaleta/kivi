module ParserTypes where


import Common
import Lexer


data PartialExpr = NoOp | FoundOp Name (Expr Pattern)
type Parser a = [Token] -> [(a, [Token])]
type Equation = ([Pattern], Expr Pattern)


data PatScDefn = PatScDefn Name [Equation]


type PatProgram = ([DataType], [PatScDefn])

