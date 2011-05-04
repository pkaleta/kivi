module Defs where

import Parser

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats, TiOutput)
type TiStack = [Addr]
type TiHeap = Heap Node
type TiGlobals = Assoc Name Addr
type TiStats = Int
type TiOutput = [Int]

type TiDump = [TiStack]

data Node
    = NAp Addr Addr
    | NSc Name [Name] CoreExpr
    | NNum Int
    | NInd Addr
    | NPrim Name Primitive
    | NData Int [Addr]
    | NMarked Node
    deriving Show

type Addr = Int
type Assoc a b = [(a, b)]
type Heap a = (Int, [Addr], Assoc Addr a)

data Primitive = Neg
               | Add
               | Sub
               | Mul
               | Div
               | PrimConstr Int Int
               | If
               | Greater
               | GreaterEq
               | Less
               | LessEq
               | Eq
               | NotEq
               | PrimCasePair
               | PrimCaseList
               | PrimCons
               | Print
               | Stop
    deriving Show

