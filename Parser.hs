module Parser where

import Char
import Lexer

data Expr a
    = EVar Name                             -- variables
    | ENum Int                              -- numbers
    | EConstr Int Int                       -- constructor (tag, arity)
    | EAp (Expr a) (Expr a)                 -- applications
    | ELet IsRec [(a, Expr a)] (Expr a)     -- let(rec) expressions (is recursive, definitions, body)
    | ECase (Expr a) [Alter a]              -- case expression (expression, alternatives)
    | ELam [a] (Expr a)                     -- lambda abstractions
    deriving (Show)

type Name = String
type CoreExpr = Expr Name
type IsRec = Bool
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name
type Program a = [ScDefn a]
type CoreProgram = Program Name
type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name
type Defn a = (a, Expr a)
type CoreDefn = Defn Name

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False

bindersOf :: [(a, b)] -> [a]
bindersOf defns = [name | (name, _) <- defns]

rhsOf :: [(a, b)] -> [b]
rhsOf defns = [rhs | (_, rhs) <- defns]


-- line number and token

keywords = ["let", "letrec", "case", "in", "of", "Pack"]

--parser implementation
--parse :: String -> CoreProgram
--parse = syntax . clex

type Parser a = [Token] -> [(a, [Token])]

-- parser functions

pSat :: (String -> Bool) -> Parser String
pSat pred (t : ts) | not (t `elem` keywords) && pred t = [(t, ts)]
pSat _ _ = []

pLit :: String -> Parser String
pLit s = pSat (== s)
--pLit s (t : ts) | s == t = [(s, ts)]
--pLit _ _ = []

pVar :: Parser String
pVar = pSat check
    where
        check (c : cs) = isAlpha c
--pVar (token : ts) | isAlpha c =
--    [(token, ts)] where c : cs = token
--pVar _ = []

pNum :: Parser Int
pNum = (pSat isNumber) `pApply` strToInt
    where
        isNumber (d : []) = isDigit d
        isNumber (d : ds) | isDigit d = isNumber ds
                          | otherwise = False
        isNumber _ = False
        strToInt x = read x :: Int

pOr :: Parser a -> Parser a -> Parser a
pOr p1 p2 tokens = (p1 tokens) ++ (p2 tokens)

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen combine p1 p2 tokens =
    [(combine v1 v2, tokens2) | (v1, tokens1) <- p1 tokens,
                                (v2, tokens2) <- p2 tokens1]

pThen3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 combine p1 p2 p3 tokens =
    [(combine v1 v2 v3, tokens3) | (v1, tokens1) <- p1 tokens,
                                   (v2, tokens2) <- p2 tokens1,
                                   (v3, tokens3) <- p3 tokens2]

pThen4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
pThen4 combine p1 p2 p3 p4 tokens =
    [(combine v1 v2 v3 v4, tokens4) | (v1, tokens1) <- p1 tokens,
                                      (v2, tokens2) <- p2 tokens1,
                                      (v3, tokens3) <- p3 tokens2,
                                      (v4, tokens4) <- p4 tokens3]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore parser = (pOneOrMore parser) `pOr` (pEmpty [])

pEmpty :: a -> Parser a
pEmpty ret tokens = [(ret, tokens)]

pOneOrMore :: Parser a -> Parser [a]
pOneOrMore parser = pThen (:) parser (pZeroOrMore parser)

--test
pHelloOrGoodbye :: Parser String
pHelloOrGoodbye = (pLit "hello") `pOr` (pLit "goodbye")

--test
pGreeting :: Parser (String, String)
pGreeting =
    pThen3 mkGreeting pHelloOrGoodbye pVar (pLit "!")
    where
        mkGreeting a b _ = (a, b)

--test
pGreetings :: Parser [(String, String)]
pGreetings = pZeroOrMore pGreeting

pGreetingsN :: Parser Int
pGreetingsN = (pZeroOrMore pGreeting) `pApply` length

pApply :: Parser a -> (a -> b) -> Parser b
pApply parser f tokens =
    [(f v, ts) | (v, ts) <- (parser tokens)]

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep parser sepParser =
    pThen (:) parser restParser
    where
        restParser =
            (pThen (\_ b -> b) sepParser (pOneOrMoreWithSep parser sepParser))
            `pOr`
            (pEmpty [])

-- test
pSepGreets :: Parser [(String, String)]
pSepGreets = pOneOrMoreWithSep pGreeting (pLit ";")
    where
        combine x xs = x:xs

--syntax analyser implementation
syntax :: [Token] -> CoreProgram
syntax = takeFirstParse . pProgram
    where
        takeFirstParse ((prog, []) : rest) = prog
        takeFirstParse (parse : rest) = takeFirstParse rest
        takeFirstParse _ = error "Syntax error: no successful parse found."


pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSep pSc (pLit ";")

pSc :: Parser CoreScDefn
pSc = pThen4 mkSc pVar (pZeroOrMore pVar) (pLit "=") pExpr
    where
        mkSc var vars equals expr = (var, vars, expr)

pExpr :: Parser CoreExpr
pExpr =
    pThen4 (mkLetExpr False) (pLit "let") pDefns (pLit "in") pExpr `pOr`
    pThen4 (mkLetExpr True) (pLit "letrec") pDefns (pLit "in") pExpr `pOr`
    pThen4 mkCaseExpr (pLit "case") pExpr (pLit "of") pAlts `pOr`
    pThen4 mkLambdaExpr (pLit "\\") (pZeroOrMore pVar) (pLit ".") pExpr `pOr`
    pAtomicExpr
    where
        mkLetExpr rec _ defns _ body = ELet rec defns body
        mkCaseExpr _ expr _ alts = ECase expr alts
        mkLambdaExpr _ vars _ expr = ELam vars expr

pAtomicExpr :: Parser CoreExpr
pAtomicExpr =
    (pVar `pApply` EVar) `pOr`
    (pNum `pApply` ENum) `pOr`
    pThen3 mkConstr (pLit "Pack{") (pThen3 mkTwoNumbers pNum (pLit ",")  pNum) (pLit "}")
    where
        mkConstr _ constr _ = constr
        mkTwoNumbers a _ b = EConstr a b

pDefns :: Parser [CoreDefn]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")

pDefn :: Parser CoreDefn
pDefn = pThen3 mkDefn pVar (pLit "=") pExpr
    where
        mkDefn var _ expr = (var, expr)

pAlts :: Parser [CoreAlt]
pAlts = pOneOrMoreWithSep pAlt (pLit ";")

pAlt :: Parser CoreAlt
pAlt = pThen4 mkAlt (pThen3 mkNum (pLit "<") pNum (pLit ">")) (pOneOrMore pVar) (pLit "->") pExpr
    where
        mkAlt num vars _ expr = (num, vars, expr)
        mkNum _ num _ = num

--pBinOp :: Parser CoreBinOp
--pBinOp = pArithOp `pOr` pRelOp `pOr` pBoolOp
--
--pArithOp :: Parser CoreArithOp
--pArithOp = (pLit "+") `pOr` (pLit "-") `pOr` (pLit "*") `pOr` (pLit "/")
--
--pRelOp :: Parser CoreRelOp
--pRelOp = (pLit "<") `pOr` (pLit "<=") `pOr` (pLit "==") `pOr` (pLit "~=") `pOr` (pLit ">=") `pOr` (pLit ">")
--
--pBoolOp :: Parser CoreBoolOp
--pBoolOp = (pLit "&") `pOr` (pLit "|")
