module Parser where


import Char
import Lexer
import Common
import List
import Debug.Trace
import AbstractDataTypes


data PartialExpr = NoOp | FoundOp Name (Expr Pattern)
type Parser a = [Token] -> [(a, [Token])]
type Equation = ([Pattern], Expr Pattern)

data PatProgramElement = PatScDefn Name [Equation]
                       | PatDataType Name [Constructor]
    deriving (Show)

type PatProgram = [PatProgramElement]
type PatTypeScPair = ([PatProgramElement], [PatProgramElement])


isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False


-- line number and token

keywords = ["data", "let", "letrec", "case", "in", "of", "Pack"]

--parser implementation
parse :: String -> PatTypeScPair
parse = split . syntax . clex


-- splits datatypes and supercombinators
split :: PatProgram -> PatTypeScPair
split = partition isDataType
    where
        isDataType (PatDataType name constructors) = True
        isDataType _ = False


-- parser functions


pSat :: (String -> Bool) -> Parser String
pSat pred (t : ts) | pred t = [(t, ts)]
pSat _ _ = []


pLit :: String -> Parser String
pLit s = pSat (== s)
--pLit s (t : ts) | s == t = [(s, ts)]
--pLit _ _ = []


pVar :: Parser String
pVar = pName isLower


pConstrName :: Parser String
pConstrName = pName isUpper


pDataTypeName :: Parser String
pDataTypeName = pName isUpper


pName :: (Char -> Bool) -> Parser String
pName cond = pSat check
    where
        check token = not (token `elem` keywords) && (isAlpha first) && (cond first)
            where first = head token


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


pApply :: Parser a -> (a -> b) -> Parser b
pApply parser f tokens =
    [(f v, ts) | (v, ts) <- (parser tokens)]


pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep parser sepParser =
    pThen (:) parser restParser
    where
        restParser =
            (pThen (\_ b -> b) sepParser (pOneOrMoreWithSep parser sepParser)) `pOr`
            (pEmpty [])


--syntax analyser implementation
syntax :: [Token] -> PatProgram
syntax = takeFirstParse . pProgram
    where
        takeFirstParse ((prog, []) : rest) = prog
        takeFirstParse (parse : rest) = takeFirstParse rest
        takeFirstParse _ = error "Syntax error: no successful parse found."


pPattern :: Parser [Pattern]
pPattern = pZeroOrMore pPatternExpr


pPatternExpr :: Parser Pattern
pPatternExpr =
    (pVar `pApply` PVar) `pOr`
    (pNum `pApply` PNum) `pOr`
    pThen mkConstr pConstrName (pZeroOrMore pPatternExpr) `pOr`
    pThen3 mkParenExpr (pLit "(") pPatternExpr (pLit ")")
    where
        mkConstr name patExprs = PConstr name patExprs
        mkParenExpr _ expr _ = expr


pConstrDecl :: Parser Constructor
pConstrDecl = pThen mkConstr pConstrName pNum
    where
        mkConstr name arity = (name, undefinedTag, arity)


pProgram :: Parser PatProgram
pProgram = pOneOrMoreWithSep (pSc `pOr` pDataType) (pLit ";")


pDataType :: Parser PatProgramElement
pDataType = pThen4 mkDataType (pLit "data") pDataTypeName (pLit "=") $ pOneOrMoreWithSep pConstrDecl $ pLit "|"
    where
        mkDataType _ name _ cs = PatDataType name cs


pSc :: Parser PatProgramElement
pSc = pThen4 mkSc pVar pPattern (pLit "=") pExpr
    where
        mkSc name pattern equals expr = PatScDefn name [(pattern, expr)]


pExpr :: Parser (Expr Pattern)
pExpr =
    pThen4 (mkLetExpr False) (pLit "let") pDefns (pLit "in") pExpr `pOr`
    pThen4 (mkLetExpr True) (pLit "letrec") pDefns (pLit "in") pExpr `pOr`
    pThen4 mkCaseExpr (pLit "case") pExpr (pLit "of") pAlts `pOr`
    pThen4 mkLambdaExpr (pLit "\\") pPattern (pLit ".") pExpr `pOr`
    pOrExpr `pOr`
    pAtomicExpr
    where
        mkLetExpr rec _ defns _ body = ELet rec defns body
        mkCaseExpr _ expr _ alts = ECase expr alts
        mkLambdaExpr _ pattern _ expr = ELam pattern expr


pAtomicExpr :: Parser (Expr Pattern)
pAtomicExpr =
    (pVar `pApply` EVar) `pOr`
    (pNum `pApply` ENum) `pOr`
    (pConstrName `pApply` EConstr) `pOr`
    pThen3 mkParenExpr (pLit "(") pExpr (pLit ")")
    where
        mkParenExpr _ expr _ = expr


pDefns :: Parser [Defn Pattern]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")


pDefn :: Parser (Defn Pattern)
pDefn = pThen3 mkDefn pPatternExpr (pLit "=") pExpr
    where
        mkDefn patExpr _ expr = (patExpr, expr)


pAlts :: Parser [Alter Pattern]
pAlts = pOneOrMoreWithSep pAlt (pLit ";")


pAlt :: Parser (Alter Pattern)
pAlt = pThen3 mkAlt pPatternExpr (pLit "->") pExpr
    where
        mkAlt pattern _ expr = (pattern, expr)


assembleOp :: Expr Pattern -> PartialExpr -> Expr Pattern
assembleOp expr1 NoOp = expr1
assembleOp expr1 (FoundOp name expr2) = EAp (EAp (EVar name) expr1) expr2


-- or expression
pOrExpr :: Parser (Expr Pattern)
pOrExpr = pThen assembleOp pAndExpr pOrExprC


pOrExprC :: Parser PartialExpr
pOrExprC = (pThen FoundOp (pLit "|") pOrExpr) `pOr` (pEmpty NoOp)


-- and expression
pAndExpr :: Parser (Expr Pattern)
pAndExpr = pThen assembleOp pRelOpExpr pAndExprC


pAndExprC :: Parser PartialExpr
pAndExprC = (pThen FoundOp (pLit "&") pAndExpr) `pOr` (pEmpty NoOp)


-- rel op expression
pRelOpExpr :: Parser (Expr Pattern)
pRelOpExpr = pThen assembleOp pAddExpr pRelOpExprC


pRelOpExprC :: Parser PartialExpr
pRelOpExprC = (pThen FoundOp pRelOp pAndExpr) `pOr` (pEmpty NoOp)


pRelOp :: Parser String
pRelOp = (pLit "<") `pOr` (pLit "<=") `pOr` (pLit "==") `pOr` (pLit "!=") `pOr` (pLit ">=") `pOr` (pLit ">")


-- additive expression
pAddExpr :: Parser (Expr Pattern)
pAddExpr = pThen assembleOp pMultExpr pAddExprC


pAddExprC :: Parser PartialExpr
pAddExprC = (pThen FoundOp (pLit "+") pAddExpr) `pOr`
    (pThen FoundOp (pLit "-") pMultExpr) `pOr`
    (pEmpty NoOp)


-- multiplicative expression
pMultExpr :: Parser (Expr Pattern)
pMultExpr = pThen assembleOp pApExpr pMultExprC

pMultExprC :: Parser PartialExpr
pMultExprC = (pThen FoundOp (pLit "*") pMultExpr) `pOr`
    (pThen FoundOp (pLit "/") pApExpr) `pOr`
    (pEmpty NoOp)


-- applicative expression
pApExpr :: Parser (Expr Pattern)
pApExpr = ((pOneOrMore pAtomicExpr) `pApply` mkApChain)
    where
        mkApChain (expr : exprs) = foldl EAp expr exprs

