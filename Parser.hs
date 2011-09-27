module Parser where


import Char
import Lexer
import Common
import List
import Debug.Trace
import AbstractDataTypes
import ParserTypes
import Prelude hiding (lex)
import Data.Char


isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False


-- line number and token

keywords = ["where", "data", "let", "letrec", "case", "in", "of", "Pack"]

--parser implementation
parse :: String -> PatProgram
parse = syntax . lex


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

pChar :: Parser Int
pChar = pThen3 mkChar (pLit "'") (pSat isSingleChar) (pLit "'")
    where mkChar _ [c] _ = ord c


isSingleChar :: String -> Bool
isSingleChar s = length s == 1


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


pZeroOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pZeroOrMoreWithSep parser sepParser = (pOneOrMoreWithSep parser sepParser) `pOr` (pEmpty [])


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


pStringContent :: Parser String
pStringContent (t : ts) = [(t, ts)]


pString :: Parser (Expr Pattern)
pString =
  pThen3 mkString (pLit "\"") pStringContent (pLit "\"")
  where
    mkString _ content _ = foldr cons (EConstrName "Nil") content
    cons c acc = EAp (EAp (EConstrName "Cons") (EChar $ ord c)) acc


pList :: Parser (Expr Pattern)
pList =
    pThen3 mkList (pLit "[") (pZeroOrMoreWithSep pExpr (pLit ",")) (pLit "]") `pOr`
    pString `pOr`
    pThen3 selSecond (pLit "(") pConsList (pLit ")")
    where
        selSecond _ list _ = list
        mkList _ exprs _ = foldr cons (EConstrName "Nil") exprs


pConsList :: Parser (Expr Pattern)
pConsList = pThen3 mkList pExpr (pLit ":") pExpr
    where mkList head _ tail = cons head tail


cons :: Expr Pattern -> Expr Pattern -> Expr Pattern
cons expr list = EAp (EAp (EConstrName "Cons") expr) list


pTuple :: Parser (Expr Pattern)
pTuple = pThen3 mkTuple (pLit "(") (pOneOrMoreWithSep pExpr (pLit ",")) (pLit ")")
    where
        mkTuple _ exprs _ = foldl EAp (EConstrName name) exprs
            where name = "Tuple" ++ show (length exprs)


pPattern :: Parser [Pattern]
pPattern = pZeroOrMore pPatternExpr


pPatternExpr :: Parser Pattern
pPatternExpr =
    (pVar `pApply` PVar) `pOr`
    (pNum `pApply` PNum) `pOr`
    (pChar `pApply` PChar) `pOr`
    pThen mkConstr pConstrName (pZeroOrMore pPatternExpr) `pOr`
    pThen3 mkListPattern (pLit "[") (pZeroOrMoreWithSep pPatternExpr (pLit ",")) (pLit "]") `pOr`
    pThen3 mkParenExpr (pLit "(") pPatternConsList (pLit ")") `pOr`
    pThen3 mkParenExpr (pLit "(") pPatternExpr (pLit ")")
    where
        mkListPattern _ patterns _ = foldr cons (PConstrName "Nil" []) patterns
        mkConstr name patExprs = PConstrName name patExprs
        mkParenExpr _ expr _ = expr

        cons expr list = PConstrName "Cons" [expr, list]


pPatternConsList :: Parser Pattern
pPatternConsList = pThen3 mkList pPatternExpr (pLit ":") pPatternExpr
    where mkList head _ tail = PConstrName "Cons" [head, tail]


pConstrDecl :: Parser Constructor
pConstrDecl = pThen mkConstr pConstrName pNum
    where
        mkConstr name arity = (name, undefinedTag, arity)


pProgram :: Parser PatProgram
pProgram = pThen mkProgram (pZeroOrMoreWithSep pDataType (pLit ";")) (pOneOrMoreWithSep pSc (pLit ";"))
    where
        mkProgram adts scs = (adts, scs)


pDataType :: Parser DataType
pDataType = pThen4 mkDataType (pLit "data") pDataTypeName (pLit "=") $ pOneOrMoreWithSep pConstrDecl $ pLit "|"
    where
        mkDataType _ name _ cs = (name, cs)


pSc :: Parser PatScDefn
pSc = pScSimple `pOr` pScWhere


pScSimple :: Parser PatScDefn
pScSimple = pThen4 mkSc pVar pPattern (pLit "=") pExpr
    where mkSc name pattern equals expr = PatScDefn name [(pattern, expr)]


pScWhere :: Parser PatScDefn
pScWhere = pThen3 mkScWhere pScSimple (pLit "where") pDefns


mkScWhere (PatScDefn name [(pattern, expr)]) _ defns = PatScDefn name [(pattern, expr')]
    where expr' = ELet True defns expr


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
    (pChar `pApply` EChar) `pOr`
    (pConstrName `pApply` EConstrName) `pOr`
    pThen3 mkParenExpr (pLit "(") pExpr (pLit ")") `pOr`
    pList `pOr`
    pTuple
    where
        mkParenExpr _ expr _ = expr


pDefns :: Parser [Defn Pattern]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")


pDefn :: Parser (Defn Pattern)
pDefn =
    pThen3 mkVarDefn pPatternExpr (pLit "=") pExpr `pOr`
    pThen3 mkFunDefn (pOneOrMore pPatternExpr) (pLit "=") pExpr
    where
        mkVarDefn patExpr _ expr = (patExpr, expr)
        mkFunDefn (name : args) _ expr = (name, ELam args expr)


pAlts :: Parser [Alter Pattern Pattern]
pAlts = pOneOrMoreWithSep pAlt (pLit ";")


pAlt :: Parser (Alter Pattern Pattern)
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
    (pThen FoundOp (pLit "/") pMultExpr) `pOr`
    (pThen FoundOp (pLit "%" ) pMultExpr) `pOr`
    (pEmpty NoOp)


-- applicative expression
pApExpr :: Parser (Expr Pattern)
pApExpr = ((pOneOrMore pAtomicExpr) `pApply` mkApChain)
    where
        mkApChain (expr : exprs) = foldl EAp expr exprs

