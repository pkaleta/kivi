module Parser where

import Char

-- line number and token
type Token = [Char]
type TokenInfo = (Int, Token)

twoCharOps = ["==", "~=", ">=", "<=", "->"]
keywords = ["let", "letrec", "case", "in", "of", "Pack"]

-- lexer implementation
clex :: String -> [TokenInfo]
clex s = clex' s 1

clex' :: String -> Int -> [TokenInfo]
clex' [] _ = []
-- ignore whitespaces
clex' (c : cs) lnum | isWhiteSpace c = clex' cs lnum
-- ignore newlines
clex' (c : cs) lnum | isNewLine c = clex' cs (lnum+1)
-- numbers
clex' (c : cs) lnum | isDigit c =
    (lnum, numToken) : clex' restCs lnum
    where
        numToken = c : takeWhile isDigit cs
        restCs = dropWhile isDigit cs
-- variable names
clex' (c : cs) lnum | isAlpha c =
    (lnum, varToken) : clex' restCs lnum
    where
        varToken = c : takeWhile isIdChar cs
        restCs = dropWhile isIdChar cs
-- comments
clex' (c1 : c2 : cs) lnum | isComment c1 c2 = clex' restCs (lnum+1)
    where
        restCs = dropWhile (not . isNewLine) cs
-- relational operators
clex' (c1 : c2 : cs) lnum | op `elem` twoCharOps = (lnum, op) : clex' cs (lnum+1)
    where
        op = [c1] ++ [c2]
-- other
clex' (c : cs) lnum = (lnum, [c]) : clex' cs lnum

--syntax analyser implementation
--syntax :: [Token] -> CoreProgram

--parser implementation
--parse :: String -> CoreProgram
--parse = syntax . clex

-- private helper functions
isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || c == '_'

isWhiteSpace :: Char -> Bool
isWhiteSpace c = c `elem` " \t"

isNewLine :: Char -> Bool
isNewLine c = c == '\n'

isComment :: Char -> Char -> Bool
isComment c1 c2 = c1 == '/' && c2 == '/'

type Parser a = [Token] -> [(a, [Token])]

-- parser functions

pSat :: (String -> Bool) -> Parser String
pSat pred (t : ts) | not (t `elem` keywords) && pred t = [(t, ts)]
                   | otherwise = []

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

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 tokens = (p1 tokens) ++ (p2 tokens)

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen combine p1 p2 tokens =
    [(combine v1 v2, tokens2) | (v1, tokens1) <- p1 tokens,
                                (v2, tokens2) <- p2 tokens1]

pThen3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 combine p1 p2 p3 tokens =
    [(combine v1 v2 v3, tokens3) | (v1, tokens1) <- p1 tokens,
                                   (v2, tokens2) <- p2 tokens1,
                                   (v3, tokens3) <- p3 tokens2]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore parser = (pOneOrMore parser) `pAlt` (pEmpty [])

pEmpty :: a -> Parser a
pEmpty ret tokens = [(ret, tokens)]

pOneOrMore :: Parser a -> Parser [a]
pOneOrMore parser = pThen (:) parser (pZeroOrMore parser)

pHelloOrGoodbye :: Parser String
pHelloOrGoodbye = (pLit "hello") `pAlt` (pLit "goodbye")

pGreeting :: Parser (String, String)
pGreeting =
    pThen3 mkGreeting pHelloOrGoodbye pVar (pLit "!")
    where
        mkGreeting a b _ = (a, b)

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
            `pAlt`
            (pEmpty [])

-- test
pSepGreets :: Parser [(String, String)]
pSepGreets = pOneOrMoreWithSep pGreeting (pLit ";")
    where
        combine x xs = x:xs

