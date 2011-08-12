module Lexer where

import Char

type Token = String
type TokenInfo = (Int, Token)

twoCharOps = ["==", "~=", ">=", "<=", "->"]

-- lexer implementation
lex :: String -> [Token]
lex s = map snd $ lex' s 1

lex' :: String -> Int -> [TokenInfo]
lex' [] _ = []
-- ignore whitespaces
lex' (c : cs) lnum | isWhiteSpace c = lex' cs lnum
-- ignore newlines
lex' (c : cs) lnum | isNewLine c = lex' cs (lnum+1)
-- numbers
lex' (c : cs) lnum | isDigit c =
    (lnum, numToken) : lex' restCs lnum
    where
        numToken = c : takeWhile isDigit cs
        restCs = dropWhile isDigit cs
-- variable names
lex' (c : cs) lnum | isAlpha c =
    (lnum, varToken) : lex' restCs lnum
    where
        varToken = c : takeWhile isIdChar cs
        restCs = dropWhile isIdChar cs
-- comments
lex' (c1 : c2 : cs) lnum | isComment c1 c2 = lex' restCs (lnum+1)
    where
        restCs = dropWhile (not . isNewLine) cs
-- relational operators
lex' (c1 : c2 : cs) lnum | op `elem` twoCharOps = (lnum, op) : lex' cs (lnum+1)
    where
        op = [c1] ++ [c2]
-- other
lex' (c : cs) lnum = (lnum, [c]) : lex' cs lnum


-- private helper functions
isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || c == '_'

isWhiteSpace :: Char -> Bool
isWhiteSpace c = c `elem` " \t"

isNewLine :: Char -> Bool
isNewLine c = c == '\n'

isComment :: Char -> Char -> Bool
isComment c1 c2 = c1 == '/' && c2 == '/'

