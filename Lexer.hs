module Lexer where

import Char

type Token = [Char]
type TokenInfo = (Int, Token)

twoCharOps = ["==", "~=", ">=", "<=", "->"]

-- lexer implementation
clex :: String -> [Token]
clex s = map snd $ clex' s 1

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


-- private helper functions
isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || c == '_'

isWhiteSpace :: Char -> Bool
isWhiteSpace c = c `elem` " \t"

isNewLine :: Char -> Bool
isNewLine c = c == '\n'

isComment :: Char -> Char -> Bool
isComment c1 c2 = c1 == '/' && c2 == '/'

