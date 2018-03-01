import Data.List (nub)

--Harkaranjeet Singh
---- String operations (note: String = [Char])

-- Length and concatenation (Def 2.2, reimplements len and ++)
strlen :: String -> Int
strlen ""= 0
strlen xs = 1 + strlen(tail xs)

strcat :: String -> String -> String
strcat xs ""= ""
strcat "" ys = ys
strcat (x:xs) ys = x:(strcat xs ys)


---- Language operations. Assume inputs contain no duplicates, and insure that
---- outputs also contain no duplicates

type Language = [String]

-- Union of languages
union_lang :: Language -> Language -> Language
union_lang l1 [] = l1
union_lang [] l2 = l2
union_lang (l:l1) l2 | elem l l2 = union_lang l1 l2
                     | otherwise = l:union_lang l1 l2

-- Concatenation of languages (Def 2.5)
concat_lang :: Language -> Language -> Language
concat_lang l1 [] = l1
concat_lang l1 l2 = nub [strcat x y | x <- l1, y <- l2]


-- L^n = L * L * ... * L (n times)
power_lang :: Language -> Int -> Language
power_lang l 0 = []
power_lang l 1 = l
power_lang l n = concat_lang l (power_lang l (n - 1))

-- Bounded Kleene star, L* = L^0 U L^1 U L^2 U ... U L^n
bstar_lang :: Language -> Int -> Language
bstar_lang l 0 = []
bstar_lang l 1 = l
bstar_lang l n = union_lang  (bstar_lang l (n-1)) (power_lang l n)

-- Reimplements elem for Languages
element :: String -> Language -> Bool
element xs [] = False
element xs (l:ls) | xs == l = True
                  | otherwise = element xs ls

-- L1 subset L2
subset :: Language -> Language -> Bool
subset [] l2 = True
subset (l:l1) l2 | element l l2 = subset l1 l2
                 | otherwise = False


---- Regular expressions and the languages they denote
data RegExp = Empty
             | Str String
             | Cat RegExp RegExp
             | Union RegExp RegExp
             | Star RegExp

-- [[r]], except use bound 5 for Kleene star
lang_of :: RegExp -> Language
lang_of (Empty) = [] -- case empty
lang_of (Str r) = [r] -- case str
lang_of (Cat r1 r2) = concat_lang (lang_of r1) (lang_of r2) --case Cat
lang_of (Union a b) = union_lang (lang_of a) (lang_of b) -- case Union
lang_of (Star a) = bstar_lang (lang_of a ) 5  -- case Star
