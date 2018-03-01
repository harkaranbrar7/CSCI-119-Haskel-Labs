-- CSci 119, Lab 4
--Harkaranjeet Singh

---- Regular expressions, along with input and output
data RegExp = Empty
             | Letter Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp

instance (Show RegExp) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)


---------------- Part 1 ----------------

-- Implement the six recursive predications/operations on RegExp given in
-- Section 3.3 of the notes. Each should begin with a type declaration.
-- Include several tests for each function.


--Emptiness--

emptiness :: RegExp -> Bool
emptiness (Empty) = True
emptiness (Letter a) = False
emptiness (Union r1 r2) = emptiness(r1)
                        && emptiness(r2)
emptiness (Cat r1 r2) = emptiness(r1)
                      || emptiness(r2)
emptiness (Star r1) = False

-- Test Case for emptiness
--emptiness (Empty)
--emptiness (Letter 'd')
--emptiness (Union (Letter 'd') (Letter 'c'))
--emptiness (Union (Letter 'd') (Empty))
--emptiness (Union (Empty) (Letter 'd'))
--emptiness (Union (Empty) (Empty))
--emptiness (Cat (Letter 'd') (Letter 'c'))
--emptiness (Cat (Letter 'd') (Empty))
--emptiness (Cat (Empty) (Letter 'c'))
--emptiness (Cat (Empty) (Empty))
--emptiness (Star (Empty))
--emptiness (Star (Letter 'a'))


--Unitarity--
unitarity :: RegExp -> Bool
unitarity (Empty) = False
unitarity (Letter a) = False
unitarity (Union r1 r2) = (unitarity r1 && unitarity r2)
                        || (emptiness r1 && unitarity r2)
                        || (unitarity r1 && emptiness r2)
unitarity (Cat r1 r2) = (unitarity r1 && unitarity r2)
unitarity (Star r1) = (emptiness r1 || unitarity r1)

-- Test Case for unitarity
--unitarity (Empty)
--unitarity (Letter 'd')
--unitarity (Union (Letter 'd') (Letter 'c'))
--unitarity (Union (Letter 'd') (Empty))
--unitarity (Union (Empty) (Letter 'd'))
--unitarity (Union (Empty) (Empty))
--unitarity (Cat (Letter 'd') (Letter 'c'))
--unitarity (Cat (Letter 'd') (Empty))
--unitarity (Cat (Empty) (Letter 'c'))
--unitarity (Cat (Empty) (Empty))
--unitarity (Star (Empty))
--unitarity (Star (Letter 'a'))




--Bypassability--

bypassability :: RegExp -> Bool
bypassability (Empty) = False
bypassability (Letter a) = False
bypassability (Union r1 r2) = bypassability r1 || bypassability r2
bypassability (Cat r1 r2) = bypassability r1 && bypassability r2
bypassability (Star r1) = True

--bypassability (Empty)
--bypassability (Letter 'd')
--bypassability (Union (Letter 'd') (Letter 'c'))
--bypassability (Union (Letter 'd') (Empty))
--bypassability (Union (Empty) (Letter 'd'))
--bypassability (Union (Empty) (Empty))
--bypassability (Cat (Letter 'd') (Letter 'c'))
--bypassability (Cat (Letter 'd') (Empty))
--bypassability (Cat (Empty) (Letter 'c'))
--bypassability (Cat (Empty) (Empty))
--bypassability (Star (Empty))
--bypassability (Star (Letter 'a'))




--Infiniteness--

infiniteness :: RegExp -> Bool
infiniteness (Empty) = False
infiniteness (Letter a) = False
infiniteness (Union r1 r2) = infiniteness r1 || infiniteness r2
infiniteness (Cat r1 r2) = (infiniteness r1 && not (emptiness r2))
                          ||(infiniteness r2 && not (emptiness r1))
infiniteness (Star r1) = not (emptiness r1) && not (unitarity r1)


--infiniteness (Empty)
--infiniteness (Letter 'd')
--infiniteness (Union (Letter 'd') (Letter 'c'))
--infiniteness (Union (Letter 'd') (Empty))
--infiniteness (Union (Empty) (Letter 'd'))
--infiniteness (Union (Empty) (Empty))
--infiniteness (Cat (Letter 'd') (Letter 'c'))
--infiniteness (Cat (Letter 'd') (Empty))
--infiniteness (Cat (Empty) (Letter 'c'))
--infiniteness (Cat (Empty) (Empty))
--infiniteness (Star (Empty))
--infiniteness (Star (Letter 'a'))



-- Reversal--

reversal :: RegExp -> RegExp
reversal (Empty) = Empty
reversal (Letter a) = Letter a
reversal (Union r1 r2) = (Union (reversal r1) (reversal r2))
reversal (Cat r1 r2) = (Cat (reversal r1) (reversal r2))
reversal (Star r1) = (Star (reversal r1))

--reversal  (Empty)
--reversal  (Letter 'd')
--reversal (Union (Letter 'd') (Letter 'c'))
--reversal (Union (Letter 'd') (Empty))
--reversal (Union (Empty) (Letter 'd'))
--reversal (Union (Empty) (Empty))
--reversal (Cat (Letter 'd') (Letter 'c'))
--reversal (Cat (Letter 'd') (Empty))
--reversal (Cat (Empty) (Letter 'c'))
--reversal (Cat (Empty) (Empty))
--reversal (Star (Empty))
--reversal (Star (Letter 'a'))


-- Left Quotient--
leftquotient :: Char -> RegExp -> RegExp
leftquotient s (Empty) = (Empty)
leftquotient s (Letter a) = if s == a then (Star (Empty)) else Empty
leftquotient s (Union r1 r2) = (Union (leftquotient s r1) (leftquotient s r2))
leftquotient s (Cat r1 r2) = if (bypassability r1)
                            then
                                  (Union (Cat (leftquotient s r1) r2) (leftquotient s r2))
                            else
                                  (Cat (leftquotient s r1) r2)
leftquotient s (Star r1) = (Cat (leftquotient s r1) (Star r1))

--leftquotient 's'  (Empty)
--leftquotient 's'  (Letter 'd')
--leftquotient 's' (Union (Letter 'd') (Letter 'c'))
--leftquotient 's' (Union (Letter 'd') (Empty))
--leftquotient 's' (Union (Empty) (Letter 'd'))
--leftquotient 's' (Union (Empty) (Empty))
--leftquotient 's' (Cat (Letter 'd') (Letter 'c'))
--leftquotient 's' (Cat (Letter 'd') (Empty))
--leftquotient 's' (Cat (Empty) (Letter 'c'))
--leftquotient 's' (Cat (Empty) (Empty))
--leftquotient 's' (Star (Empty))
--leftquotient 's' (Star (Letter 'a'))



---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]

splits :: [a] -> [([a], [a])]
splits xs = [(take x xs, drop x xs) | x <- [0..(length xs)]]


--Matching Algorithm 1
match1 :: RegExp -> String -> Bool
match1 (Empty) w = False
match1 (Letter a) "" = False
match1 (Letter a) (b:w) = a == b && w == []
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or [ (match1 r1 w1) && (match1 r2 w2)
                        | (w1, w2) <- (splits w) ]
match1 (Star r1) w = (w == "") || or [ w1 /= "" && (match1 r1 w1)
                  && (match1 (Star r1) w2) | (w1, w2) <- (splits w) ]

--Test cases

--match1 (ab) "a"
--match1 (ttla) "b"
--match1 (ena) "c"
--match1 (bb1) "a"

--match1 (Union ttla ttla) "b"
--match1 (Union ttla Empty) "b"
--match1 (Union Empty Empty) "b"
--match1 (Union Empty ttla) "b"

--match1 (Cat ttla ttla) "b"
--match1 (Cat ttla Empty) "b"
--match1 (Cat Empty Empty) "b"
--match1 (Cat Empty ttla) "b"

--match1 (Star Empty) "b"
--match1 (Star ttla) "b"



--Matching Algorithm 2

match2 :: [RegExp] -> String -> Bool -> Bool
match2 [] w c = w == ""
match2 ((Empty):rs) w c = False
match2 ((Letter a):rs) "" c = False
match2 ((Letter a):rs) (b:w) c = (a:w) == (b:w) && (match2 rs w False)
match2 ((Union r1 r2):rs) w c = (match2 (r1:rs) w c) || (match2 (r2:rs) w c)
match2 ((Cat r1 r2):rs) w c = (match2 (r1:r2:rs) w c)
                            || ( c == True && bypassability(r1) && (match2 (r2:rs) w True) )
match2 ((Star r):rs) w c = (c == False && (match2 rs w False)) || (match2 (r:rs) w True)


--Test cases
--match2 [ab] "a" True
--match2 [ttla] "b" True
--match2 [ena] "c" True
--match2 [bb1] "a" True

--match2 [Union ttla ttla] "b" True
--match2 [Union ttla Empty] "b" True
--match2 [Union Empty Empty] "b" True
--match2 [Union Empty ttla] "b" True

--match2 [Cat ttla ttla] "b" True
--match2 [Cat ttla Empty] "b" True
--match2 [Cat Empty Empty] "b" True
--match2 [Cat Empty ttla] "b" True

--match2 [Star Empty] "b" True
--match2 [Star ttla] "b" True


-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get).

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once
