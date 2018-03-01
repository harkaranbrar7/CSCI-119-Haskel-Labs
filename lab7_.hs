-- Lab 7: Convert FSMs to regular expressions

--
-- Harkaranjeet Singh --
--
--


import Data.List (sort, elemIndex)


---------------- Given functions ----------------

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Ordinary regular expressions and a show method for them
data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE
instance (Show RE) where    -- use precedence to minimize parentheses
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

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RE' = Zero | One | Letter' Char | Union' [RE'] | Cat' [RE'] | Star' RE'
  deriving (Eq, Ord, Show)

-- Convert ordinary REs into extended REs
toRE' :: RE -> RE'
toRE' Empty = Zero
toRE' (Letter c) = Letter' c
toRE' (Union r1 r2) = Union' [toRE' r1, toRE' r2]
toRE' (Cat r1 r2) = Cat' [toRE' r1, toRE' r2]
toRE' (Star r1) = Star' (toRE' r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
toRE :: RE' -> RE
toRE Zero = Empty
toRE One = Star Empty
toRE (Letter' c) = Letter c
toRE (Union' []) = Empty
toRE (Union' [r]) = toRE r
toRE (Union' (r:rs)) = Union (toRE r) (toRE (Union' rs))
toRE (Cat' []) = Star Empty
toRE (Cat' [r]) = toRE r
toRE (Cat' (r:rs)) = Cat (toRE r) (toRE (Cat' rs))
toRE (Star' r) = Star (toRE r)

-- Basic postfix parser for RE', assuming binary + and ., for testing
re :: String -> RE'
re w = re' w [] where
  re' [] [r] = r
  re' ('0':xs) rs = re' xs (Zero:rs)
  re' ('1':xs) rs = re' xs (One:rs)
  re' ('+':xs) (r2:r1:rs) = re' xs (Union' [r1,r2]:rs)
  re' ('.':xs) (r2:r1:rs) = re' xs (Cat' [r1,r2]:rs)
  re' ('*':xs) (r:rs) = re' xs (Star' r:rs)
  re' (x:xs) rs = re' xs (Letter' x:rs)


-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }


-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a


---------------- Lab 7 begins here ----------------

sigma = "ab"  -- Everything below should work with any choice of sigma


-------- Part 1

-- Reimplement your RE operations from Part 1 of Lab 4 for the type RE'

-- Implement one more function: proper (cannot recognize epsilon)
proper :: RE' -> Bool
proper Zero = True
proper One = False
proper (Letter' c) = True
proper (Union' rs) = all proper rs --all unions have to be proper
proper (Cat' rs) =  any proper rs --at list one character has to be proper
proper (Star' r) = False


-- (proper (Zero))
-- (proper (re "a"))
-- (proper (re "00+"))
-- (proper (re "0b+"))
-- (proper (re "a0+"))
-- (proper (re "ab+"))
-- (proper (re "0*0*+"))
-- (proper (re "00."))
-- (proper (re "0b."))
-- (proper (re "a0."))
-- (proper (re "ab."))
-- (proper (re "0*0*."))
-- (proper (re "a*"))
-- (proper (re "0*"))
-- (proper (re "0*0*0*0*0*0*....."))
-- (proper (re "0*0*0*0*0*a....."))
-- (proper (re "0*0*a*0*0*0....."))
-- (proper (re "a*0*0*0*0*0....."))
-- (proper (re "0*0*."))
-- (proper (re "0*0*0*0*0*0*+++++"))
-- (proper (re "0*0*0*0*0*a+++++"))
-- (proper (re "0*0*a*0*0*0+++++"))
-- (proper (re "a*0*0*0*0*0+++++"))
-- (proper (re "0*0*+"))proper

emptiness :: RE' -> Bool
emptiness Zero = True
emptiness One = emptiness (Star' Zero)
emptiness (Letter' c) = False
emptiness (Union' rs) = all emptiness rs
emptiness (Cat' rs) = any emptiness rs
emptiness (Star' r) = False


-- (emptiness (Zero))
-- (emptiness (re "a"))
-- (emptiness (re "00+"))
-- (emptiness (re "0b+"))
-- (emptiness (re "a0+"))
-- (emptiness (re "ab+"))
-- (emptiness (re "0*0*+"))
-- (emptiness (re "00."))
-- (emptiness (re "0b."))
-- (emptiness (re "a0."))
-- (emptiness (re "ab."))
-- (emptiness (re "0*0*."))
-- (emptiness (re "a*"))
-- (emptiness (re "0*"))
-- (emptiness (re "0*0*0*0*0*0*+++++"))
-- (emptiness (re "0*0*0*0*0*a+++++"))
-- (emptiness (re "0*0*a*0*0*0+++++"))
-- (emptiness (re "a*0*0*0*0*0+++++"))
-- (emptiness (re "0*0*+"))


unitarity :: RE' -> Bool
unitarity Zero = False
unitarity One = unitarity (Star' Zero)
unitarity (Letter' c) = False
unitarity (Union' rs@(r1:rs1)) = (all unitarity rs) || (emptiness (r1) && all unitarity rs1) || (unitarity (r1) && all emptiness rs1)
unitarity (Cat' rs) = all unitarity rs
unitarity (Star' r) = emptiness (r) || unitarity (r)


-- (unitarity (Zero))
-- (unitarity (re "a"))
-- (unitarity (re "00+"))
-- (unitarity (re "0b+"))
-- (unitarity (re "a0+"))
-- (unitarity (re "ab+"))
-- (unitarity (re "0*0*+"))
-- (unitarity (re "00."))
-- (unitarity (re "0b."))
-- (unitarity (re "a0."))
-- (unitarity (re "ab."))
-- (unitarity (re "0*0*."))
-- (unitarity (re "a*"))
-- (unitarity (re "0*"))
-- (unitarity (re "0*0*0*0*0*0*+++++"))
-- (unitarity (re "0*0*0*0*0*a+++++"))
-- (unitarity (re "0*0*a*0*0*0+++++"))
-- (unitarity (re "a*0*0*0*0*0+++++"))
-- (unitarity (re "0*0*+"))



bypassability :: RE' -> Bool
bypassability Zero = False
bypassability One = bypassability (Star' Zero)
bypassability (Letter' c) = False
bypassability (Union' rs) = any bypassability rs
bypassability (Cat' rs) = all bypassability rs
bypassability (Star' r) = True


-- (bypassability (Zero))
-- (bypassability (re "a"))
-- (bypassability (re "00+"))
-- (bypassability (re "0b+"))
-- (bypassability (re "a0+"))
-- (bypassability (re "ab+"))
-- (bypassability (re "0*0*+"))
-- (bypassability (re "00."))
-- (bypassability (re "0b."))
-- (bypassability (re "a0."))
-- (bypassability (re "ab."))
-- (bypassability (re "0*0*."))
-- (bypassability (re "a*"))
-- (bypassability (re "0*"))
-- (bypassability (re "0*0*0*0*0*0*....."))
-- (bypassability (re "0*0*0*0*0*a....."))
-- (bypassability (re "0*0*a*0*0*0....."))
-- (bypassability (re "a*0*0*0*0*0....."))
-- (bypassability (re "0*0*."))
-- (bypassability (re "0*0*0*0*0*0*+++++"))
-- (bypassability (re "0*0*0*0*0*a+++++"))
-- (bypassability (re "0*0*a*0*0*0+++++"))
-- (bypassability (re "a*0*0*0*0*0+++++"))
-- (bypassability (re "0*0*+"))



infiniteness :: RE' -> Bool
infiniteness Zero = False
infiniteness One = infiniteness (Star' Zero)
infiniteness (Letter' c) = False
infiniteness (Union' rs) = any infiniteness rs
infiniteness (Cat' rs@(r1:rs1)) = (infiniteness (r1) && not (all emptiness rs1)) || (all infiniteness rs1 && not (emptiness (r1)))
infiniteness (Star' r) = not (emptiness (r)) && not (unitarity (r))

--
-- (infiniteness (Zero))
-- (infiniteness (re "a"))
-- (infiniteness (re "00+"))
-- (infiniteness (re "0b+"))
-- (infiniteness (re "a0+"))
-- (infiniteness (re "ab+"))
-- (infiniteness (re "0*0*+"))
-- (infiniteness (re "00."))
-- (infiniteness (re "0b."))
-- (infiniteness (re "a0."))
-- (infiniteness (re "ab."))
-- (infiniteness (re "0*0*."))
-- (infiniteness (re "a*"))
-- (infiniteness (re "0*"))
-- (infiniteness (re "a*a*a*a*a*a*....."))
-- (infiniteness (re "0*0*0*0*0*0*....."))
-- (infiniteness (re "0*0*0*0*0*a....."))
-- (infiniteness (re "0*0*a*0*0*0....."))
-- (infiniteness (re "a*0*0*0*0*0....."))
-- (infiniteness (re "0*0*."))
-- (infiniteness (re "a*a*a*a*a*a*+++++"))
-- (infiniteness (re "0*0*0*0*0*0*+++++"))
-- (infiniteness (re "0*0*0*0*0*a+++++"))
-- (infiniteness (re "0*0*a*0*0*0+++++"))
-- (infiniteness (re "a*0*0*0*0*0+++++"))
-- (infiniteness (re "0*0*+"))


reversal :: RE' -> RE'
reversal Zero = Zero
reversal One = One
reversal (Letter' c) = (Letter' c)
reversal (Union' rs@(r1:[])) = reversal r1
reversal (Union' rs@(r1:rs1)) = (Union' ((reversal r1):[reversal (Union' rs1)]))
reversal (Cat' rs@(r1:[])) = reversal r1
reversal (Cat' rs@(r1:rs1)) = (Cat' ((reversal (Cat' rs1)):[reversal r1]))
reversal (Star' r) = (Star' (reversal(r)))


--
-- toRE (reversal (Zero))
-- toRE (reversal (re "a"))
-- toRE (reversal (re "00+"))
-- toRE (reversal (re "0b+"))
-- toRE (reversal (re "a0+"))
-- toRE (reversal (re "ab+"))
-- toRE (reversal (re "0*0*+"))
-- toRE (reversal (re "00."))
-- toRE (reversal (re "0b."))
-- toRE (reversal (re "a0."))
-- toRE (reversal (re "ab."))
-- toRE (reversal (re "0*0*."))
-- toRE (reversal (re "a*"))
-- toRE (reversal (re "0*"))
-- toRE (reversal (re "a*a*a*a*a*a*+++++"))
-- toRE (reversal (re "0*0*0*0*0*0*+++++"))
-- toRE (reversal (re "0*0*0*0*0*a+++++"))
-- toRE (reversal (re "0*0*a*0*0*0+++++"))
-- toRE (reversal (re "a*0*0*0*0*0+++++"))
-- toRE (reversal (re "0*0*+"))
-- toRE (reversal (re "a*a*a*a*a*a*....."))
-- toRE (reversal (re "0*0*0*0*0*0*....."))
-- toRE (reversal (re "0*0*0*0*0*a....."))
-- toRE (reversal (re "0*0*a*0*0*0....."))
-- toRE (reversal (re "a*0*0*0*0*0....."))
-- toRE (reversal (re "0*0*."))
-- toRE (reversal (re "a*b.cd.+"))
--


leftquotient :: Char -> RE' -> RE'
leftquotient c Zero = Zero
leftquotient c One = (Star' Zero)
leftquotient c1 (Letter' c2)
 | c1 == c2 = (Star' Zero)
 | otherwise = Zero
leftquotient c (Union' rs@(r1:[])) = leftquotient c r1
leftquotient c (Union' rs@(r1:rs1)) = (Union' ((leftquotient c r1):[(leftquotient c (Union' rs1))]))
leftquotient c (Cat' rs@(r1:[])) = leftquotient c r1
leftquotient c (Cat' rs@(r1:rs1))
 | bypassability r1 = (Union' ( (Cat' ( (leftquotient c r1):rs1 )):[(leftquotient c (Union' rs1))] ) )
 | otherwise = (Cat' ((leftquotient c r1):rs1))
leftquotient c (Star' r) = (Cat' ((leftquotient c r):[(Star' r)]))



-- toRE (leftquotient 'c' (re "aa.bb.."))
-- toRE (leftquotient 'a' (re "aa.bb.."))
-- toRE (leftquotient 'a' (re "a*b.cd.+"))

-------- Part 2

-- Solve a system of proper linear equations
-- You can assume that the system is correctly formed and proper
solve :: [[RE']] -> [RE'] -> [RE']

solve [] [] = []
solve ((l11:l1J) : rows) (l1':lI') = simp x1 : xI where
  -- l11 is the corner element, and l1J = [l12,...,l1n] is the rest of 1st row
  -- rows are the rest of the rows [[l21,...,l2n], ..., [ln1,...,lnn]]
  -- l1' is the first constant
  -- lI' are the rest of the contants [l2',...,ln']

  -- first column [l21, ..., ln1]
  lI1 = map head rows

  -- sub-matrix [[l22,...,l2n], ..., [ln2,...,lnn]]
  lIJ = map tail rows

  -- [[l22_bar,...,l2n_bar], ..., [ln2_bar,...,lnn_bar]] computed via (6)
  lIJ_bar = zipWith3 six lI1 lIJ l1J
  six li1 liJ l1j = map (\lij -> Union' [Cat' [li1, Star' l11, l1j], lij]) liJ

  -- [l2'_bar,..., ln'_bar] computed via (7)
  lI'_bar = zipWith seven lI1 lI'
  seven li1 li' = Union' [Cat' [li1, Star' l11, l1'], li']

  -- recursively solve the system of size n-1
  xI = solve lIJ_bar lI'_bar

  -- compute x1 from xI via (5)
  x1 = Cat' [Star' l11, Union' (zipWith (\lij xi -> Cat' [lij, xi]) l1J xI ++ [l1'])]


-- Generate a regular SPLE from an FSM via formulas in Theorem 6.5
toSPLE :: FSM Int -> ([[RE']], [RE'])
toSPLE m = (lIJ, lI') where
  qs = states m

  -- Construct matrix of coefficients (coef i j = Lij)
  lIJ = [[simp (coef i j) | j <- qs] | i <- qs]
  coef i j = Union' [Cat' [Letter' a, Star' Zero] | a <- sigma, d <- delta m, d == (i, a, j)]


  -- Construct constants
  lI' = [zeone q | q <- qs] where
    zeone a
      | elem a (finals m) = One
      | otherwise = Zero

-- Convert an FSM to a RE'
conv :: FSM Int -> RE'
conv m = simp $ solution !! start m where
  (matrix, consts) = toSPLE m
  solution = solve matrix consts


-- Test! Test! Test! (and show your tests here)

-- even_as is a machine that accepts strings with an even number of a's
-- states: (number of a's read so far) mod 2
even_as :: FSM Int
even_as = FSM { states = [0,1], start = 0, finals = [0], delta = [(i, a, d i a) | i <- [0,1], a <- sigma] } where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

-- no_aaa is a machine that accepts strings that don't have three a's in a row
-- states: number of a's in a row just read (n = 0, 1, 2), 3 is a trap
no_aaa :: FSM Int
no_aaa = FSM { states = [0..3], start = 0, finals = [0..2], delta = [(i, a, d i a) | i <- [0..3], a <- sigma] } where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0

even_num_a :: FSM Int
even_num_a = FSM { states = [0,1], start = 0, finals = [0], delta = [(0,'a',1),(1,'a',0),(0,'b',0),(1,'b',1)] }

evenFSM :: FSM Int
evenFSM = FSM { states = [0, 1, 2], start = 0, finals = [2], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 1), (2, 'b', 2)] }

fsmtest00 :: FSM Int
fsmtest00 = FSM { states = [0, 1, 2], start = 0, finals = [1], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 1), (2, 'b', 2)] }

fsmtest01 :: FSM Int
fsmtest01 = FSM { states = [0, 1, 2], start = 0, finals = [0], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 1), (2, 'b', 2)] }

fsmtest02 :: FSM Int
fsmtest02 = FSM { states = [0, 1, 2], start = 0, finals = [0, 1 ,2], delta = [(0, 'a', 1), (0, 'b', 0), (1, 'a', 2), (1, 'b', 1), (2, 'a', 1), (2, 'b', 2)] }


-- toRE (solve [[Letter' 'a', Letter' 'b', Zero], [Letter' 'a', Zero, Letter' 'b'], [Zero, Zero, Union' [Letter' 'a', Letter' 'b']]] [One, Zero, Zero] !! 0)
-- toRE (solve [[Letter' 'b', Letter' 'a'], [Zero, Union' [Letter' 'a', Letter' 'b']]] [One, Zero] !! 0)
-- toRE (solve [[re "a", re "b", re "0"], [re "a", re "0", re "b"], [re "0", re "0", re "ab+"]] [re "1", re "0", re "0"] !! 0)
-- toRE (solve [[re "b", re "a"], [re "0", re "ab+"]] [re "1", re "0"] !! 0)
--

-- toSPLE evenFSM
-- toSPLE even_as
-- toSPLE even_num_a
-- toSPLE fsmtest00
-- toSPLE fsmtest01
-- toSPLE fsmtest02




---------------- Lab 7 ends here ----------------------------------


{----------------------------------------------------------------------------
| Bonus feature:  A regular-expression simplifier
|----------------------------------------------------------------------------

A "simplified" RE' satisfies the following conditions:
(1) Every Union' is applied to a normalized list of two or more arguments,
    each of which is a One, Letter', Cat', or Star' (i.e., not Zero or Union')
(2) Every Cat' is applied to a list of two or more arguments, each of which is
    a Letter' or Star' (i.e., not Zero, One, Union', or Cat')
(3) Every Star' is applied to a Letter', Union', or Cat' (i.e., not Zero, One,
    or Star')

The following simplification rules, when applied repeatedly at every subterm
of a RE' until the RE' no longer changes, result in a simplified RE':

   Union' []                          --> Zero
   Union' [r]                         --> r
   Union' (rs1 ++ [Zero] ++ rs2)      --> Union' (rs1 ++ rs2)
   Union' (rs1 ++ [Union' rs] ++ rs2) --> Union' (rs1 ++ rs ++ rs2)
   Union' rs                          --> Union' (norm rs)                  (*)

   Cat' []                            --> One
   Cat' [r]                           --> r
   Cat' (rs1 ++ [Zero] ++ rs2)        --> Zero
   Cat' (rs1 ++ [One] ++ rs2)         --> Cat' (rs1 ++ rs2)
   Cat' (rs1 ++ [Union' rs] ++ rs2)   --> Union' (map (\r -> Cat' (rs1 ++ [r] ++ rs2)) rs)
   Cat' (rs1 ++ [Cat' rs] ++ rs2)     --> Cat' (rs1 ++ rs ++ rs2)

   Star' Zero                         --> One
   Star' One                          --> One
   Star' (Star' r)                    --> Star' r

(*) Note: this rule should only be applied if rs is not already normalized;
    normalization is used to realize the commutativity and idempotency of union
    (i.e., that  L1 u L2 = L2 u L1  and  L u L = L ).

However, it would be very inefficient to attempt to apply these rules in the
manner indicated. Instead, our approach is to stage the application of these
rules carefully to minimize the number of traversals of the regular expression.
-------------------------------------------------------------------------------}

simp :: RE' -> RE'
simp Zero = Zero
simp One = One
simp (Letter' c) = Letter' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RE'] -> RE'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RE'] -> RE'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RE' -> RE'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RE'] -> [RE']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RE'] -> [RE']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RE'] -> [RE'] -> [RE']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs
