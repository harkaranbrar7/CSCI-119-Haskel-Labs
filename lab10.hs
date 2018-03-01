-- Lab 10: REG closure under other operations

--Harkaranjeet Singh


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
  showsPrec d (Star Empty)  = showString "1"
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}, and a show instance.
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'


-- Implement each of the following operations on regular expressions or FSMs
--------------------------------------------------------------------------------
toRE :: [Char] -> RE
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)

--------------------------------------------------------------------------------
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a
--------------------------------------------------------------------------------
delta_1 :: Eq a => FSM a -> a -> Char -> a
delta_1 = ap . delta
--------------------------------------------------------------------------------
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta_1
--------------------------------------------------------------------------------
accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m w = elem (delta_star m (start m) w) (finals m)
--------------------------------------------------------------------------------
-- [[reverseRE r]] = rev([[r]]), defined by recursion on r
reverseRE :: RE -> RE
reverseRE Empty = Empty
reverseRE (Letter c) = (Letter c)
reverseRE (Union r1 r2) = Union (reverseRE r1) (reverseRE r2)
reverseRE (Cat r1 r2) = Cat (reverseRE r2)(reverseRE r1)
reverseRE (Star r) = Star (reverseRE r)
--------------------------------------------------------------------------------
-- L(complementFSM M) = Sigma^* - L(M)
complementFSM :: Ord a => FSM a -> FSM a
complementFSM m = FSM {
                    states = (states m),
                    start = (start m),
                    finals = [x |x <- (states m), (x `elem` (finals m)) == False ],
                    delta = (delta m)
                    }
--------------------------------------------------------------------------------
-- L(intersectFSM m1 m2) = L(m1) intersect L(m2)
intersectFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a,b)
intersectFSM m1 m2 = FSM {
                       states = [(q1, q2) |
                                            q1 <- (states m1), q2 <- (states m2)],
                       start = (start m1, start m2),
                       finals = [(f1, f2) |
                                            f1 <- (finals m1), f2 <- (finals m2)],
                       delta = [((qm1, qm2), c, (dm1, dm2)) |
                                                              (qm1, c, dm1)<-(delta m1), (qm2, c', dm2)<- (delta m2), c == c']
                       }
--------------------------------------------------------------------------------
even_as :: FSM Int
even_as = FSM { states = [0,1], start = 0, finals = [0], delta = [(i, a, d i a) |
                                                                                  i <- [0,1], a <- sigma] } where
 d i 'a' = (i + 1) `mod` 2
 d i 'b' = i
--------------------------------------------------------------------------------
no_aaa :: FSM Int
no_aaa = FSM { states = [0..3], start = 0, finals = [0..2], delta = [(i, a, d i a) |
                                                                                    i <- [0..3], a <- sigma] } where
 d i 'a' = min 3 (i + 1)
 d 3 'b' = 3
 d _ 'b' = 0
--------------------------------------------------------------------------------
-- [[himage r h]] = h^*([[r]]), defined by recursion on r
himage :: RE -> (Char -> [Char]) -> RE
himage Empty _ = Empty
himage (Letter c) h = toRE (h c)
himage (Union r1 r2) h = Union (himage r1 h) (himage r2 h)
himage (Cat r1 r2) h = Cat (himage r1 h) (himage r2 h)
himage (Star r) h = Star (himage r h)
--------------------------------------------------------------------------------
h :: Char -> [Char]
h 'a' = "ab.a."
h 'b' = "ba.b."
--------------------------------------------------------------------------------
-- L(hinvimage m h) = (h^*)^{-1}(L(m))
hinvimage :: Ord a => FSM a -> (Char -> [Char]) -> FSM a
hinvimage m h = FSM {
                  states = states m,
                  start  = start m,
                  finals  = finals m,
                  delta = [(q, a, (delta_star m (start m) [x |
                                                              x <- (h a), elem x sigma])) |
                                                              q <- (states m), a <- sigma]
                  }
--------------------------------------------------------------------------------
-- L(rightq m a) = { w | wa in L(m) }
rightq :: Ord a => FSM a -> Char -> FSM a
rightq m a = FSM{
               states = states m,
               start  = start m,
               finals = [delta_star m (start m) [a] |
                                                      elem (delta_star m (start m) [a]) (finals m)],
               delta = delta m
               }
--------------------------------------------------------------------------------
-- Note: left quotient was already implemented in a previous lab


-- reverseRE (Empty)
-- reverseRE (Letter 'c')
-- reverseRE (Union (Letter 'a') (Letter 'b'))
-- reverseRE (Cat (Letter 'a') (Letter 'b'))
-- reverseRE (Star (Cat (Letter 'a') (Letter 'b')))
-- reverseRE (Star (Union (Letter 'a') (Letter 'b')))
-- reverseRE (toRE 'aa+')
--
-- even_as
-- no_aaa
-- complementFSM even_as
-- complementFSM no_aaa
-- intersectFSM even_as no_aaa
-- intersectFSM no_aaa even_as
--
-- himage (Empty) h
-- himage (Letter 'a') h
-- himage (Letter 'b') h
-- himage (Union (Letter 'b') (Letter 'a')) h
-- himage (Cat (Letter 'a') (Letter 'b')) h
-- himage (Star (Letter 'a')) h
-- himage (Union (Cat (Letter 'a') (Letter 'b')) (Star (Letter 'b'))) h
--
-- even_as
-- no_aaa
-- hinvimage even_as h
-- hinvimage no_aaa h
--
-- rightq even_as 'a'
-- rightq no_aaa 'a'
-- rightq no_aaa 'b'
