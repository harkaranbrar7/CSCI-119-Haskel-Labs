-- Lab 8: Non-deterministic finite state machines
-- Feel free to use any additional functions from previous labs
--Harkaranjeet Singh

import Data.List (sort, subsequences)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }

-- Output format for FSMs
instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (finals m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'


-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a


---- Lab 8 begins here -----------------------------------------------------

-- Nondeterministic FSMs
data NFSM a = NFSM {
  nstates :: [a],
  nstarts :: [a],
  nfinals :: [a],
  ndelta  :: [(a,Char,a)]
  }

-- nap ts q a == the normalized list of q' such that (q, a, q') is in ts
nap :: Ord a => [(a,Char,a)] -> a -> Char -> [a]
nap ts q a = norm [q2 |(q1,c,q2)<-ts, q1 == q, c == a]

-- ndelta_star m q w == normalized list of states m goes to from q on w
ndelta_star :: Ord a => NFSM a -> a -> [Char] -> [a]
ndelta_star m q [] = [q]
ndelta_star m q (a:w) = concat ( norm [ndelta_star m qa w | qa <- (nap (ndelta m) q a)] )


naccept :: Ord a => NFSM a -> [Char] -> Bool
naccept m w = or [elem x (nfinals m) | q <- nstarts m, x <- ndelta_star m q w]


----------------------------------------------------------------
-- Nondeterministic FSMs with epsilon moves
data EFSM a = EFSM {
  estates :: [a],
  estarts :: [a],
  efinals :: [a],
  edelta  :: [(a,Char,a)],
  epsilon :: [(a,a)]
  }


-- Normalized epsilon closure of a set of states
-- (Hint: look at definition of reachable below)
eclose :: Ord a => EFSM a -> [a] -> [a]
eclose m qs = sort $ stable $ iterate close (qs, []) where
                stable ((fr,qs):rest) = if null qs then fr else stable rest
                close (fr, xs) = (fr', xs') where
                  xs' = fr ++ xs
                  fr' = norm $ filter (`notElem` xs') (concatMap step fr)
                  step q = norm [qa | (q, qa)<-epsilon m, elem q fr']


-- edelta_star m q w == eclosed list of states m goes to from q on w
edelta_star :: Ord a => EFSM a -> a -> [Char] -> [a]
edelta_star m q "" = [q]
edelta_star m q (a:w) = eclose m (concat [edelta_star m qa w | qa <- eclose m (nap (edelta m) q a) ])


eaccept :: Ord a => EFSM a -> [Char] -> Bool
eaccept m w = overlap  (efinals m) (concat $ norm [edelta_star m qa w | qa <- (estarts m)])



----------------------------------------------------------------
-- Machine conversions

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm m = NFSM {
  nstates = states m,
  nstarts = [start m],
  nfinals = finals m,
  ndelta  = delta m
  }


-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm m = FSM {
    states = subsequences (nstates m),
    start = nstarts m,
    finals = [fi | fi<-states (nfsm_to_fsm m), overlap (nfinals m) fi],
    delta = norm [ (q, a, ( norm [ qb | (qa,aa,qb) <- (ndelta m), elem qa q, a == aa ] ) ) | (x,a,y) <- (ndelta m), q <- states (nfsm_to_fsm m) ]
}


-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm m = FSM {
    states = norm (subsequences (estates m)),
    start = [st | st<-(eclose m (estarts m))],
    finals = [fi | fi<-states (efsm_to_fsm m), overlap (efinals m) fi],
    delta = norm [ (q, a, (eclose (m) ( norm [qb | (qa,aa,qb) <- (edelta m), elem qa q, a == aa ] ) ) ) | (x,a,y) <- (edelta m), q <- states (efsm_to_fsm m) ]
}

fdelta :: Eq a => FSM a -> a -> Char -> a
fdelta m = ap (delta m)

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . fdelta

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m w = elem (delta_star m (start m) w) (finals m)

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m q [] = elem q (finals m)
accept2_aux m q (a:w) = accept2_aux m (fdelta m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m w = accept2_aux m (start m) w


even_a_e = EFSM { estates = [0,1], estarts = [0], efinals = [0], edelta = [(i, a, d i a) | i <- [0,1], a <- sigma], epsilon = [(0, 0), (1, 1)] } where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

no_trip_e = EFSM { estates = [0..3], estarts = [0], efinals = [0..2], edelta = [(i, a, d i a) | i <- [0..3], a <- sigma], epsilon = [(0, 0), (1, 0), (2, 0), (3, 3)] } where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0

even_as = FSM { states = [0,1], start = 0, finals = [0], delta = [(i, a, d i a) | i <- [0,1], a <- sigma] } where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

no_aaa = FSM { states = [0..3], start = 0, finals = [0..2], delta = [(i, a, d i a) | i <- [0..3], a <- sigma] } where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0


{- Tests:

1. m and fsm_to_nfsm m accept the same strings
2. m and nfsm_to_fsm m accept the same strings
3. m and efsm_to_fsm m accept the same strings

-}


---- Lab 8 ends here ----------------------------------------------------

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable (FSM {states=qs, start=s, finals=fs, delta=d}) =
  FSM {states=qs', start=s, finals=fs', delta=d'} where
    qs' = sort $ stable $ iterate close ([s], [])
    fs' = filter (`elem` qs') fs
    d'  = filter (\(q,_,_) -> q `elem` qs') d
    stable ((fr,qs):rest) = if null fr then qs else stable rest
    -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
    close (fr, xs) = (fr', xs') where
      xs' = fr ++ xs
      fr' = norm $ filter (`notElem` xs') (concatMap step fr)
      step q = map (ap d q) sigma


-- Change the states of an FSM from an equality type to Int
intify :: Eq a => FSM a -> FSM Int
intify m = FSM {
  states = map index (states m),
  start  = index (start m),
  finals = map index (finals m),
  delta  = [(index q, a, index q') | (q,a,q') <- delta m]
  } where
    index q = lookup (states m) q
    lookup (q':qs) q = if q == q' then 0 else 1 + lookup qs q










    -- accept1 even_as ""
    -- accept1 even_as "a"
    -- accept1 even_as "aa"
    -- accept1 even_as "aaa"
    -- accept1 even_as "aaaa"
    -- accept1 even_as "aaba"
    -- accept1 even_as "aabaa"
    --
    -- naccept (fsm_to_nfsm even_as) ""
    -- naccept (fsm_to_nfsm even_as) "a"
    -- naccept (fsm_to_nfsm even_as) "aa"
    -- naccept (fsm_to_nfsm even_as) "aaa"
    -- naccept (fsm_to_nfsm even_as) "aaaa"
    -- naccept (fsm_to_nfsm even_as) "aaba"
    -- naccept (fsm_to_nfsm even_as) "aabaa"
    --
    -- naccept (fsm_to_nfsm even_as) ""
    -- naccept (fsm_to_nfsm even_as) "a"
    -- naccept (fsm_to_nfsm even_as) "aa"
    -- naccept (fsm_to_nfsm even_as) "aaa"
    -- naccept (fsm_to_nfsm even_as) "aaaa"
    -- naccept (fsm_to_nfsm even_as) "aaba"
    -- naccept (fsm_to_nfsm even_as) "aabaa"
    --
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) ""
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) "a"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) "aa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) "aaa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) "aaaa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) "aaba"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm even_as) "aabaa"
    --
    -- naccept (fsm_to_nfsm no_aaa) ""
    -- naccept (fsm_to_nfsm no_aaa) "aa"
    -- naccept (fsm_to_nfsm no_aaa) "aaba"
    -- naccept (fsm_to_nfsm no_aaa) "aabaa"
    -- naccept (fsm_to_nfsm no_aaa) "abaa"
    -- naccept (fsm_to_nfsm no_aaa) "baa"
    -- naccept (fsm_to_nfsm no_aaa) "aab"
    -- naccept (fsm_to_nfsm no_aaa) "aaa"
    -- naccept (fsm_to_nfsm no_aaa) "baaa"
    -- naccept (fsm_to_nfsm no_aaa) "aaab"
    -- naccept (fsm_to_nfsm no_aaa) "baaaba"
    --
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) ""
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "aa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "aaba"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "aabaa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "abaa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "baa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "aab"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "aaa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "baaa"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "aaab"
    -- accept1 (nfsm_to_fsm $ fsm_to_nfsm no_aaa) "baaaba"
    --
    -- eaccept even_a_e ""
    -- eaccept even_a_e "a"
    -- eaccept even_a_e "aa"
    -- eaccept even_a_e "aaa"
    -- eaccept even_a_e "aaaa"
    -- eaccept even_a_e "aaba"
    -- eaccept even_a_e "aabaa"
    --
    -- accept1 (efsm_to_fsm even_a_e) ""
    -- accept1 (efsm_to_fsm even_a_e) "a"
    -- accept1 (efsm_to_fsm even_a_e) "aa"
    -- accept1 (efsm_to_fsm even_a_e) "aaa"
    -- accept1 (efsm_to_fsm even_a_e) "aaaa"
    -- accept1 (efsm_to_fsm even_a_e) "aaba"
    -- accept1 (efsm_to_fsm even_a_e) "aabaa"
    --
    -- eaccept no_trip_e ""
    -- eaccept no_trip_e "aa"
    -- eaccept no_trip_e "aaba"
    -- eaccept no_trip_e "aabaa"
    -- eaccept no_trip_e "abaa"
    -- eaccept no_trip_e "baa"
    -- eaccept no_trip_e "aab"
    -- eaccept no_trip_e "aaa"
    -- eaccept no_trip_e "baaa"
    -- eaccept no_trip_e "aaab"
    -- eaccept no_trip_e "baaaba"
    --
    -- accept1 (efsm_to_fsm no_trip_e) ""
    -- accept1 (efsm_to_fsm no_trip_e) "aa"
    -- accept1 (efsm_to_fsm no_trip_e) "aaba"
    -- accept1 (efsm_to_fsm no_trip_e) "aabaa"
    -- accept1 (efsm_to_fsm no_trip_e) "abaa"
    -- accept1 (efsm_to_fsm no_trip_e) "baa"
    -- accept1 (efsm_to_fsm no_trip_e) "aab"
    -- accept1 (efsm_to_fsm no_trip_e) "aaa"
    -- accept1 (efsm_to_fsm no_trip_e) "baaa"
    -- accept1 (efsm_to_fsm no_trip_e) "aaab"
    -- accept1 (efsm_to_fsm no_trip_e) "baaaba"
