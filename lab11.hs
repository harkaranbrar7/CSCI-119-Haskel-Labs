---------------------------------------------------------------------------------
-- Harkaranjeet Singh
---------------------------------------------------------------------------------
import Data.List (nub,sort,tails)

sigma = "ab"

data FSM a = FSM {
  states :: [a],
  start  :: a,
  final_s :: [a],
  delta  :: [(a,Char,a)]
  }
---------------------------------------------------------------------------------
instance Show a => Show (FSM a) where
  show m = "("   ++ show (states m) ++
           ", "  ++ show (start m)  ++
           ", "  ++ show (final_s m) ++
           ", [" ++ steps (delta m) ++ "])" where
    steps [] = []
    steps [t] = step t
    steps (t:ts) = step t ++ "," ++ steps ts
    step (q,c,q') = show q ++ "/" ++ [c] ++ ">" ++ show q'
---------------------------------------------------------------------------------
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]
---------------------------------------------------------------------------------
rmdups [] = []
rmdups [x] = [x]
rmdups (x:ys) | x == head ys = rmdups ys
              | otherwise = x : rmdups ys

ap2 ((x,y):rs) a = if x == a then y else ap2 rs a

---------------------------------------------------------------------------------
closure :: Ord a => [a] -> (a -> [a]) -> [a]
closure start step = stable $ iterate close (start,[]) where
  stable ((frr,xs):rest) = if null frr then xs else stable rest
  close (frr, xs) = (frr', xs') where
      xs' = frr ++ xs
      frr' = nub $ filter (`notElem` xs') (concatMap step frr)

---------------------------------------------------------------------------------
minimize :: Ord a => FSM a -> FSM a
minimize (FSM {states=qs, start=s, final_s=fs, delta=ts}) = FSM {
  states = reps,
  start  = rep s,
  final_s = [q | q <- reps, elem q fs],
  delta  = [(q,a,rep q') | (q,a,q') <- ts, elem q reps]
  } where
    qs' = sort qs
    lt  = [(q1,q2) | (q1:rest) <- tails qs', q2 <- rest]
    leq = [(q1,q2) | (q1:rest) <- tails qs', q2 <- q1:rest]
    dinv q a = [q1 | (q1,b,q2) <- ts, q2 == q, b == a]
    dist = closure init step
    init = [p | p <- lt, elem (fst p) fs /= elem (snd p) fs]
    step (q1,q2) = concatMap (\a -> dinv q1 a >< dinv q2 a) sigma
    eq  = [p | p <- leq, notElem p dist]
    eq' = [p | (p:rs) <- tails eq, null rs || fst p < fst (head rs)]
    reps = rmdups $ map snd eq'
    rep = ap2 eq'
---------------------------------------------------------------------------------
