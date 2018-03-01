---- CSci 119, Lab 1 ----
---- Harkaranjeet Singh ---------------
-- Note: you will replace all instances of "undefined" below with your answers.


---- Boolean operators

-- The following code tests whether "and" is commutative:
bools = [True, False]
and_commutes = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar defintions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and"
or_commutes = and  [(p || q) == (q || p) | p <- bools, q <- bools]
and_assoc = and [(p && (q && r)) == ((p && q) && r) | p <- bools, q <-bools, r <-bools]
or_assoc = and [(p || (q || r)) == ((p || q) || r) | p <- bools, q <-bools, r <-bools]
and_dist = and [(p && (q || r)) == ((p && q) || (p && r)) | p <- bools, q <- bools, r <- bools]
or_dist = and [(p || (q && r)) == ((p || q) && (p || r)) | p <- bools, q <- bools, r <- bools]

-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above
xor_commutes = and [(p /= q) == (q /= p) | p <- bools, q <- bools]
xor_assoc    = and [(p /= (q /= r)) == ((p /= q) /= r) | p <- bools, q <-bools, r <-bools]
xor_dist_and = and [(p /= (q && r)) == ((p /= q) && (p /= r)) | p <- bools, q <- bools, r <- bools]
xor_dist_or  = and [(p /= (q || r)) == ((p /= q) || (p /= r)) | p <- bools, q <- bools, r <- bools]
and_dist_xor = and [(p && (q /= r)) == ((p && q) /= (p && r)) | p <- bools, q <- bools, r <- bools]
or_dist_xor  = and [(p || (q /= r)) == ((p || q) /= (p || r)) | p <- bools, q <- bools, r <- bools]

-- The implication operator on Bool in Haskell is equivalent to <=.
-- Check whether implication is associative or commutative:
assoc_imp = and [(p <= (q <= r)) == ((p <= q) <= r) | p <- bools, q <-bools, r <-bools]
comm_imp = and [(p <= q) == (q <= p) | p <- bools, q <- bools]


----- Evaluating statements involving quantifiers

-- Assume that the universe of discourse is the set {1,2,3,4,5,6,7,8},
-- that is, that the word "number" temporarily means 1, 2, ..., 8.

u = [1..8]

-- Translate each of the following statements first, in a comment, into a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true. I'll work one example.
--
--
-- 1. "Every number that's greater than 2 is greater than 1"
-- A: for all n, (n > 2) imp (n > 1)
prob1 = and [(n > 2) <= (n > 1) | n <- u]

--
-- 2. Every number is either greater than 1 or less than 2
-- A: for all n, (n > 1) or (n < 2)
prob2 = and [(n > 1) || (n < 2) | n <- u]

--
-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- A: for all n, m (n <= m) or (m <= n)
prob3 = and [(n <= m) || (m <= n) | n <- u, m <- u]

-- 4. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- A:for all n, odd n -> exists m , even m && m > n
prob4 = and [ or [n < m | m<-u, even m] | n<-u, odd n]

-- 5. For every even number, there is a greater odd number
-- A: for all n , even n -> exists m, odd m && m > n
prob5 = and [ or [n < m | m<-u, odd m] | n<-u, even n]

-- 6: There are two odd numbers that add up to 6
-- A: exists n odd n exists m odd m,  imp n + m == 6
prob6 = or [ n + m == 6 | m <-u, odd m, n <- u, odd n]

-- 7. There is a number that is at least as large as every number
--    (i.e., according to >= )
-- A: for all n, exists m  imp m >= n
prob7 = or [and [n >= m | m <- u] | n <- u]

-- 8. For every number, there is a different number such that there are no
--    numbers between these two.
-- A: for all n, exists m  imp ( (n-m == 1) || ( n-m == (-1) ))
prob8 = or [(n - m == 1) || (n - m == (-1)) | n <- u, m <- u, n /= m]
