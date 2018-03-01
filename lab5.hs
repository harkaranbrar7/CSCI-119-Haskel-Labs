-- CSci 119, Lab 5
-- Harkaranjeet Singh
-- Reference: Lecture notes, Sections 4.1, 4.2
sigma = ['a', 'b']

-- Finite State Machine M = (Q, q0, F, d)
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

-- Check whether a finite state machine (qs, q0, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (q0 is in qs)
-- (3) Final states are states (fs is a subset of qs; don't worry about dups)
-- (4) Transition relation is a function from qs and sigma to qs (exactly one
--     output state for each state and letter from sigma)



unique :: Eq a => [a] -> Bool
unique [] = True
unique (state:states) = not (elem state states) && unique states

subset :: [Int] -> [Int]-> Bool
subset [] _ = True
subset (final: finals) states = (elem final states)
                                && subset finals states


check_trans :: [(Int, Char, Int)] -> [Int] -> Bool
check_trans [] _ = True
check_trans _ [] = False
check_trans (t@(s1, c, s2):ts) states = (elem s1 states) &&
                                 (elem c sigma) &&
                                 (elem s2 states) &&
                (and [s2 == s2'| (s1, c, s2) <- (t:ts), (s1', c', s2') <- (t:ts), c == c', s1 == s1'])&& check_trans ts states


checkFSM :: FSM -> Bool
checkFSM (qs, q0, fs, ts) = (unique qs) && (elem q0 qs) && (subset fs qs) && (check_trans ts qs)

-- Gives the transition function of the machine as a function
-- i.e., delta m q a = the state machine m goes to when reading a in state q
delta :: FSM -> Int -> Char -> Int
delta (m@(qs, q0, fs, (s1, c, s2):ts)) q a = head [ d | (q', a', d) <-ts, q==q', a==a']
--if ((s1 == q) && (c == a)) then s2 else 0

-- Gives the delta* function
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q [] = q
delta_star m q (w:ws) = (delta_star m) (delta m q w) ws


accept1_final_state :: FSM -> [Int]
accept1_final_state (qs, q0, fs, ts) = fs

accept1_start_state :: FSM -> Int
accept1_start_state (qs, q0, fs, ts) = q0


-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m@(qs,q0,fs,ts) w = elem (delta_star m q0 w) fs


-- Machine acceptance, Definition 2 (via L_q(M))

accept2_aux_final_state :: FSM -> Int -> Bool
accept2_aux_final_state (qs, q0, fs, ts) q = q `elem` fs

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m@(qs, q0, fs, ts) q [] = elem q fs
accept2_aux m q (w:ws) = accept2_aux m (delta m q w) ws

accept2_start_state :: FSM -> Int
accept2_start_state (qs, q0, fs, ts) = q0

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m w = accept2_aux m (accept2_start_state m) w


-- Define a machine that accepts exactly the strings with an even number of a's
-- and test it adequately
even_a :: FSM Int
even_a = ([0,1], 0, [0], [(i, a, d i a) | i <- [0,1], a <- sigma]) where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i


-- Define a machine that accepts exactly the strings that do not contain "aaa"
-- as a substring and test it adequately
no_aaa :: FSM Int
no_aaa = ([0..3], 0, [0..2], [(i, a, d i a) | i <- [0..3], a <- sigma]) where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0
