module ProofBasedVerification
-- This is the work for Chapter 8: Property Based Testing
-- However, for Idris I am rechristening it "Proof Based Verification"
-- While "Property Based Testing" is still relevent with Idris,
-- I believe such Properties should predominantly be proven statically,
-- rather than "demonstrated with reasonable confidence" whenever they
-- can.
--
-- In an intuitionistic/contructionist logic/TT sometimesit gets pretty
-- hard to prove some things, so Prop based testing (ala QuickCheck/specs2)
-- is more appropriate.
--

total
listRepeat : Nat -> a -> List a
listRepeat Z _      = Nil
listRepeat (S n) x  = x :: (listRepeat n x)

total
sum1 : List Nat -> Nat
sum1 []         = 0
sum1 (x :: xs)  = x + (sum1 xs)

||| Exercise 1: Think of some props for
||| sum1
|||
total
exercise1a : (x : Nat) -> (n : Nat) -> sum1 (listRepeat n x) = (n * x)
exercise1a x n = ?exercise1a_rhs

||| This definition makes the proof for 1b easier in Idris,
||| though in Coq the foldl (flip (::)) Nil definition would
||| leave the proof quite doable.
|||
total
reverse1 : List a -> List a
reverse1 Nil = Nil
reverse1 (x :: xs) = xs ++ [x]

total
plusZero : (x : Nat) -> x = x + Z
plusZero x = ?plusZero_rhs

total
exercise1bLemma : (x : Nat) -> (y : Nat) -> S (plus y x) = plus y (S x)
exercise1bLemma x y = ?exercise1bLemma_rhs

total
plusCommutes : (x : Nat) -> (y : Nat) -> x + y = y + x
plusCommutes x y = ?plusCommutes_rhs

||| Exercise 1: Think of some props for
||| sum1
|||
total
exercise1b : (xs : List Nat) -> (ys : List Nat) -> sum1 (xs ++ ys) = (sum1 xs) + (sum1 ys)
exercise1b xs ys = ?exercise1b_rhs

||| Exercise 1: Think of some props for
||| sum1
|||
||| This is an example of a theorem that's hard to prove in idris.
||| I think it can be done in Coq though.
|||
total
exercise1c : (xs : List Nat) -> sum1 (reverse1 xs) = sum1 xs
exercise1c xs = ?exercise1c_rhs

-- Exercise 2
-- maximum should have most of the same properties as sum1 as they are both commutative binary operations

-- Exercise 3 N/A

-- Exercise 4 N/A

-- Exercise 5 N/A

-- Exercise 6 N/A

-- Exercise 7 N/A

-- Exercise 8 N/A

-- Exercise 9 N/A

-- Exercise 10 N/A

-- Exercise 11 N/A

-- Exercise 12 N/A

-- Exercise 13 N/A

-- Exercise 14 N/A

-- Exercise 15 N/A

-- Exercise 16 N/A

-- Exercise 17 I didn't do the Ch. 7 exercises

total
myTakeWhile : (a -> Bool) -> List a -> List a
myTakeWhile f Nil = Nil
myTakeWhile f (x :: xs) = if f x then x :: (myTakeWhile f xs) else Nil

total
myDropWhile : (a -> Bool) -> List a -> List a
myDropWhile f Nil = Nil
myDropWhile f (x :: xs) = if f x then x :: xs else myDropWhile f xs

||| Exercise 18: come up with some props for takeWhile and dropWhile
|||
exercise18 : (xs : List a) -> (f : a -> Bool) -> (myTakeWhile f xs) ++ (myDropWhile f xs) = xs
exercise18 Nil f        = ?exercise18_base_rhs
exercise18 (x :: xs') f =
    let
        ih = exercise18 xs' f
    in
        ?exercise18_ind_rhs

-- Exercise 19 N/A

-- Exercise 20 N/A

---------- Proofs ----------

ProofBasedVerification.exercise18_base_rhs = proof
  intros
  refine refl


ProofBasedVerification.exercise1c_rhs = proof
  intros
  induction xs
  compute
  refine refl
  intro x
  intro xs'
  intro ih
  compute
  let result1b = exercise1b xs' [x]
  rewrite sym result1b
  let xplusO = plusZero x
  rewrite xplusO
  let commutative = plusCommutative x (sum1 xs')
  rewrite commutative
  refine refl


ProofBasedVerification.exercise1b_rhs = proof
  intros
  induction xs
  compute
  refine refl
  intro x
  intro xs'
  intro ih
  compute
  rewrite sym ih
  let assoc = plusAssociative x (sum1 xs') (sum1 ys)
  refine assoc


ProofBasedVerification.plusCommutes_rhs = proof
  intros
  induction x
  compute
  let yPlusZero = plusZero y
  refine yPlusZero 
  intro x'
  intro ih
  compute
  rewrite sym ih
  let lemma = exercise1bLemma x' y
  refine lemma


ProofBasedVerification.exercise1bLemma_rhs = proof
  intros
  induction y
  compute
  refine refl
  intro y'
  intro ih
  compute
  rewrite sym ih
  refine refl


ProofBasedVerification.plusZero_rhs = proof
  intros
  induction x
  compute
  refine refl
  intro x'
  intro ih
  compute
  rewrite ih
  refine refl


ProofBasedVerification.exercise1a_rhs = proof
  intros
  induction n
  compute
  refine refl
  intro n1
  intro ih
  compute
  rewrite sym ih
  refine refl


