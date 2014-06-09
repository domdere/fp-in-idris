module Disjunction

infixr 2 \/

||| A disjunction of propositions,
||| A \\/ B implies that at least one of either
||| A or B is true, i.e a proof for either A
||| of B is a necessary and sufficient condition
||| to prove A \\/ B.
|||
data (\/) : Type -> Type -> Type where
    ||| A Proof for A is sufficient to prove A \\/ B
    ||| @ a A proof for the Left Proposition
    |||
    LeftP   : a -> (a \/ b)

    ||| A Proof for B is sufficient to prove A \\/ B
    ||| @ b A proof for the right proposition
    |||
    RightP  : b -> (a \/ b)

||| If A -> P and B -> P then (A \\/ B) -> P
|||
total
disjunctInd : (a -> p) -> (b -> p) -> (a \/ b) -> p
disjunctInd l r (LeftP lprf) = l lprf
disjunctInd l r (RightP rprf) = r rprf


-- Test it with a list..

infixr 7 :::

total
inList : a -> List a -> Type
inList _ Nil        = _|_
inList x (y :: ys)  = (x = y) \/ (inList x ys)

using (a: Type, xs' : List a)
    total
    myListInd : (p : List a -> Type) -> (mx : List a) -> p Nil -> ((x : a) -> (xs' : List a) -> p xs' -> p (x :: xs')) -> p mx
    myListInd p Nil baseCase indCase        = baseCase
    myListInd p (x :: xs') baseCase indCase = indCase x xs' (myListInd p xs' baseCase indCase)

testLemma1 : (x : a) -> (y : a) -> (xs : List a) -> (x = y) -> inList x (y :: xs)
testLemma1 x y xs h1 = ?testLemma1Proof

mapProofProp : (f : a -> b) -> (x : a) -> (mx : List a) -> Type
mapProofProp f x mx = inList x mx -> inList (f x) (map f mx)

mapProof : (f : a -> b) -> (x : a) -> (mx : List a) -> (mapProofProp f x) mx
mapProof f x mx = myListInd (mapProofProp f x) mx baseCase indCase
    where
        baseCase : mapProofProp f x Nil
        baseCase = \h1 => ?baseCaseProof


        --indCase x' xs' ih = \h1 => ?indCaseProof
        indCase x' xs' ih = disjunctInd headEq xInTail
            where
                headEq h1   = ?headEqProof
                xInTail h1  = ?xInTailProof

---------- Proofs ----------

headEqProof = proof
  intros
  refine LeftP
  rewrite h1
  refine refl


baseCaseProof = proof
  intros
  trivial


testLemma1Proof = proof
  intros
  refine LeftP
  trivial


