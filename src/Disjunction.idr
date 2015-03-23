module Disjunction

import public Implication

infixr 2 \/

||| A disjunction of propositions,
||| A \\/ B implies that at least one of either
||| A or B is true, i.e a proof for either A
||| of B is a necessary and sufficient condition
||| to prove A \\/ B.
|||
||| A Proof for A is sufficient to prove A \\/ B (LeftP)
|||
||| A Proof for B is also sufficient to prove A \\/ B (RightP)
|||
%elim data (\/) a b =
        LeftP a
    |   RightP b

infixr 3 /\

||| A conjunction of propositions,
||| A /\\ B implies that both A and B are true,
||| So proofs for both cases are required to prove the
||| the case for A /\\ B.
|||
%elim data (/\) a b =
    ||| Proofs for both A and B are required to prove A /\\ B
    ||| @ a A proof for A
    ||| @ b A proof for B
    |||
    Split a b

||| If A -> P and B -> P then (A \\/ B) -> P
|||
total
disjunctInd : ((a ===> p) /\ (b ===> p)) -> (a \/ b) ===> p
disjunctInd (Split (Implies l) (Implies r)) = Implies (go l r)
where
    go : (a -> p) -> (b -> p) -> (a \/ b) -> p
    go l' r' (LeftP lprf) = l' lprf
    go l' r' (RightP rprf) = r' rprf

total
modusPonens : ((a ===> b) /\ a) -> b
modusPonens (Split (Implies f) x) = f x

-- Test it with a list..

infixr 7 :::

total
inList : a -> List a -> Type
inList _ Nil        = Void
inList x (y :: ys)  = (x = y) \/ (inList x ys)

total
testLemma1 : (x : a) -> (y : a) -> (xs : List a) -> (x = y) -> inList x (y :: xs)
testLemma1 x y xs h1 = ?testLemma1Proof

total
mapPreservesInListLemma : (f : a -> b) -> (x : a) -> (mx : List a) -> (inList x mx ===> inList (f x) (map f mx))
mapPreservesInListLemma f x mx = ?mapProof

---------- Proofs ----------

mapProof = proof
  intros
  induction mx
  refine Implies
  compute
  intro h1
  refine h1
  intro x'
  intro xs'
  intro ih
  compute
  refine Implies
  intro h1
  induction h1
  intro h1Left
  refine LeftP
  rewrite h1Left
  refine Refl
  intro h1Right
  refine RightP
  let ih1 = modusPonens (Split ih h1Right)
  refine ih1


testLemma1Proof = proof
  intros
  refine LeftP
  trivial
