module Disjunction

infixr 2 \/

using (a : Type, b : Type, p : Type)
    ||| A disjunction of propositions,
    ||| A \\/ B implies that at least one of either
    ||| A or B is true, i.e a proof for either A
    ||| of B is a necessary and sufficient condition
    ||| to prove A \\/ B.
    |||
    data (\/) : Type -> Type -> Type where
        ||| A Proof for A is sufficient to prove A \\/ B
        LeftP   : a -> (a \/ b)

        ||| A Proof for B is sufficient to prove A \\/ B
        RightP  : b -> (a \/ b)

    ||| If A -> P and B -> P then (A \\/ B) -> P
    |||
    total
    disjunctInd : (a -> p) -> (b -> p) -> (a \/ b) -> p
    disjunctInd l r (LeftP lprf) = l lprf
    disjunctInd l r (RightP rprf) = r rprf


-- Test it with a list..

infixr 7 :::

data MyList : Type -> Type where
        Nilm  : MyList a
        (:::) : a -> MyList a -> MyList a

total
inList : a -> MyList a -> Type
inList _ Nilm       = _|_
inList x (y ::: ys) = (x = y) \/ (inList x ys)

total
foldrMyList : (a -> b -> b) -> b -> MyList a -> b
foldrMyList rec base Nilm       = base
foldrMyList rec base (x ::: xs) = rec x (foldrMyList rec base xs)

using (a: Type, xs' : MyList a)
    total
    myListInd : (p : MyList a -> Type) -> (mx : MyList a) -> p Nilm -> ((x : a) -> (xs' : MyList a) -> p xs' -> p (x ::: xs')) -> p mx
    myListInd p Nilm baseCase indCase        = baseCase
    myListInd p (x ::: xs') baseCase indCase = indCase x xs' (myListInd p xs' baseCase indCase)

total
mapMyList : (a -> b) -> MyList a -> MyList b
mapMyList f = foldrMyList (\x, ys => f x ::: ys) Nilm

appendMyList : MyList a -> MyList a -> MyList a
appendMyList xs ys = foldrMyList (\z, zs => z ::: zs) ys xs


bindMyList : MyList a -> (a -> MyList b) -> MyList b
bindMyList xs f = foldrMyList (\x, ys => appendMyList (f x) ys) Nilm xs

joinMyList : MyList (MyList a) -> MyList a
joinMyList xs = bindMyList xs id

pureMyList : a -> MyList a
pureMyList x = x ::: Nilm

lift2MyList : (a -> b -> c) -> MyList a -> MyList b -> MyList c
lift2MyList f mx my = bindMyList mx (\x => bindMyList my (\y => pureMyList (f x y)))

applyMyList : MyList (a -> b) -> MyList a -> MyList b
applyMyList = lift2MyList id

instance Functor MyList where
    map = mapMyList

instance Applicative MyList where
    pure = pureMyList
    (<$>) = applyMyList

instance Monad MyList where
    (>>=) = bindMyList

testLemma1 : (x : a) -> (y : a) -> (xs : MyList a) -> (x = y) -> inList x (y ::: xs)
testLemma1 x y xs h1 = ?testLemma1Proof

mapProofProp : (f : a -> b) -> (x : a) -> (mx : MyList a) -> Type
mapProofProp f x mx = inList x mx -> inList (f x) (mapMyList f mx)

mapProof : (f : a -> b) -> (x : a) -> (mx : MyList a) -> (mapProofProp f x) mx
mapProof f x mx = myListInd (mapProofProp f x) mx baseCase indCase
    where
        baseCase : mapProofProp f x Nilm
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


