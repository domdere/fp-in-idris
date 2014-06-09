module Implication

infixr 2 ==>

||| Implication
||| An Implication relation A -> B
||| Is equivalent to a function that takes a proof
||| of A to a proof of B.
||| This type is essentially a newtype for
||| the (->) operator
|||
data (==>) : Type -> Type -> Type where
    ||| A function that takes a proof of A
    ||| to a proof of B
    |||
    Implies : (a -> b) -> (a ==> b)

infixr 2 <=>

||| iff
||| if A ==> B and B ==> A then we have (A <=> B) or B iff A
|||
data (<=>) : Type -> Type -> Type where
    Iff : (a ==> b) -> (b ==> a) -> (a <=> b)

||| ==> functions

||| All impliclations (A ==> B) have a function (A -> B) on proofs
|||
implicationFunction : (a ==> b) -> a -> b
implicationFunction (Implies f) = f

implicationTransitivity : (a ==> b) -> (b ==> c) -> (a ==> c)
implicationTransitivity (Implies f) (Implies g) = Implies (g . f)

||| <=> functions

||| A <=> B is equivalent to B <=> A
flipIff : (a <=> b) -> (b <=> a)
flipIff (Iff x y) = Iff y x

