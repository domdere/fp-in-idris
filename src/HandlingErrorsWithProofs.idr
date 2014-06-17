module HandlingErrorsWithProofs

import Disjunction

||| A look at combining proofs with programs,
||| If an operation fails, it returns a proof of
||| of a proposition for the input, that results in the
||| failure.
||| Otherwise it returns the desired value
|||
%elim data OptionProof failProp a =
        Fail failProp
    |   Success ((~) failProp) a

||| With this approach, if you have a proof that failure
||| should not be possible then you can extract the result out,
||| this is not a partial function (compare to fromJust for Maybe in Haskell)
|||
total
fromSuccess : OptionProof a b -> ((~) a) -> b
fromSuccess (Fail prf) (Not notPrf) = absurd (notPrf prf)
fromSuccess (Success nPrf x) prf    = x

||| negation is a bit of a pain in Constructionist logic
||| so here is another function similar to fromSuccess
|||
total
fromSuccessNeg : OptionProof ((~) a) b -> a -> b
fromSuccessNeg (Fail (Not notPrf)) prf  = absurd (notPrf prf)
fromSuccessNeg (Success nPrf x) prf     = x

||| Convert a function with failure into a total function on the subset
||| of the input that can be proven to succeed with that function.
|||
total
limitDomain : (a -> OptionProof b c) -> a -> ((~) b) -> c
limitDomain f x prf = fromSuccess (f x) prf

||| Again, the negated counterpart (to limitDomain).
|||
total
limitDomainNeg : (a -> OptionProof ((~) b) c) -> a -> b -> c
limitDomainNeg f x prf = fromSuccessNeg (f x) prf

||| map works just as you would expect...
||| (OptionProof b) is a functor
|||
total
mapOptionProof : (a -> b) -> OptionProof c a -> OptionProof c b
mapOptionProof f (Fail prf)       = Fail prf
mapOptionProof f (Success prf x)  = Success prf (f x)

||| a pure OptionProof is one that cannot fail (because we definitely have an a).
||| Hence _|_ shows up...
|||
total
pureOptionProof : a -> OptionProof _|_ a
pureOptionProof = Success (Not id)

total
successPrf : ((~) p) -> ((~) q) -> (p \/ (((~) p) /\ q)) -> _|_
successPrf (Not notP) (Not notQ) (LeftP x)              = notP x
successPrf (Not notP) (Not notQ) (RightP (Split np y))  = notQ y

||| for bind, we dont have a proper monadic behaviour, see the type of this function.
||| The functor type no longer stays the same.
||| if the input has failed if p, and the function f will fail if b,
||| then the final result will fail if (p \/ ((~p) /\ q)).
|||
||| This combinator will hence let you build up proofs.
|||
total
bindOptionProof : OptionProof p a -> (a -> OptionProof q b) -> OptionProof (p \/ (((~) p) /\ q)) b
bindOptionProof (Fail prf) f  = Fail (LeftP prf)
bindOptionProof (Success nprf x) f = case f x of
    Fail prf          => (Fail (RightP (Split nprf prf)))
    Success nprf2 prf => Success (Not (successPrf nprf nprf2)) prf

data Empty : List a -> Type where
    isNil : Empty (the (List a) Nil)

instance Uninhabited (Empty (x :: xs)) where
    uninhabited Nil impossible

emptyToEq : {xs : List a} -> (xs = the (List a) Nil) -> Empty xs
emptyToEq xs refl = isNil

-- examples
total
safeHead : (DecEq a) => (xs : List a) -> OptionProof (xs = (the (List a) Nil)) a
safeHead Nil = Fail refl
safeHead (x :: xs') = Success (absurd . emptyToEq) x
