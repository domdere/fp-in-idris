module HandlingErrors

import Disjunction
import Verified

-- The Maybe Type

%elim data Option a =
        None
    |   Some a

||| simple eliminator
|||
total
option : b -> (a -> b) -> Option a -> b
option x f None     = x
option x f (Some y) = f y

||| induction principle for option, since Option isnt a recursive inductive type,
||| this is more for destruct style proofs
||| @ P A proposition on an Option
||| @ n The proof for the None case
||| @ s The proof for the Some case
total
optionInd : (P : Option a -> Type) -> (n : P None) -> (s : (x : a) -> P (Some x)) -> (ma : Option a) -> P ma
optionInd _ noneCase someCase None     = noneCase
optionInd _ noneCase someCase (Some y) = someCase y

-- Some Option based propositions, to prove some toy propositions
-- In the REPL you can try these:
-- > contains (the Nat 4) None
-- > contains (the Nat 4) (Some 3)
-- > contains (the Nat 4) (Some 4)
--
using (x : a)
    data OptionContains : a -> Option a -> Type where
        Contains : x = y -> OptionContains x (Some y)

    instance Uninhabited (OptionContains x None) where
        uninhabited (Contains p) impossible

    total
    contains : DecEq a => (x : a) -> (my : Option a) -> Dec (OptionContains x my)
    contains x None = No absurd
    contains x (Some y) with (decEq x y)
        contains x (Some x) | (Yes Refl)  = Yes (Contains Refl)
        contains x (Some y) | (No contra) = No (mkNo contra)
            where
                mkNo : {x' : a} -> {y' : a} -> ((x' = y') -> Void) -> OptionContains x' (Some y') -> Void
                mkNo f (Contains prf) = f prf


using (x : a, y : a)
    total
    destructOptionContains : OptionContains x (Some y) -> x = y
    destructOptionContains (Contains prf) = prf

total
optionContains : a -> Option a -> Type
optionContains x None     = Void
optionContains x (Some y) = (x = y) ===> OptionContains x (Some y)

total
optionMap : (a -> b) -> Option a -> Option b
optionMap _ None      = None
optionMap f (Some x)  = Some (f x)

-- A toy lemma, this result could be expressed and proven without OptionContains, but i'm curious to try it

total
mappedOptionContains : (a -> b) -> a -> Option a -> Type
mappedOptionContains f x mx = OptionContains x mx -> OptionContains (f x) (optionMap f mx)

total
optionMapLemmaHard : (f : a -> b) -> (x : a) -> (ma : Option a) -> mappedOptionContains f x ma
optionMapLemmaHard f x ma = optionInd (mappedOptionContains f x) (noneCase f x) (someCase f x) ma
    where
        noneCase : (f : a -> b) -> (x : a) -> (mappedOptionContains f x) None
        noneCase f x = absurd

        someCase : (f : a -> b) -> (x : a) -> (y : a) -> (mappedOptionContains f x) (Some y)
        someCase f x y = \(Contains prf) => ?mappedOptionSomeContainsProof


total
optionMapLemmaEasy : (f : a -> b) -> (x : a) -> (ma : Option a) -> (OptionContains x ma ===> OptionContains (f x) (optionMap f ma))
optionMapLemmaEasy f x ma = ?optionMapLemmaProof

total
optionJoin : Option (Option a) -> Option a
optionJoin None             = None
optionJoin (Some None)      = None
optionJoin (Some (Some x))  = Some x

total
optionJoinSome : (x : Option a) -> optionJoin (Some x) = x
optionJoinSome None     = ?optionJoinSomeNone
optionJoinSome (Some y) = ?optionJoinSomeProofSome

-- another toy lemma
total
joinKeepsValueLemma : (x : a) -> (mx : Option a) -> OptionContains x mx -> OptionContains x (optionJoin (Some mx))
joinKeepsValueLemma x None p                  = absurd p
joinKeepsValueLemma x (Some y) (Contains prf) = ?joinKeepsValueLemmaProof

total
optionBind' : (a -> Option b) -> Option a -> Option b
optionBind' f = optionJoin . optionMap f

total
optionBind : Option a -> (a -> Option b) -> Option b
optionBind = flip optionBind'

total
optionLift2 : (a -> b -> c) -> Option a -> Option b -> Option c
optionLift2 f ma mb = optionBind ma (\a => optionBind mb (\b => Some (f a b)))

total
optionApply : Option (a -> b) -> Option a -> Option b
optionApply = optionLift2 id

-- for ma : Option a,
-- foldOption ma : a -> a
-- If its None then it amounts to (a -> a), it can only be id
-- If its (Some thing) then we have a special `a` we can use and the possibilities expand to `const thing` as well
-- Its a pretty good instance of the pairing between id and const, they appear together pretty frequently
--
fromOption : Option a -> a -> a
fromOption None     = id
fromOption (Some x) = const x

-- fold for an Option
foldOption : (a -> b) -> b -> Option a -> b
foldOption f x ma = fromOption (optionMap f ma) x


-- Instances

instance Functor Option where
--  map : (a -> b) -> f a -> f b
    map = optionMap

instance VerifiedFunctor Option where
    mapIdentity mx    = ?mapIdentityProof

    mapComposition mx = ?mapCompositionProof

instance Applicative Option where
--  pure : a -> f a
    pure = Some

--  (<*>) : f (a -> b) -> f a -> f b
    (<*>) = optionApply

instance VerifiedApplicative Option where
    applicativePureId mx          = ?applicativePureIdProof

    applicativeComposition None v w                   = ?applicativeCompositionOptionUNone
    applicativeComposition (Some f) None w            = ?applicativeCompositionOptionVNone
    applicativeComposition (Some f) (Some g) None     = ?applicativeCompositionOptionWNone
    applicativeComposition (Some f) (Some g) (Some x) = ?applicativeCompositionOptionAllSome

    applicativeHomomorphism k x   = ?applicativeHomomorphOption

    applicativeInterchange None y     = ?applicativeInterchangeOptionNone
    applicativeInterchange (Some f) y = ?applicativeInterchangeOptionSome

instance Monad Option where
--  (>>=) : m a -> (a -> m b) -> m b
    (>>=) = optionBind

instance VerifiedMonad Option where
    monadPureIdentityL k x = ?monadPureIdentityLOption

    monadPureIdentityR mx  = ?monadPureIdentityROption

    monadBindAssociative k h None     = ?monadBindAssociativeOptionNone
    monadBindAssociative k h (Some x) = ?monadBindAssociativeOptionSome

    monadBindApplySame f None my            = ?monadBindApplySameOptionNone
    monadBindApplySame f (Some x) None      = ?monadBindApplySameOptionSomeNone
    monadBindApplySame f (Some x) (Some y)  = ?monadBindApplySameOptionSomeSome

instance Foldable Option where
--  foldr : Foldable t => (a -> b -> b) -> b -> t a -> b
    foldr f y = foldOption (\x => f x y) y

--  foldl : Foldable t => (b -> a -> b) -> b -> t a -> b
    foldl f y = foldOption (\x => f y x) y


instance Traversable Option where
--  traverse : Traversable t => Applicative f => (a -> f b) -> t a -> f (t b)
    traverse f = foldOption (\x => map Some (f x)) (pure None)

-- Exercises

-- Exercise 1 was basically to implement all of the above functions

-- Exercise 2

total
natToFloat : Nat -> Float
natToFloat Z      = 0.0
natToFloat (S n)  = 1.0 + (natToFloat n)

--natToFloatIncProof : (n : Nat) -> natToFloat (n + 1) = 1.0 + (natToFloat n)
--natToFloatIncProof n = ?natToFloatIncProof1

total
listFloatLength : List a -> Float
listFloatLength xs = foldl (+) 0.0 (map (const 1.0) xs)

total
listMean : List Float -> Option Float
listMean Nil = None
listMean xs = Some ((foldl (+) 0.0 xs)/(listFloatLength xs))


total
listVariance : List Float -> Option Float
listVariance xs = (listMean xs) >>= (\mean => listMean (map (\x => pow (x - mean) 2) xs))

-- Exercise 3

-- see optionLift2

-- Exercise 4

total
optionSequence : List (Option a) -> Option (List a)
optionSequence = foldr (\mx, mxs => (map (::) mx) <*> mxs) (pure Nil)

-- Exercise 5

total
optionTraverse : (a -> Option b) -> List a -> Option (List b)
optionTraverse f = foldr (\x, mxs => map (::) (f x) <*> mxs) (pure Nil)

total
optionSequence2 : List (Option a) -> Option (List a)
optionSequence2 = optionTraverse id

total
optionSequenceSameProof : (mxs : List (Option a)) -> optionSequence mxs = optionSequence2 mxs
optionSequenceSameProof Nil = ?optionSequenceSameProofBase
optionSequenceSameProof (x::xs) =
    let
        ih = optionSequenceSameProof xs
    in
        ?optionSequenceSameProofInd


-- The Either Data Type

%elim data Either' e a =
        Left' e
    |   Right' a

-- Exercise 7

total
eitherMap : (a -> b) -> Either' e a -> Either' e b
eitherMap _ (Left' e)  = Left' e
eitherMap f (Right' x) = Right' (f x)

total
eitherJoin : (Either' e (Either' e a)) -> Either' e a
eitherJoin (Left' e)            = Left' e
eitherJoin (Right' (Left' e))   = Left' e
eitherJoin (Right' (Right' x))  = Right' x

total
eitherBind' : (a -> Either' e b) -> Either' e a -> Either' e b
eitherBind' f = eitherJoin . eitherMap f

total
eitherBind : Either' e a -> (a -> Either' e b) -> Either' e b
eitherBind = flip eitherBind'

total
eitherLift2 : (a -> b -> c) -> Either' e a -> Either' e b -> Either' e c
eitherLift2 f mx my = eitherBind mx (\x => eitherBind my (\y => Right' (f x y)))

total
eitherApply : Either' e (a -> b) -> Either' e a -> Either' e b
eitherApply = eitherLift2 id

-- Instances

instance Functor (Either' e) where
    map = eitherMap

instance Applicative (Either' e) where
    pure  = Right'
    (<*>) = eitherApply

instance Monad (Either' e) where
    (>>=) = eitherBind


total
eitherTraverse : (a -> Either' e b) -> List a -> Either' e (List b)
eitherTraverse f = foldr (\x, mxs => map (::) (f x) <*> mxs) (pure Prelude.List.Nil)

total
eitherSequence : List (Either' e a) -> Either' e (List a)
eitherSequence = eitherTraverse id

-- Exercise 8

-- This is Either but with the ability to accumulate errors rather than dropping them all after the first
-- It only goes up to Applicative as this behaviour is no longer compatible with the Monad laws

%elim data AccValidation e a =
        Fail e
    |   Pass a

total
accMap : (a -> b) -> AccValidation e a -> AccValidation e b
accMap _ (Fail err) = Fail err
accMap f (Pass x)   = Pass (f x)

total
accApply : (Semigroup e) => AccValidation e (a -> b) -> AccValidation e a -> AccValidation e b
accApply (Fail err1) (Fail err2)  = Fail (err1 <+> err2)
accApply (Fail err) _             = Fail err
accApply _ (Fail err)             = Fail err
accApply (Pass f) (Pass x)        = Pass (f x)


-- Instances

instance Functor (AccValidation e) where
    map = accMap

instance (Semigroup e) => Applicative (AccValidation e) where
    pure = Pass
    (<*>) = accApply

---------- Proofs ----------

monadBindAssociativeOptionSome = proof
  intros
  let h1 = optionJoinSome (k x)
  rewrite sym h1
  let h2 = optionJoinSome (optionJoin (optionMap h (k x)))
  rewrite sym h2
  refine Refl


monadBindAssociativeOptionNone = proof
  intros
  refine Refl


monadPureIdentityROption = proof
  intros
  induction mx
  compute
  refine Refl
  intro x
  compute
  refine Refl


applicativeCompositionOptionAllSome = proof
  intros
  refine Refl


applicativeCompositionOptionWNone = proof
  intros
  refine Refl


applicativeCompositionOptionVNone = proof
  intros
  refine Refl


applicativeCompositionOptionUNone = proof
  intros
  refine Refl


applicativePureIdProof = proof
  intros
  induction mx
  compute
  refine Refl
  intro x
  compute
  refine Refl


applicativeHomomorphOption = proof
  intros
  refine Refl


applicativeInterchangeOptionSome = proof
  intros
  refine Refl


applicativeInterchangeOptionNone = proof
  intros
  refine Refl


mapCompositionProof = proof
  intros
  induction mx
  compute
  refine Refl
  intro x
  compute
  refine Refl


mapIdentityProof = proof
  intros
  induction mx
  compute
  refine Refl
  intro x
  compute
  refine Refl


optionMapLemmaProof = proof
  intros
  induction ma
  refine Implies
  intro h1
  compute
  let abs = the (OptionContains (f x) None) (absurd h1)
  refine abs1
  intro x'
  refine Implies 
  intro h1
  let h2 = destructOptionContains h1
  refine Contains
  rewrite h2
  refine Refl


mappedOptionSomeContainsProof = proof
  intros
  refine Contains
  rewrite prf
  refine Refl


joinKeepsValueLemmaProof = proof
  intros
  rewrite prf
  refine Contains
  refine Refl

monadBindApplySameOptionSomeNone = proof
  intros
  refine Refl


monadBindApplySameOptionSomeSome = proof
  intros
  refine Refl


monadBindApplySameOptionNone = proof
  intros
  refine Refl


monadPureIdentityLOption = proof
  intros
  rewrite sym (optionJoinSome (k x))
  refine Refl


optionJoinSomeNone = proof
  intros
  refine Refl


optionJoinSomeProofSome = proof
  intros
  refine Refl

optionSequenceSameProofBase = proof
  intros
  refine Refl

optionSequenceSameProofInd = proof
  intros
  refine Refl


