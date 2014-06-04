module HandlingErrors

-- The Maybe Type

data Option a =
        None
    |   Some a

total
optionMap : (a -> b) -> Option a -> Option b
optionMap _ None      = None
optionMap f (Some x)  = Some (f x)

total
optionJoin : Option (Option a) -> Option a
optionJoin None             = None
optionJoin (Some None)      = None
optionJoin (Some (Some x))  = Some x

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

-- Instances

instance Functor Option where
    map = optionMap

instance Applicative Option where
    pure = Some
    (<$>) = optionApply

instance Monad Option where
    (>>=) = optionBind

-- Exercises

-- Exercise 1 was basically to implement all of the above functions

-- Exercise 2

total
natToFloat : Nat -> Float
natToFloat O      = 0.0
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
optionSequence = foldr (\mx, mxs => (map (::) mx) <$> mxs) (pure Nil)

-- Exercise 5

total
optionTraverse : (a -> Option b) -> List a -> Option (List b)
optionTraverse f = foldr (\x, mxs => map (::) (f x) <$> mxs) (pure Nil)

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

data Either' e a =
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
    (<$>) = eitherApply

instance Monad (Either' e) where
    (>>=) = eitherBind


total
eitherTraverse : (a -> Either' e b) -> List a -> Either' e (List b)
eitherTraverse f = foldr (\x, mxs => map (::) (f x) <$> mxs) (pure Prelude.List.Nil)

total
eitherSequence : List (Either' e a) -> Either' e (List a)
eitherSequence = eitherTraverse id

-- Exercise 8

data AccValidation e a =
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

instance Applicative (AccValidation e) where
    pure 

---------- Proofs ----------

HandlingErrors.optionSequenceSameProofBase = proof
  intros
  refine refl


HandlingErrors.optionSequenceSameProofInd = proof
  intros
  refine refl


