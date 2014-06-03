module FunctionalDataStructures

-- | exercise 1
--
someFunc : List Int -> Int
someFunc (x :: 2 :: 4 :: _) = x
someFunc Nil = 42
someFunc (x :: y :: 3 :: 4 :: _) = x + y
someFunc (h :: t) = h + (sum t)
someFunc _ = 101

-- | exercise 2
--
safeTail : List a -> Maybe (List a)
safeTail Nil       = Nothing
safeTail (_ :: xs) = Just xs

-- | exercise 3
--
setHead : a -> List a -> Maybe (List a)
setHead x xs = ((::) x) `map` (safeTail xs)

-- | exercise 4
--
myDrop : Nat -> List a -> List a
myDrop _ Nil            = Nil
myDrop Z xs             = xs
myDrop (S n) (x :: xs)  = myDrop n xs

-- | exercise 5
--
myDropWhile : (a -> Bool) -> List a -> List a
myDropWhile _ Nil = Nil
myDropWhile f (x :: xs) = case f x of
    True  => x :: xs
    False => myDropWhile f xs

-- | exercise 6
--
safeInit : List a -> Maybe (List a)
safeInit Nil = Nothing
safeInit (_ :: Nil) = Just Nil
safeInit (x :: xs) = (x ::) `map` (safeInit xs)

-- | exercise 7
-- not with eager evaluation
--
eagerFoldR : (a -> b -> b) -> b -> List a -> b
eagerFoldR _ z Nil = z
eagerFoldR f z (x :: xs) = f x (eagerFoldR f z xs)

--lazyFoldR : (a -> b -> b) -> Lazy b -> List a -> Lazy b
--lazyFoldR _ z Nil = z
--lazyFoldR f z (x :: xs) = Delay (f x (eagerFoldR f z xs))

-- Exercise 8
--
foldNilConIsIdentity : (xs : List a) -> eagerFoldR (::) Nil xs = xs
foldNilConIsIdentity Nil = ?baseCase
foldNilConIsIdentity (x :: xs) =
    let
        ih = foldNilConIsIdentity xs
    in
        ?inductiveCase

-- Exercise 9
myLength : List a -> Nat
myLength = eagerFoldR (+) Z . (map (const (S Z)))

-- Exercise 10
eagerFoldL : (b -> a -> b) -> b -> List a -> b
eagerFoldL _ x Nil = x
eagerFoldL f x (y :: ys) = eagerFoldL f (f x y) ys

-- Exercise 11
mySum2 : (Num a) => List a -> a
mySum2 = eagerFoldL (+) 0

myProduct : (Num a) => List a -> a
myProduct = eagerFoldL (*) 1

myLength2 : List a -> Nat
myLength2 = eagerFoldL (+) Z . map (const (S Z))

-- Exercise 12

myReverse : List a -> List a
myReverse = eagerFoldL (flip (::)) Nil


-- Exercise 13
foldLeftFromFoldRight : (b -> a -> b) -> b -> List a -> b
foldLeftFromFoldRight f x xs = (eagerFoldR (\y, g, b => g (f b y)) id xs) x

--foldLeftFromFoldRightEquiv : (f : (b -> a -> b)) -> (x : b) -> (xs : List a) -> eagerFoldL f x xs = foldLeftFromFoldRight f x xs
--foldLeftFromFoldRightEquiv _ _ Nil = ?foldLeftFromFoldRightEquivBase
--foldLeftFromFoldRightEquiv f x (y :: ys) =
--    let
--        ih = foldLeftFromFoldRightEquiv f (f x y) ys
--    in
--        ?foldLeftFromFoldRightEquivInductive

-- Exercise 14

myAppend : List a -> List a -> List a
myAppend xs ys = eagerFoldR (::) ys xs

-- Exercise 15
myJoin : List (List a) -> List a
myJoin = eagerFoldR myAppend Nil

myMap : (a -> b) -> List a -> List b
myMap f = eagerFoldR (\x, ys => (f x) :: ys) Nil

-- Exercise 16
plus1ToAll : List Nat -> List Nat
plus1ToAll = myMap (+1)

-- Exercise 17
toStringAll : (Show a) => List a -> List String
toStringAll = myMap show

-- Exercise 18 see myMap

-- Exercise 19
myFilter : (a -> Bool) -> List a -> List a
myFilter _ Nil = Nil
myFilter f (x :: xs) = case f x of
    True  => x :: myFilter f xs
    False => myFilter f xs

-- Exercise 20
myFlatMap : List a -> (a -> List b) -> List b
myFlatMap xs f = (myJoin . myMap f) xs

-- Exercise 21
myFilter2 : (a -> Bool) -> List a -> List a
myFilter2 f xs = myFlatMap xs (\x => if f x then [x] else Nil)

-- Exercise 22 and 23

zipWith : (a -> b -> c) -> List a -> List b -> List c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil
zipWith f (x :: xs) (y :: ys) = (f x y) :: zipWith f xs ys

addElements : (Num a) => List a -> List a -> List a
addElements = zipWith (+)

-- Exercise 24

-- Returns True if the first argument is a prefix of the second
isPrefix : (Eq a) => List a -> List a -> Bool
isPrefix Nil _ = True
isPrefix _ Nil = False
isPrefix (x::xs) (y::ys) = x == y && (isPrefix xs ys)

app_prefix_proof : (Eq a) => (xs : List a) -> (ys : List a) -> isPrefix xs (xs ++ ys) = True
app_prefix_proof Nil ys = ?app_prefix_proof_base
app_prefix_proof (x :: xs) ys =
    let
        ih = app_prefix_proof xs ys
    in
        ?app_prefix_proof_ind


---------- Proofs ----------

baseCase = proof
  intros
  refine refl


inductiveCase = proof
  intros
  rewrite ih
  refine refl


