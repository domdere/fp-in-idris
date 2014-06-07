module FunctionalDataStructures

-- | exercise 1
--
total
someFunc : List Int -> Int
someFunc (x :: 2 :: 4 :: _) = x
someFunc Nil = 42
someFunc (x :: y :: 3 :: 4 :: _) = x + y
someFunc (h :: t) = h + (sum t)
someFunc _ = 101

-- | exercise 2
--
total
safeTail : List a -> Maybe (List a)
safeTail Nil       = Nothing
safeTail (_ :: xs) = Just xs

-- | exercise 3
--
total
setHead : a -> List a -> Maybe (List a)
setHead x xs = ((::) x) `map` (safeTail xs)

-- | exercise 4
--
total
myDrop : Nat -> List a -> List a
myDrop _ Nil            = Nil
myDrop Z xs             = xs
myDrop (S n) (x :: xs)  = myDrop n xs

-- | exercise 5
--
total
myDropWhile : (a -> Bool) -> List a -> List a
myDropWhile _ Nil = Nil
myDropWhile f (x :: xs) = case f x of
    True  => x :: xs
    False => myDropWhile f xs

-- | exercise 6
--
total
safeInit : List a -> Maybe (List a)
safeInit Nil = Nothing
safeInit (_ :: Nil) = Just Nil
safeInit (x :: xs) = (x ::) `map` (safeInit xs)

-- | exercise 7
-- not with eager evaluation
--
total
eagerFoldR : (a -> b -> b) -> b -> List a -> b
eagerFoldR _ z Nil = z
eagerFoldR f z (x :: xs) = f x (eagerFoldR f z xs)

--total
--lazyFoldR : (a -> b -> b) -> Lazy b -> List a -> Lazy b
--lazyFoldR _ z Nil = z
--lazyFoldR f z (x :: xs) = Delay (f x (eagerFoldR f z xs))

-- Exercise 8
--
total
foldNilConIsIdentity : (xs : List a) -> eagerFoldR (::) Nil xs = xs
foldNilConIsIdentity Nil = ?baseCase
foldNilConIsIdentity (x :: xs) =
    let
        ih = foldNilConIsIdentity xs
    in
        ?inductiveCase

-- Exercise 9
total
myLength : List a -> Nat
myLength = eagerFoldR (+) Z . (map (const (S Z)))

-- Exercise 10
total
eagerFoldL : (b -> a -> b) -> b -> List a -> b
eagerFoldL _ x Nil = x
eagerFoldL f x (y :: ys) = eagerFoldL f (f x y) ys

-- Exercise 11
total
mySum2 : (Num a) => List a -> a
mySum2 = eagerFoldL (+) 0

total
myProduct : (Num a) => List a -> a
myProduct = eagerFoldL (*) 1

total
myLength2 : List a -> Nat
myLength2 = eagerFoldL (+) Z . map (const (S Z))

-- Exercise 12

total
myReverse : List a -> List a
myReverse = eagerFoldL (flip (::)) Nil


-- Exercise 13
total
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

total
myAppend : List a -> List a -> List a
myAppend xs ys = eagerFoldR (::) ys xs

-- Exercise 15
total
myJoin : List (List a) -> List a
myJoin = eagerFoldR myAppend Nil

total
myMap : (a -> b) -> List a -> List b
myMap f = eagerFoldR (\x, ys => (f x) :: ys) Nil

-- Exercise 16
total
plus1ToAll : List Nat -> List Nat
plus1ToAll = myMap (+1)

-- Exercise 17
total
toStringAll : (Show a) => List a -> List String
toStringAll = myMap show

-- Exercise 18 see myMap

-- Exercise 19
total
myFilter : (a -> Bool) -> List a -> List a
myFilter _ Nil = Nil
myFilter f (x :: xs) = case f x of
    True  => x :: myFilter f xs
    False => myFilter f xs

-- Exercise 20
total
myFlatMap : List a -> (a -> List b) -> List b
myFlatMap xs f = (myJoin . myMap f) xs

-- Exercise 21
total
myFilter2 : (a -> Bool) -> List a -> List a
myFilter2 f xs = myFlatMap xs (\x => if f x then [x] else Nil)

-- Exercise 22 and 23

total
zipWith : (a -> b -> c) -> List a -> List b -> List c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil
zipWith f (x :: xs) (y :: ys) = (f x y) :: zipWith f xs ys

total
addElements : (Num a) => List a -> List a -> List a
addElements = zipWith (+)

-- Exercise 24

-- Returns True if the first argument is a prefix of the second
total
isPrefix : (Eq a) => List a -> List a -> Bool
isPrefix Nil _ = True
isPrefix _ Nil = False
isPrefix (x::xs) (y::ys) = x == y && (isPrefix xs ys)

class (Eq a) => VerifiedEq a where
    total eqReflexive : (x : a) -> (x == x) = True
    total eqTransitive : (x : a) -> (y : a) -> (z : a) -> ((x == y) && (y == z)) = True -> (x == z) = True

total
appPrefixProof : (VerifiedEq a) => (xs : List a) -> (ys : List a) -> isPrefix xs (xs ++ ys) = True
appPrefixProof Nil ys = ?appPrefixProofBase
appPrefixProof (x :: xs) ys =
    let
        ih = appPrefixProof xs ys
    in
        ?appPrefixProofInd

-- appSuffixPrefixProof : (VerifiedEq a) => (xs : List a) -> (zs : List a) -> Exists (List a) (\Pa => (ys : List a) -> isPrefix xs zs = True -> zs = xs ++ ys)
-- appSuffixPrefixProof Nil zs = ?appSuffixPrefixProofBase
-- appSuffixPrefixProof (c::cs) (z::zs) =
--     let
--         ih = appPrefixProof cs zs

-- Returns True if the first substring given is a subsequence of the second
total
isSubsequence : (Eq a) => List a -> List a -> Bool
isSubsequence sub Nil = False
isSubsequence sub (x::xs) = isPrefix sub (x::xs) || isSubsequence sub xs

data Tree a =
        Leaf a
    |   Branch (Tree a) (Tree a)

tree1 : Tree Nat
tree1 = Branch (Branch (Leaf 1) (Leaf 2)) (Leaf 3)

-- Exercise 25

total
on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on op f x y = op (f x) (f y)

total
treeSize : Tree a -> Nat
treeSize (Leaf _)             = 1
treeSize (Branch left right)  = 1 + (((+) `on` treeSize) left right)

-- Exercise 26
total
treeMax : (Ord a) => Tree a -> a
treeMax (Leaf x)            = x
treeMax (Branch left right) = (max `on` treeMax) left right

-- Exercise 27
total
treeDepth : Tree a -> Nat
treeDepth (Leaf _)            = 0
treeDepth (Branch left right) = 1 + ((max `on` treeDepth) left right)

-- Exercise 28
total
treeMap : (a -> b) -> Tree a -> Tree b
treeMap f (Leaf x) = Leaf (f x)
treeMap f (Branch left right) = (Branch `on` (treeMap f)) left right

total
treeMapIdProof : (t : Tree a) -> treeMap id t = t
treeMapIdProof (Leaf x)             = ?treeMapIdProofBase
treeMapIdProof (Branch left right)  =
    let
        ihLeft  = treeMapIdProof left
    in let
        ihRight = treeMapIdProof right
    in
        ?treeMapIdProofInd

total
treeMapCompositionProof : (f : b -> c) -> (g : a -> b) -> (t : Tree a) -> treeMap (f . g) t = (treeMap f . treeMap g) t
treeMapCompositionProof f g (Leaf x)            = ?treeMapCompositionProofBase
treeMapCompositionProof f g (Branch left right) =
    let
        ihLeft  = treeMapCompositionProof f g left
    in let
        ihRight = treeMapCompositionProof f g right
    in
        ?treeMapCompositionProofInd

total
foldTree : (b -> b -> b) -> (a -> b) -> Tree a -> b
foldTree _ f (Leaf x)             = f x
foldTree f g (Branch left right)  = (f `on` (foldTree f g)) left right

total
foldTreeIdProof : (t : Tree a) -> foldTree Branch Leaf t = t
foldTreeIdProof (Leaf x) = ?foldTreeIdProofBase
foldTreeIdProof (Branch left right) =
    let
        ihLeft = foldTreeIdProof left
    in let
        ihRight = foldTreeIdProof right
    in
        ?foldTreeIdProofInd

total
treeToList : Tree a -> List a
treeToList = foldTree (++) (\y => [y])

total
foldSize : Tree a -> Nat
foldSize = foldTree (\x, y => 1 + x + y) (const 1)

total
foldSizeIsSizeProof : (t : Tree a) -> foldSize t = treeSize t
foldSizeIsSizeProof (Leaf x)            = ?foldSizeIsSizeProofBase
foldSizeIsSizeProof (Branch left right) =
    let
        ihLeft = foldSizeIsSizeProof left
    in let
        ihRight = foldSizeIsSizeProof right
    in
        ?foldSizeIsSizeProofInd

total
foldMax : (Ord a) => Tree a -> a
foldMax = foldTree max id

total
foldMaxIsMaxProof : (Ord a) => (t : Tree a) -> foldMax t = treeMax t
foldMaxIsMaxProof (Leaf x)            = ?foldMaxIsMaxProofBase
foldMaxIsMaxProof (Branch left right) =
    let
        ihLeft = foldMaxIsMaxProof left
    in let
        ihRight = foldMaxIsMaxProof right
    in
        ?foldMaxIsMaxProofInd

total
mapByFold : (a -> b) -> Tree a -> Tree b
mapByFold f = foldTree Branch (Leaf . f)

total
mapByFoldIsMapProof : (f : a -> b) -> (t : Tree a) -> mapByFold f t = treeMap f t
mapByFoldIsMapProof f (Leaf x)            = ?mapByFoldIsMapProofBase
mapByFoldIsMapProof f (Branch left right) =
    let
        ihLeft = mapByFoldIsMapProof f left
    in let
        ihRight = mapByFoldIsMapProof f right
    in
        ?mapByFoldIsMapProofInd

---------- Proofs ----------

mapByFoldIsMapProofBase = proof
  intros
  refine refl


mapByFoldIsMapProofInd = proof
  intros
  rewrite ihLeft
  rewrite ihRight
  refine refl


foldMaxIsMaxProofBase = proof
  intros
  refine refl


foldMaxIsMaxProofInd = proof
  intros
  rewrite ihLeft
  rewrite ihRight
  refine refl


foldSizeIsSizeProofBase = proof
  intros
  refine refl


foldSizeIsSizeProofInd = proof
  intros
  rewrite ihLeft
  rewrite ihRight
  refine refl


foldTreeIdProofBase = proof
  intros
  refine refl


foldTreeIdProofInd = proof
  intros
  rewrite sym ihLeft
  rewrite sym ihRight
  refine refl


treeMapCompositionProofInd = proof
  intros
  rewrite sym ihLeft
  rewrite sym ihRight
  refine refl


treeMapCompositionProofBase = proof
  intros
  refine refl


treeMapIdProofBase = proof
  intros
  refine refl


treeMapIdProofInd = proof
  intros
  rewrite sym ihLeft
  rewrite sym ihRight
  refine refl


appPrefixProofInd = proof
  intros
  rewrite sym ih
  rewrite sym (eqReflexive x)
  compute
  refine refl


appPrefixProofBase = proof
  intros
  refine refl


baseCase = proof
  intros
  refine refl


inductiveCase = proof
  intros
  rewrite ih
  refine refl


