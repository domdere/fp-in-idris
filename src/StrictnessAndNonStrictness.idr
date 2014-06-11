module StrictnessAndNonStrictness

import Disjunction
import Implication

infixr 7 ::

||| The "Stream" in the text is really only a Lazy List (I.e its still potentially finite)
||| The Idris Stream is for infinite data only
|||
data LazyList a =
        Nil
    |   (::) a (Lazy' LazyCodata (LazyList a))

||| An infinite Stream of ones
|||
ones : LazyList Int
ones = 1 :: ones

||| A finite Int Stream
|||
oneTwoThree : LazyList Int
oneTwoThree = 1 :: 2 :: 3 :: Nil

||| Exercise 1 - Write a function to conver a LazyList to a List
|||
foldLazyList : (a -> Lazy' LazyCodata b -> b) -> Lazy' LazyCodata b -> LazyList a -> b
foldLazyList f y Nil = y
foldLazyList f y (x :: xs) = f x (Delay (foldLazyList f y xs))

||| Exercise 1 - Write a function to convert a Lazy List into a List
|||
unLazyList : LazyList a -> List a
unLazyList = foldLazyList (\y, b => y :: b) Nil

||| Exercise 1 - Write a function to convert a Lazy List into a List
||| see unLazyList
|||
exercise1 : LazyList a -> List a
exercise1 = unLazyList

||| Exercise 2 - Write a function to take the first n elements of a LazyList
|||
lazyTake : Nat -> LazyList a -> LazyList a
lazyTake Z xs             = Nil
lazyTake n Nil            = Nil
lazyTake (S n) (x :: xs)  = x :: lazyTake n xs

||| Exercise 2a - Write a function to take the first n elements of a LazyList
||| see lazyTake
|||
exercise2a : Nat -> LazyList a -> LazyList a
exercise2a = lazyTake

||| Exercise 2b - Write a function that drops n elements of the LazyList and returns the rest
|||
lazyDrop : Nat -> LazyList a -> LazyList a
lazyDrop Z xs             = xs
lazyDrop n Nil            = Nil
lazyDrop (S n) (x :: xs)  = lazyDrop n xs

||| Exercise 2b - Write a function that drops n elements of the LazyList and returns the rest
||| see lazyDrop
|||
exercise2b : Nat -> LazyList a -> LazyList a
exercise2b = lazyDrop

strictTake : Nat -> LazyList a -> List a
strictTake n xs = unLazyList (lazyTake n xs)

||| append two LazyLists
appendLazy : LazyList a -> Lazy' LazyCodata (LazyList a) -> LazyList a
appendLazy Nil ys       = ys
appendLazy (x :: xs) ys = x :: (appendLazy xs ys)

||| WIP This doesnt seem to work in a lazy fashion...
|||
cycle : LazyList a -> LazyList a
cycle xs = appendLazy xs (cycle xs)


||| Coinductive Proof
|||
-- appendTakeDrop
--     :   (n : Nat)
--     ->  (x : a)
--     ->  (xs : LazyList a)
--     ->  (appendLazy (lazyTake n xs) (lazyDrop n xs)) = xs
--     ->  (appendLazy (lazyTake (S n) (x :: xs)) (lazyDrop (S n) (x :: xs))) = (x :: xs)
-- appendTakeDrop n x xs p = ?appendTakeDrop_rhs

||| Exercise 3 - Write a function takeWhile that takes elements from the list while the predicate is satisfied
|||
lazyTakeWhile : (a -> Bool) -> LazyList a -> LazyList a
lazyTakeWhile p Nil       = Nil
lazyTakeWhile p (x :: xs) = if p x then x :: (lazyTakeWhile p xs) else Nil

||| Exercise 3 - Write a function takeWhile that takes elements from the list while the predicate is satisfied
||| see lazyTakeWhile
|||
exercise3 : (a -> Bool) -> LazyList a -> LazyList a
exercise3 = lazyTakeWhile

repeat : a -> LazyList a
repeat x = x :: (repeat x)

mapLazy : (a -> b) -> LazyList a -> LazyList b
mapLazy f = foldLazyList (\x, xs => f x :: xs) Nil

||| Exercise 4 - Write a function forAll that takes a stream and returns a Bool
||| indicating whether or not the predicate holds for all elements in the stream
|||
forAll : (a -> Bool) -> LazyList a -> Bool
forAll p = foldLazyList (\x, b => p x && b) True

||| Exercise 4 - Write a function forAll that takes a stream and returns a Bool
||| see forAll
|||
exercise4 : (a -> Bool) -> LazyList a -> Bool
exercise4 = forAll

||| Exercise 5 - Write takeWhile using a foldRight (Already have, see `lazytakeWhile`)
|||
exercise5 : (a -> Bool) -> LazyList a -> LazyList a
exercise5 = lazyTakeWhile

-- Exercise 6 - Write a function headMaybe that uses a foldRight to return the head of the list

lazyFirst : a -> Lazy' LazyEval  b -> a
lazyFirst x y = x

||| Exercise 6 - Write a function headMaybe that uses a foldRight to return the head of the list
|||
headMaybe : LazyList a -> Maybe a
headMaybe = foldLazyList (\x, b => lazyFirst (Just x) b) Nothing

||| Exercise 6 - Write a function headMaybe that uses a foldRight to return the head of the list
||| see headMaybe
|||
exercise6 : LazyList a -> Maybe a
exercise6 = headMaybe

||| Exercise 7a - implement map with foldRight
||| see mapLazy
|||
exercise7a : (a -> b) -> LazyList a -> LazyList b
exercise7a = mapLazy

||| Exercise 7b - Implement filter with a foldRight
|||
filterLazy : (a -> Bool) -> LazyList a -> LazyList a
filterLazy p = foldLazyList (lazyCondCons p) Nil
    where
        lazyCondCons : (a -> Bool) -> a -> Lazy' LazyCodata (LazyList a) -> LazyList a
        lazyCondCons p x xs = if p x then x :: xs else xs

||| Exercise 7b - Implement filter with a foldRight
||| see filterLazy
|||
exercise7b : (a -> Bool) -> LazyList a -> LazyList a
exercise7b = filterLazy

||| Exercise 7c - Implement append with a foldRight, should be lazy in its arguments..
||| see appendLazy
|||
exercise7c : LazyList a -> Lazy' LazyCodata (LazyList a) -> LazyList a
exercise7c = appendLazy

||| Test example for Exercise 7d
|||
oneTwoThrees : LazyList (LazyList Int)
oneTwoThrees = repeat oneTwoThree

||| Exercise 7d - Implement bind with a foldRight
|||
bindLazy : LazyList a -> (a -> LazyList b) -> LazyList b
bindLazy xs f = foldLazyList (\x, ys => appendLazy (f x) ys) Nil xs

||| Exercise 7d - Implement bind with a foldRight
||| see bindLazy
|||
exercise7d : LazyList a -> (a -> LazyList b) -> LazyList b
exercise7d = bindLazy

||| Exercise 8 - Write a function repeat that given an element, returns an
||| infinite LazyList containing that element.
|||
||| See repeat
|||
exercise8 : a -> LazyList a
exercise8 = repeat

||| Exercise 9 - Write a function fromLazy.
||| @ n Returns a list of Nats that counts up from n
|||
fromLazy : (n : Nat) -> LazyList Nat
fromLazy n = n :: fromLazy (S n)

||| Exercise 9 - Write a function fromLazy.
||| See fromLazy
||| @ n Returns a list of Nats that counts up from n
|||
exercise9 : (n : Nat) -> LazyList Nat
exercise9 = fromLazy

||| Exercise 10 - Write a function fibs that returns an infinite stream of fibonacci numbers.
|||
fibLazy : LazyList Nat
fibLazy = go 0 1
    where
        go : Nat -> Nat -> LazyList Nat
        go x y = x :: (go y (x + y))

||| Exercise 10 - Write a function fibs that returns an infinite stream of fibonacci numbers.
||| See fibLazy
|||
exercise10 : LazyList Nat
exercise10 = fibLazy

||| Exercise 11 - Write unfold
|||
||| @ f If f returns Nothing then it signifies the end of the stream, otherwise it gives the
|||     next value and the new generator state
||| @ init The initial generator state.
|||
unfoldLazy : (f : s -> Maybe (a, s)) -> (init : s) -> LazyList a
unfoldLazy f init = case f init of
    Nothing => Nil
    Just (x, newState) => x :: unfoldLazy f newState

||| Exercise 11 - Write unfold.
|||
||| See unfoldLazy
|||
||| @ f If f returns Nothing then it signifies the end of the stream, otherwise it gives the
|||     next value and the new generator state
||| @ init The initial generator state.
|||
exercise11 : (f : s -> Maybe (a, s)) -> (init : s) -> LazyList a
exercise11 = unfoldLazy

||| Exercise 12a - redo fibLazy using unfoldLazy
|||
exercise12a : LazyList Nat
exercise12a = unfoldLazy go (0, 1)
    where
        go : (Nat, Nat) -> Maybe (Nat, (Nat, Nat))
        go (x, y) = Just (x, (y, x + y))

||| Exercise 12b - redo fromLazy with unfoldLazy
|||
exercise12b : Nat -> LazyList Nat
exercise12b n = unfoldLazy go n
    where
        go : Nat -> Maybe (Nat, Nat)
        go n = Just (n, S n)

||| Exercise 12c - redo repeat with unfoldLazy
|||
exercise12c : a -> LazyList a
exercise12c x = unfoldLazy go x
    where
        go : a -> Maybe (a, a)
        go x = Just (x, x)

||| Exercise 13a - Implement mapLazy with unfoldLazy
|||
mapUnfold : (a -> b) -> LazyList a -> LazyList b
mapUnfold f = unfoldLazy go
    where
        go Nil        = Nothing
        go (x :: xs)  = Just (f x, xs)

||| Exercise 13a - Implement mapLazy with unfoldLazy.
|||
||| See mapUnfold
|||
exercise13a : (a -> b) -> LazyList a -> LazyList b
exercise13a = mapUnfold

||| Exercise 13b - Implement lazyTake with unfoldLazy
|||
takeUnfold : Nat -> LazyList a -> LazyList a
takeUnfold n xs = unfoldLazy go (n, xs)
    where
        go : (Nat, LazyList a) -> Maybe (a, (Nat, LazyList a))
        go (Z, xs)          = Nothing
        go (n, Nil)         = Nothing
        go (S n, (x :: xs)) = Just (x, (n, xs))

||| Exercise 13b - Implement lazyTake with unfoldLazy.
|||
||| See takeUnfold
|||
exercise13b : Nat -> LazyList a -> LazyList a
exercise13b = takeUnfold

||| Exercise 13c - Implement takeWhile with unfoldLazy
|||
takeWhileUnfold : (a -> Bool) -> LazyList a -> LazyList a
takeWhileUnfold p = unfoldLazy go
    where
        go : LazyList a -> Maybe (a, LazyList a)
        go Nil = Nothing
        go (x :: xs) = if p x then Just (x, xs) else Nothing

||| Exercise 13c - Implement takeWhile with unfoldLazy.
|||
||| See takeWhileUnfold
|||
exercise13c : (a -> Bool) -> LazyList a -> LazyList a
exercise13c = takeWhileUnfold

||| Exercise 13d - Implement zipWith with unfoldLazy
|||
zipWithUnfold : (a -> b -> c) -> LazyList a -> LazyList b -> LazyList c
zipWithUnfold f xs ys = unfoldLazy (go f) (xs, ys)
    where
        go : (a -> b -> c) -> (LazyList a, LazyList b) -> Maybe (c, (LazyList a, LazyList b))
        go g (Nil, ys)                  = Nothing
        go g (xs, Nil)                  = Nothing
        go f' ((x :: xs'), (y :: ys'))  = Just (f' x y, (xs', ys'))

||| Exercise 13d - Implement zipWith with unfoldLazy.
|||
||| See zipWithUnfold.
|||
exercise13d : (a -> b -> c) -> LazyList a -> LazyList b -> LazyList c
exercise13d = zipWithUnfold

||| Exercise 13e - Implement zipAll with unfoldLazy.
|||
zipAllUnfold : LazyList a -> LazyList b -> LazyList (Maybe a, Maybe b)
zipAllUnfold xs ys = unfoldLazy go (xs, ys)
    where
        go : (LazyList a, LazyList b) -> Maybe ((Maybe a, Maybe b), (LazyList a, LazyList b))
        go ((x' :: xs'), (y' :: ys')) = Just ((Just x', Just y'), (xs', ys'))
        go (Nil, (y' :: ys'))         = Just ((Nothing, Just y'), (Nil, ys'))
        go ((x' :: xs'), Nil)         = Just ((Just x', Nothing), (xs', Nil))
        go (Nil, Nil)                 = Nothing

||| Exercise 13e - Implement zipAll with unfoldLazy.
|||
||| See zipAllUnfold
|||
exercise13e : LazyList a -> LazyList b -> LazyList (Maybe a, Maybe b)
exercise13e = zipAllUnfold

||| Exercise 14 - Implement startsWith using functions you've written
||| It checks if one LazyList is a prefix of another.
|||
startsWithLazy : Eq a => LazyList a -> LazyList a -> Bool
startsWithLazy xs ys = foldLazyList check False (zipAllUnfold xs ys)
    where
        check : Eq a => (Maybe a, Maybe a) -> Lazy' LazyCodata Bool -> Bool
        check (Nothing, Just y) acc = True
        check (mx, Nothing) acc     = False
        check (Just x, Just y) acc  = (x == y) && acc

||| Exercise 14 - Implement startsWith using functions you've written
||| It checks if one LazyList is a prefix of another.
|||
||| See startsWithLazy
|||
exercise14 : Eq a => LazyList a -> LazyList a -> Bool
exercise14 = startsWithLazy

||| Exercise 15 - Implement tailsLazy with unfoldLazy
||| e.g given (1 :: 2 :: 3 :: Nil) it should return
||| (1 :: 2 :: 3 :: Nil) :: (2 :: 3 :: Nil) :: (3 :: Nil) :: Nil :: Nil
|||
tailsLazy : LazyList a -> LazyList (LazyList a)
tailsLazy xs = unfoldLazy go (Just xs)
    where
        go : Maybe (LazyList a) -> Maybe (LazyList a, Maybe (LazyList a))
        go Nothing          = Nothing
        go (Just Nil)       = Just (Nil, Nothing)
        go (Just (x :: xs)) = Just (x :: xs, Just xs)

||| Exercise 15 - Implement tailsLazy with unfoldLazy
||| e.g given (1 :: 2 :: 3 :: Nil) it should return
||| (1 :: 2 :: 3 :: Nil) :: (2 :: 3 :: Nil) :: (3 :: Nil) :: Nil :: Nil.
|||
||| See tailsLazy
exercise15 : LazyList a -> LazyList (LazyList a)
exercise15 = tailsLazy

||| Exercise  16 - Generalise tailsLazy to the function scanRightLazy
||| which is like a foldLazyList that returns a LazyList of intermediate results
|||
scanRightLazy : (a -> Lazy' LazyCodata b -> b) -> Lazy' LazyCodata b -> LazyList a -> LazyList b
scanRightLazy f acc = ?scanRightLazy_rhs



---------- Proofs ----------


