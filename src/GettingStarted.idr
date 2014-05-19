module GettingStarted

fib_tail : Nat -> Nat -> Nat -> Nat
fib_tail Z _ prev       = prev
fib_tail (S Z) val _    = val
fib_tail (S n) val prev = fib_tail n (val + prev) val

fibonacci : Nat -> Nat
fibonacci n = fib_tail n 1 0

isSorted : List a -> (a -> a -> Bool) -> Bool
isSorted Nil _              = True
isSorted (_ :: Nil) _       = True
isSorted (x :: y :: xs) gt  = not (gt x y) && isSorted (y :: xs) gt


