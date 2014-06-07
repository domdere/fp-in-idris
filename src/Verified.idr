module Verified


||| Verified Functors
||| @ f the action of the functor on objects
class Functor f => VerifiedFunctor (f : Type -> Type) where
    ||| map must map the identity function on `a` to the identity function on `f a`
    total mapIdentity : (fa : f a) -> map id fa = fa

    ||| map must preserve function composition: map k . map g = map (k . g)
    total mapComposition : (fa : f a) -> (k : b -> c) -> (g : a -> b) -> (map k . map g) fa = map (k . g) fa

||| An Applicative that is verified to satisfy the Applicative laws.
class Applicative f => VerifiedApplicative (f : Type -> Type) where
    total applicativePureId       : (v : f a) -> (pure id) <$> v = v
    total applicativeComposition  : (u : f (b -> c)) -> (v : f (a -> b)) -> (w : f a) -> pure (.) <$> u <$> v <$> w = u <$> (v <$> w)
    total applicativeHomomorphism : (k : a -> b) -> (x : a) -> pure k <$> pure x = pure (k x)
    total applicativeInterchange  : (u : f (a -> b)) -> (y : a) -> (u <$> (pure y)) = (pure (flip apply y) <$> u)

infixr 1 >=>

||| Kleisli Composition
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> a -> m c
(>=>) f g x = f x >>= g

liftM2 : Monad m => (a -> b -> c) -> m a -> m b -> m c
liftM2 f mx my = mx >>= (\x => my >>= (\y => pure (f x y)))

class Monad m => VerifiedMonad (m : Type -> Type) where
    total monadPureIdentityL : (k : a -> m b) -> (x : a) -> pure x >>= k = k x
    total monadPureIdentityR : (ma : m a) -> ma >>= pure = ma
    total monadBindAssociative : (k : a -> m b) -> (h : b -> m c) -> (ma : m a) -> ma >>= (k >=> h) = (ma >>= k) >>= h

    ||| Lifting a curried function using the Monad bind should be consistent with the Applicative behaviour
    total monadBindApplySame : (f : a -> b -> c) -> (mx : m a) -> (my : m b) -> liftM2 f mx my = liftA2 f mx my

