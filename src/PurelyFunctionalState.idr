module PurelyFunctionalState

import Verified

||| The State Functor, abstracts all the combinators
||| We'll be using in this chapter
|||
data MyState s a =
    StateAction (s -> (a, s))

||| To fold MyState s a into (a, s) you need to give it an initial state
|||
runMyState : MyState s a -> s -> (a, s)
runMyState (StateAction action) = action

-- Need to define the combinators, we're in a strict environment, so you have to start from the most
-- generic one and work your way down...

bindMyState : MyState s a -> (a -> MyState s b) -> MyState s b
bindMyState mx f = StateAction stateAction
    where
        stateAction : s -> (b, s)
        stateAction st = let (x, st1) = runMyState mx st in runMyState (f x) st1

pureMyState : a -> MyState s a
pureMyState x = StateAction (\st => (x, st))

mapMyState : (a -> b) -> MyState s a -> MyState s b
mapMyState f mx = bindMyState mx (pureMyState . f)

lift2MyState : (a -> b -> c) -> MyState s a -> MyState s b -> MyState s c
lift2MyState g mx my = bindMyState mx (\x => bindMyState my (\y => pureMyState (g x y)))

applyMyState : MyState s (a -> b) -> MyState s a -> MyState s b
applyMyState = lift2MyState id

-- instances

instance Functor (MyState s) where
    map = mapMyState

instance VerifiedFunctor (MyState s) where
    mapIdentity fa = ?mapIdentityMyState_rhs

    mapComposition fa k g = ?mapCompositionMyState_rhs

instance Applicative (MyState s) where
    pure = pureMyState

    (<$>) = applyMyState

instance VerifiedApplicative (MyState s) where
    applicativePureId v = ?applicativePureIdMyState_rhs

    applicativeComposition u v w = ?applicativeCompositionMyState_rhs

    applicativeHomomorphism k x = ?applicativeHomomorphismMyState_rhs

    applicativeInterchange u y = ?applicativeInterchangeMyState_rhs

instance Monad (MyState s) where
    (>>=) = bindMyState

instance VerifiedMonad (MyState s) where
    monadPureIdentityL k x = ?monadPureIdentityLMyState_rhs

    monadPureIdentityR ma = ?monadPureIdentityLMyState_rhs

    monadBindAssociative k h ma = ?monadBindAssociativeMyState_rhs

    monadBindApplySame f mx my = ?monadBindApplySameMyState_rhs

-- exercises


