module Parsing

data ParseError = Failed

data Line = LineC Int

data Col = ColC Int

data Position = Pos Line Col

data ParseState = ParseStateC Position String

data Prod : Type -> Type -> Type where
    ProdC : s -> a -> Prod s a

instance Functor (Prod s) where
    map f (ProdC st x) = ProdC st (f x)

||| State Monad Transformer.
|||
||| Adds a state aspect to a monad.
|||
||| Prod gets used here instead of (,) cos then the type inferencer
||| requires m : (Type, Type) -> Type instead of Type -> Type.
|||
data StateT : (Type -> (Type -> Type) -> Type -> Type) where
    StateTC : (s -> m (Prod s a)) -> StateT s m a

liftStateT : (Functor m) => m a -> StateT s m a
liftStateT mx = StateTC (\st => map (\x => ProdC st x) mx)

runStateT : StateT s m a -> s -> m (Prod s a)
runStateT (StateTC f) = f

instance (Functor m) => Functor (StateT s m) where
    map f (StateTC g) = StateTC (\st => map (map f) (g st))

pureStateT : (Applicative f) => a -> StateT s f a
pureStateT x = liftStateT (pure x)

bindStateT : (Monad m) => StateT s m a -> (a -> StateT s m b) -> StateT s m b
bindStateT sma f = StateTC (\st => (runStateT sma st) >>= (\(ProdC st' x) => runStateT (f x) st'))

lift2StateT : (Monad m) => (a -> b -> c) -> StateT s m a -> StateT s m b -> StateT s m c
lift2StateT g mx my = bindStateT mx (\x => bindStateT my (\y => pureStateT (g x y)))

instance (Monad m) => Applicative (StateT s m) where
    pure = pureStateT
    (<$>) = lift2StateT id

instance (Monad m) => Monad (StateT s m) where
    (>>=) = bindStateT

data Parser a = ParserC (StateT ParseState (Either ParseError) a)
