module Parsing

data ParseError = Failed

data Line = LineC Nat

total
incrementLine : Nat -> Line -> Line
incrementLine n (LineC x) = LineC (n + x)

total
fromLine : Line -> Nat
fromLine (LineC x) = x

data Col = ColC Nat

total
incrementCol : Nat -> Col -> Col
incrementCol n (ColC x) = ColC (n + x)

total
fromCol : Col -> Nat
fromCol (ColC x) = x

data Position = Pos Line Col

total
positionLine : Position -> Line
positionLine (Pos l c) = l

total
positionCol : Position -> Col
positionCol (Pos l c) = c

data ParseState = ParseStateC Position String

data Prod : Type -> Type -> Type where
    ProdC : s -> a -> Prod s a

total
prodSecond : Prod s a -> a
prodSecond (ProdC st x) = x

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

total
liftStateT : (Functor m) => m a -> StateT s m a
liftStateT mx = StateTC (\st => map (\x => ProdC st x) mx)

total
gets : (Monad m) => (s -> a) -> StateT s m a
gets f = StateTC (\st => pure (ProdC st (f st)))

total
get : (Monad m) => StateT s m s
get = gets id

total
put : (Monad m) => s -> StateT s m ()
put st = StateTC (\st' => pure (ProdC st ()))

total
runStateT : StateT s m a -> s -> m (Prod s a)
runStateT (StateTC f) = f

instance (Functor m) => Functor (StateT s m) where
    map f (StateTC g) = StateTC (\st => map (map f) (g st))

total
pureStateT : (Applicative f) => a -> StateT s f a
pureStateT x = liftStateT (pure x)

total
bindStateT : (Monad m) => StateT s m a -> (a -> StateT s m b) -> StateT s m b
bindStateT sma f = StateTC (\st => (runStateT sma st) >>= (\(ProdC st' x) => runStateT (f x) st'))

total
lift2StateT : (Monad m) => (a -> b -> c) -> StateT s m a -> StateT s m b -> StateT s m c
lift2StateT g mx my = bindStateT mx (\x => bindStateT my (\y => pureStateT (g x y)))

instance (Monad m) => Applicative (StateT s m) where
    pure = pureStateT
    (<$>) = lift2StateT id

instance (Monad m) => Monad (StateT s m) where
    (>>=) = bindStateT

data Parser a = ParserC (StateT ParseState (Either ParseError) a)

total
runParser : Parser a -> String -> Either ParseError a
runParser (ParserC sma) str = map prodSecond (runStateT sma (ParseStateC (Pos (LineC 1) (ColC 0)) str))
