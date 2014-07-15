module Parsing

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

data ParseErrorType =
        Unknown
    |   Failed

data ParseError = ParseErrorC Position ParseErrorType

total
errorPosition : ParseError -> Position
errorPosition (ParseErrorC p t) = p

total
positionLine : Position -> Line
positionLine (Pos l c) = l

total
positionCol : Position -> Col
positionCol (Pos l c) = c

total
comparePositions : Position -> Position -> Bool
comparePositions p1 p2 = if (fromLine . positionLine) p1 == (fromLine . positionLine) p2 then (fromCol . positionCol) p1 > (fromCol . positionCol) p2 else (fromLine . positionLine) p1 > (fromLine . positionLine) p2

data ParseState = ParseStateC Position (List Char)

total
parsePosition : ParseState -> Position
parsePosition (ParseStateC p str) = p

total
parseString : ParseState -> List Char
parseString (ParseStateC p str) = str

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
unParser : Parser a -> StateT ParseState (Either ParseError) a
unParser (ParserC sma) = sma

total
pgets : (ParseState -> a) -> Parser a
pgets f = ParserC (gets f)

pget : Parser ParseState
pget = pgets id

pput : ParseState -> Parser ()
pput st = ParserC (put st)

instance Functor Parser where
    map f (ParserC x) = ParserC (map f x)

instance Applicative Parser where
    pure = ParserC . pure

    (ParserC mf) <$> (ParserC mx) = ParserC (mf <$> mx)

instance Monad Parser where
    (ParserC mx) >>= f = ParserC (mx >>= (unParser . f))

||| The empty Parser is the one that always fails.
||| That way empty <|> p = p for all parsers p
||| and p <|> empty = p for all parsers p
|||
zeroParser : Parser a
zeroParser = (ParserC . StateTC) (\st => (Left (ParseErrorC (parsePosition st) Unknown)))

on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)

||| Choose the error that indicates parsing got the furthest...
||| (Unless the type is Unknown, in which case just return the other one)
|||
mergeError : ParseError -> ParseError -> ParseError
mergeError (ParseErrorC p Unknown) x  = x
mergeError x (ParseErrorC p Unknown)  = x
mergeError x y                        = if ((comparePositions `on` errorPosition) x y) then x else y

total
orEither : (a -> a -> a) -> Either a b -> Either a b -> Either a b
orEither f (Right x) y          = Right x
orEither f (Left e1) (Right y)  = Right y
orEither f (Left e1) (Left e2)  = Left (f e1 e2)

orParser : Parser a -> Parser a -> Parser a
orParser (ParserC smx) (ParserC smy) = (ParserC . StateTC) (\st => orEither mergeError (runStateT smx st) (runStateT smy st))

instance Alternative Parser where
    empty = zeroParser
    (<|>) = orParser

total
runParser : Parser a -> List Char -> Either ParseError a
runParser (ParserC sma) str = map prodSecond (runStateT sma (ParseStateC (Pos (LineC 1) (ColC 0)) str))

-- helpers

total
repeatN : Nat -> a -> List a
repeatN Z x     = Nil
repeatN (S n) x = x :: (repeatN n x)

total
safeHead : List a -> Maybe a
safeHead Nil        = Nothing
safeHead (x :: xs)  = Just x

total
safeTail : List a -> Maybe (List a)
safeTail Nil        = Nothing
safeTail (x :: xs)  = Just xs

mkTuple : a -> b -> (a, b)
mkTuple x y = (x, y)

parsedChar : Position -> (Char, List Char) -> Parser Char
parsedChar pos (c, cs) = do
    pput (ParseStateC pos cs)
    pure c

-- Simple Foundational Parsers

total
char : Char -> Parser Char
char c = do
    pos <- pgets parsePosition
    let incPos = Pos (positionLine pos) (incrementCol 1 (positionCol pos))
    str <- pgets parseString
    maybe ((ParserC . liftStateT) (Left (ParseErrorC pos Failed))) (\(c', cs) => if c == c' then parsedChar incPos (c', cs) else ((ParserC . liftStateT) (Left (ParseErrorC pos Failed)))) ((mkTuple `map` (safeHead str)) <$> (safeTail str))



-- Other Combinators

total
listOfN : Nat -> Parser a -> Parser (List a)
listOfN n px = sequence (repeatN n px)

-- Derived Parsers

total
parseStr : List Char -> Parser (List Char)
parseStr cs = sequence (map char cs)
