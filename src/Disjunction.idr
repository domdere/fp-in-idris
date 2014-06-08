module Disjunction

infixr 2 \/

data (\/) : (a : Type) -> (b : Type) -> Type where
    LeftP   : a -> (a \/ b)
    RightP  : b -> (a \/ b)
