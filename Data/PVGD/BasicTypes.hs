{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, TypeOperators #-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances #-}

module Data.PVGD.BasicTypes where



data Proxy (t :: k) = Proxy
data KindProxy (t :: *) = KindProxy

data Nat = Z | S Nat

-- needs it to be a proxy in the second case
type family CountArgs (kp :: KindProxy k) :: Nat
type instance CountArgs (kp :: KindProxy *) = Z
type instance CountArgs (kp :: KindProxy (kD -> kR)) = S (CountArgs ('KindProxy :: KindProxy kR))

type family Length (ts :: [k]) :: Nat
type instance Length '[] = Z
type instance Length (t ': ts) = S (Length ts)

type family Nth (n :: Nat) (ts :: [k]) :: k
type instance Nth Z     (a ': as) = a
type instance Nth (S n) (a ': as) = Nth n as

type Head ts = Nth Z ts

type family Tail (ts :: [k]) :: [k]
type instance Tail (t ': ts) = ts

-- functionality of Take, but non-strict in the input list
type family LazyTake (n :: Nat) (ts :: [k]) :: [k]
type instance LazyTake Z     ts = '[]
type instance LazyTake (S n) ts = Head ts ': LazyTake n (Tail ts)

-- n is always the actual length of the list
class (ts ~ LazyTake n ts) => NLong (n :: Nat) (ts :: [k])
instance (ts ~ LazyTake n ts) => NLong n ts
