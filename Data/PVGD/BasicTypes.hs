{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, Rank2Types, TypeOperators #-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
  UndecidableInstances, ScopedTypeVariables #-}

module Data.PVGD.BasicTypes where



data Proxy (t :: k) = Proxy
data KindProxy (t :: *) = KindProxy

data Nat = Z | S Nat

type family Nth (n :: Nat) (ts :: [k]) :: k

type instance Nth Z     (a ': as) = a
type instance Nth (S n) (a ': as) = Nth n as

-- NB needs it to be a proxy in the second case
type family CountArgs (kp :: KindProxy k) :: Nat
type instance CountArgs (kp :: KindProxy *) = Z
type instance CountArgs (kp :: KindProxy (kD -> kR)) = S (CountArgs ('KindProxy :: KindProxy kR))

type family Length (ts :: [k]) :: Nat
type instance Length '[] = Z
type instance Length (t ': ts) = S (Length ts)

class NLong (n :: Nat) (ts :: [k])

instance ('[] ~ ps) => NLong Z ps
instance ((t ': pstail) ~ ps, NLong n pstail) => NLong (S n) ps
-- NB switch to this instance to see what goes wrong without NLong
-- instance NLong n ts
