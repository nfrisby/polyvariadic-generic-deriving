{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, Rank2Types, TypeOperators #-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
  UndecidableInstances, ScopedTypeVariables, InstanceSigs #-}

module Data.PVGD.BasicTypes where



data Proxy (t :: k) = Proxy
data KindProxy (t :: *) = KindProxy

data Nat = Z | S Nat

type family Nth (n :: Nat) (ts :: [k]) :: k

type instance Nth Z     (a ': as) = a
type instance Nth (S n) (a ': as) = Nth n as

-- needs it to be a proxy in the second case
type family CountArgs (kp :: KindProxy k) :: Nat
type instance CountArgs (kp :: KindProxy *) = Z
type instance CountArgs (kp :: KindProxy (kD -> kR)) = S (CountArgs ('KindProxy :: KindProxy kR))

type family Length (ts :: [k]) :: Nat
type instance Length '[] = Z
type instance Length (t ': ts) = S (Length ts)



-- n is always the actual length of the list
type TakeN n ts = TakeNAfterDroppingM n Z ts

-- (n + m) is always the actual length of the list
type family TakeNAfterDroppingM (n :: Nat) (m :: Nat) (ts :: [k]) :: [k]
type instance TakeNAfterDroppingM Z     m ts = '[]
type instance TakeNAfterDroppingM (S n) m ts = Nth m ts ': TakeNAfterDroppingM n (S m) ts

-- n is always the actual length of the list
class (ts ~ TakeN n ts, Lemma_NLong_inductive n) => NLong (n :: Nat) (ts :: [k])
instance (ts ~ TakeN n ts, Lemma_NLong_inductive n) => NLong n ts

-- NB I include Lemma_NLong_inductive so that NLong n ts implies NLong (S n)
-- (any ': ts)





-- can be read "ts is n long iff (any ': ts) is (S n) long", but it's more
-- involved in order to handle the (ts ~ _) wrappers

-- or consider TakeNAfterDroppingM arithmetically:
--   n + 0 = ts   <=>   n + 1 = 1 + ts
lemma_NLong_inductive_0 :: forall n ts any a. Lemma_NLong_inductive n =>
  Proxy '(n, any, ts) ->
  ((TakeNAfterDroppingM n Z ts ~ TakeNAfterDroppingM n (S Z) (any ': ts)) => a) -> a
lemma_NLong_inductive_0 _ = lemma_NLong_inductive (Proxy :: Proxy '(n, Z, any, ts))

-- can be read "ts is src is (n + m) long iff (any ': src) is (n + S m) long",
-- but it's more involved in order to handle the (ts ~ _) wrappers

-- arithmetically: n + m = src   <=>   n + (1 + m) = 1 + src
class Lemma_NLong_inductive n where
  lemma_NLong_inductive :: Proxy '(n, m, any, src) ->
    ((TakeNAfterDroppingM n m src ~ TakeNAfterDroppingM n (S m) (any ': src)) => a) -> a

instance Lemma_NLong_inductive Z where lemma_NLong_inductive _ x = x

instance Lemma_NLong_inductive n => Lemma_NLong_inductive (S n) where
  lemma_NLong_inductive p x = lemma_NLong_inductive (shift p) x where
    shift :: Proxy '(S n,   m, any, src) ->
             Proxy '(  n, S m, any, src)
    shift _ = Proxy
