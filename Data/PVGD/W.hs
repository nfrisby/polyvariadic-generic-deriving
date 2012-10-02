{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds #-}

{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

module Data.PVGD.W where

import Data.PVGD.BasicTypes



-- | The W data family encapsulates type-level polyvariadism. It effectively
-- uncurries t.
data family W (t :: k) :: [*] -> *
newtype instance W (t :: *) ps = W0 t deriving (Show, Eq)

newtype instance W (t :: * -> *) ps = W1 (t (Nth Z ps))
deriving instance Show (t (Nth Z ps)) => Show (W (t :: * -> *) ps)
deriving instance Eq   (t (Nth Z ps)) => Eq   (W (t :: * -> *) ps)

newtype instance W (t :: * -> * -> *) ps = W2 (t (Nth (S Z) ps) (Nth Z ps))
deriving instance Show (t (Nth (S Z) ps) (Nth Z ps)) => Show (W (t :: * -> * -> *) ps)
deriving instance Eq   (t (Nth (S Z) ps) (Nth Z ps)) => Eq   (W (t :: * -> * -> *) ps)

newtype instance W (t :: * -> * -> * -> *) ps = W3 (t (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps))
deriving instance Show (t (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps)) => Show (W (t :: * -> * -> * -> *) ps)
deriving instance Eq   (t (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps)) => Eq   (W (t :: * -> * -> * -> *) ps)

-- NB could support any number of *uniformly kinded* arguments
--data family W (t :: k) :: [k1] -> *

{- NB I want to use these types, but then the Generic instances become
  ill-typed with rather error messages that seem unfounded to me.

unW0 :: W t '[] -> t
unW1 :: W t '[a] -> t a
unW2 :: W t '[b, a] -> t b a
unW3 :: W t '[c, b, a] -> t c b a

These types would incur type errors in Generic instance like

    Could not deduce (ps ~ (':) * a0 ('[] *))
    from the context (NLong
                        * (CountArgs (* -> *) ('KindProxy (* -> *))) ps)

But why can't it? The arguments are defined enough to expand the NLong
constraint. But for some reason, GHC 7.6 won't. -}

unW0 (W0 x) = x
unW1 (W1 x) = x
unW2 (W2 x) = x
unW3 (W3 x) = x

asW0 f = unW0 . f . W0
asW1 f = unW1 . f . W1
asW2 f = unW2 . f . W2
asW3 f = unW3 . f . W3

onW0 f = W0 . f . unW0
onW1 f = W1 . f . unW1
onW2 f = W2 . f . unW2
onW3 f = W3 . f . unW3

