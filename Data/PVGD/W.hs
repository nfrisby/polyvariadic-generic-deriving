{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds #-}

{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances,
  FlexibleInstances #-}

module Data.PVGD.W where

import Data.PVGD.BasicTypes


-- TODO, now that NLong is so strongly defined, should I make these instances
-- GADT-like wrt to ps?


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

{- TODO now that NLong is so strongly defined, should I tighten th types of
    unWN?

unW0 :: W t '[] -> t
unW1 :: W t '[a] -> t a
unW2 :: W t '[a, b] -> t b a
unW3 :: W t '[a, b, c] -> t c b a

-- it would at least require adding NLong constraints to the methods of WIso
-- below

-}


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




-- cf W
type family Apps (t :: k) (ps :: [*]) :: *
type instance Apps (t :: *) ps = t
type instance Apps (t :: * -> *) ps = t (Nth Z ps)
type instance Apps (t :: * -> * -> *) ps = t (Nth (S Z) ps) (Nth Z ps)
type instance Apps (t :: * -> * -> * -> *) ps
  = t (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps)

class WIso (t :: k) where
  toApps :: W t ps -> Apps t ps
  frApps :: Apps t ps -> W t ps

instance WIso (t :: *) where toApps = unW0 ; frApps = W0
instance WIso (t :: * -> *) where toApps = unW1 ; frApps = W1
instance WIso (t :: * -> * -> *) where toApps = unW2 ; frApps = W2
instance WIso (t :: * -> * -> * -> *) where toApps = unW3 ; frApps = W3








newtype instance W (t :: * -> * -> * -> * -> *) ps
  = W4 (t (Nth (S (S (S Z))) ps) (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps))
deriving instance Show (t (Nth (S (S (S Z))) ps) (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps)) =>
  Show (W (t :: * -> * -> * -> * -> *) ps)
deriving instance Eq   (t (Nth (S (S (S Z))) ps) (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps)) =>
  Eq   (W (t :: * -> * -> * -> * -> *) ps)

unW4 (W4 x) = x

asW4 f = unW4 . f . W4

onW4 f = W4 . f . unW4

type instance Apps (t :: * -> * -> * -> * -> *) ps
  = t (Nth (S (S (S Z))) ps) (Nth (S (S Z)) ps) (Nth (S Z) ps) (Nth Z ps)

instance WIso (t :: * -> * -> * -> * -> *) where toApps = unW4 ; frApps = W4


-- NB @asW@ is kind of useless, since @t@ is not determined by the argument
-- @Apps t ps@.  All of the available @W t@s are polymorphic in @t@, and only
-- require @Generic t@ -- in other words, I need Apps to be considered
-- injective wrt @t@.

-- asW :: WIso t => (W t ps -> W t ps') -> Apps t ps -> Apps t ps'
-- asW f = toApps . f . frApps
