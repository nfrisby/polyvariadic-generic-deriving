{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, TypeOperators, Rank2Types #-}

{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE FlexibleContexts, UndecidableInstances, GADTs #-}

{-# LANGUAGE ScopedTypeVariables #-}

{-

This module defines the generic view.

The T type represents type applications with any number of arguments. It
trivially includes occurrences of non-parameters. I'm not yet distinguishing
recursive from non-recursive type occurrences, but I think that'd be
admissible.

We unfortunately cannot express the relationship between k and the length of ps
in the Rep family and Generic class. This would inhibit type inference, were it
not for the pervasive NLong constraints on the Generic methods. Because they're
on those methods, they unfortunately need to be on all classes' methods. But it
otherwise appears from the user's perspective as a simulation of a promoted
Vec.

In the Data.Yoko.BasicTypes file, the instances of NLong can be replaced with
the informationless totally parametric instance in order to see how NLong's
role in type inference. When NLong is thusly made trivial, this module no
longer type checks. The errors are variations on this theme:

  *Data.PVGD.View> -- with the meaningless NLong instance:
  *Data.PVGD.View> :t asW1 $ \x -> frRep (toRep x)
  asW1 $ \x -> frRep (toRep x)
    :: (Generic (* -> *) t1, Generic (* -> *) t2,
        Rep (* -> *) t1 ~ Rep (* -> *) t2) =>
       t2 t -> t1 t

  *Data.PVGD.View> -- with the meaningless NLong instance:
  *Data.PVGD.View> :t asW1 $ \x -> frRep (toRep x)
  asW1 $ \x -> frRep (toRep x)
    :: (Generic (* -> *) t, Generic (* -> *) t1,
        Rep (* -> *) t ~ Rep (* -> *) t1) =>
       t1 (Nth * 'Z ps) -> t (Nth * 'Z ps)

The key point is that the length of ps cannot be inferred from the kind of t
without the NLong constraints. If Vec could be promoted, this would be built
into the types of toRep and frRep.

Even with the NLong constraints, I cannot use more strongly typed versions of
unW0, unW1, unW2, ... GHC 7.6 is for some reason not reducing the NLong
constraints when type-checking the Generic instances. Similarly, the W
instances cannot be GADT-like wrt to the ps parameter. Thus, I use the Nth
family to access the type list "non strictly".

-}

module Data.PVGD.View where

import Data.PVGD.BasicTypes
import Data.PVGD.W



-- NB ideally Rep and Generic would use a promoted Vec GADT in order to relate
-- k and the length of the promoted list; in the meantime, we recover useful
-- type inference via the NLong constraints
type family Rep (t :: k) :: [*] -> *

class Generic (t :: k) where
  toRep :: NLong (CountArgs ('KindProxy :: KindProxy k)) ps => W   t ps -> Rep t ps
  frRep :: NLong (CountArgs ('KindProxy :: KindProxy k)) ps => Rep t ps -> W   t ps

-- the normal sum-of-products representation types
data Void (ps :: [*])
instance Eq (Void ps) where (==) = error "Eq @Void"

infixr 5 :+:
data (l :+: r) (ps :: [*]) = L (l ps) | R (r ps) deriving Eq
foldPlus f _ (L x) = f x
foldPlus _ g (R x) = g x

data U (ps :: [*]) = U deriving Eq

infixr 6 :*:
data (l :*: r) (ps :: [*]) = l ps :*: r ps deriving Eq

-- the representation for supporting many parameters
newtype Par (n :: Nat) (ps :: [*]) = Par (Nth n ps)
deriving instance Eq (Nth n ps) => Eq (Par n ps)
unPar (Par x) = x





--------------------
-- representation type for type applications

type family Eval (r :: [*] -> *) (ps :: [*]) :: *

type instance Eval (Par n) ps = Nth n ps
type instance Eval (T t rs) ps = Apps t (MapEval rs ps)

-- psuedo: @map (\x -> Eval x ps)@
type family MapEval (fs :: [[*] -> *]) (arg :: [*]) :: [*]
type instance MapEval '[]       arg = '[]
type instance MapEval (f ': fs) arg = Eval f arg ': MapEval fs arg

-- lemma for CovariantR at T
class Lemma_NLongLengthMapEval (fs :: [[*] -> *]) where
  lemma_NLongLengthMapEval :: Proxy fs -> Proxy arg ->
    (NLong (Length fs) (MapEval fs arg) => a) -> a

instance Lemma_NLongLengthMapEval '[] where lemma_NLongLengthMapEval _ _ x = x
instance Lemma_NLongLengthMapEval ts => Lemma_NLongLengthMapEval (t ': ts) where
  lemma_NLongLengthMapEval _ pArg x = lemma_NLongLengthMapEval (Proxy :: Proxy ts) pArg x



-- NB @rs@ is a (reversed) type list of representations, the use of @MapEval@ is a
-- promotion of @map (\x -> Eval x ps)@; recall that W essentially uncurries t
newtype T t argReps ps = T (W t (MapEval argReps ps))
deriving instance Eq (W t (MapEval argReps ps)) => Eq (T t argReps ps)
deriving instance Show (W t (MapEval argReps ps)) => Show (T t argReps ps)

unT (T x) = x





{- NB deprecated -- I don't think it should add the parameter itself)
newtype Idxd (idx :: [*] -> *) (r :: [*] -> *) (ps :: [*])
  = Idxd (r (Eval idx ps ': ps))

unIdxd (Idxd x) = x
-}

data Idxd :: Nat -> ([*] -> *) -> ([*] -> *) -> [*] -> * where
  Idxd :: (Nth n ps ~ Eval idx ps) => r ps -> Idxd n idx r ps

unIdxd (Idxd x) = x


{- TODO

Maybe generic definitions over these could be shaped like generic definitions
over T if we had a generic representation of Constraints.

data QE :: (* -> Constraint) -> ([*] -> *) -> [*] -> * where
  QE :: c a => r (a ': ps) -> QE c r ps

newtype QU (c :: * -> Constraint) (r :: [*] -> *) (ps :: [*])
  = QU (forall a. c a => r (a ': ps))
-}


newtype QU (r :: [*] -> *) (ps :: [*]) = QU (forall a. r (a ': ps))

unQU (QU x) = x
