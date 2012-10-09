{-# LANGUAGE TypeFamilies, LambdaCase, PolyKinds, TypeOperators, DataKinds,
  FlexibleContexts, MultiParamTypeClasses, GADTs, FlexibleInstances,
  ScopedTypeVariables, UndecidableInstances, InstanceSigs, DefaultSignatures #-}

module Data.PVGD.Enumerate where

import Data.PVGD.BasicTypes
import Data.PVGD.W
import Data.PVGD.View



interleave x y = diag [x, y]

-- plucked from Luke Palmer's Control.Monad.Omega
diag :: [[a]] -> [a]
diag = concat . stripe
    where
    stripe [] = []
    stripe ([]:xss) = stripe xss
    stripe ((x:xs):xss) = [x] : zipCons xs (stripe xss)

    zipCons [] ys = ys
    zipCons xs [] = map (:[]) xs
    zipCons (x:xs) (y:ys) = (x:y) : zipCons xs ys





-- the enumerations being extended
data family Enums (n :: Nat) :: [*] -> *
data instance Enums Z ps = Enums
-- use a GADT so that the provided functions can determine @ps@ and @ps'@
infixl 5 :::
data instance Enums (S n) (ps :: [*]) :: * where
  (:::) :: (ps ~ (a ': as)) => Enums n as -> [a] -> Enums (S n) ps






class Enumerate (t :: k) where
  enum :: NLong (CountArgs ('KindProxy :: KindProxy k)) ps =>
          Enums (CountArgs ('KindProxy :: KindProxy k)) ps -> [W t ps]

  default enum :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
                   Generic t, EnumerateR (Rep t) (CountArgs ('KindProxy :: KindProxy k))) =>
                  Enums (CountArgs ('KindProxy :: KindProxy k)) ps -> [W (t :: k) ps]
  enum = gen_enum

class EnumerateR (t :: [*] -> *) (n :: Nat) where
  enumR :: NLong n ps => Enums n ps -> [t ps]

gen_enum :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
             Generic t, EnumerateR (Rep t) (CountArgs ('KindProxy :: KindProxy k))) =>
             Enums (CountArgs ('KindProxy :: KindProxy k)) ps -> [W (t :: k) ps]
gen_enum = map frRep . enumR

instance (EnumerateR l n, EnumerateR r n) => EnumerateR (l :+: r) n where
  enumR enums = map L (enumR enums) `interleave` map R (enumR enums)
instance EnumerateR Void n where enumR _ = []

instance (EnumerateR l n, EnumerateR r n) => EnumerateR (l :*: r) n where
  enumR enums = diag $
                flip map (enumR enums) $ \l ->
                flip map (enumR enums) $ \r ->
                  l :*: r
instance EnumerateR U n where enumR _ = [U]



instance NthEnumR m n => EnumerateR (Par m) n where
  enumR = map Par . nthEnumR (Proxy :: Proxy m)

class NthEnumR m n where nthEnumR :: Proxy m -> Enums n ps -> [Nth m ps]

instance (n ~ S n') => NthEnumR Z n where
  nthEnumR _ (_ ::: as) = as
instance (n ~ S n', NthEnumR m n') => NthEnumR (S m) n where
  nthEnumR _ (enums ::: _) = nthEnumR (Proxy :: Proxy m) enums



instance (Lemma_NLongLengthMapEval argReps,
          Enumerate t, NewEnums argReps n,
          CountArgs ('KindProxy :: KindProxy k) ~ Length argReps) =>
  EnumerateR (T (t :: k) argReps) n where
  enumR :: forall (ps :: [*]). NLong n ps => Enums n ps -> [T t argReps ps]
  enumR = lemma_NLongLengthMapEval (Proxy :: Proxy argReps) (Proxy :: Proxy ps) $
          map T . enum . newEnums (Proxy :: Proxy argReps)

class NewEnums (argReps :: [[*] -> *]) (n :: Nat) where
  newEnums :: NLong n ps => Proxy argReps -> Enums n ps -> Enums (Length argReps) (MapEval argReps ps)

instance NewEnums '[] n where newEnums _ _ = Enums
instance (EnumerateR argRep n, NewEnums argReps n, Field argRep) =>
  NewEnums (argRep ': argReps) n where
  newEnums :: forall (ps :: [*]). NLong n ps =>
              Proxy (argRep ': argReps) -> Enums n ps ->
              Enums (Length (argRep ': argReps)) (MapEval (argRep ': argReps) ps)
  newEnums _ enums = newEnums (Proxy :: Proxy argReps) enums :::
                     map (frField . (id :: argRep ps -> argRep ps)) (enumR enums)



-- we can only enumerate existentials that do not occur as data
instance EnumerateR r (S n) => EnumerateR (QE r) n where
  enumR :: forall (ps :: [*]). NLong n ps => Enums n ps -> [QE r ps]
  enumR enums = map QE $ enumR (enums ::: [])



{-

instance EnumerateR r n => EnumerateR (Idxd which idx r) n where
  enumR enums = map Idxd $ enumR enums

Data/PVGD/Enumerate.hs:123:21:
    Could not deduce (Eval idx ps ~ Nth * which ps)
    from the context (EnumerateR r n)
      bound by the instance declaration
      at Data/PVGD/Enumerate.hs:122:10-58
    or from (NLong * n ps)
      bound by the type signature for
                 enumR :: NLong * n ps => Enums n ps -> [Idxd which idx r ps]
      at Data/PVGD/Enumerate.hs:123:3-38

TODO: perhaps Idxd needs to introduce the existential type (instead of letting
QE do it) in order for this to work?

-}
