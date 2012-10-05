{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, Rank2Types, TypeOperators #-}

{-# LANGUAGE DefaultSignatures, InstanceSigs #-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
  UndecidableInstances, GADTs, ScopedTypeVariables #-}

module Data.PVGD.Covariant where

import Data.PVGD.BasicTypes
import Data.PVGD.W
import Data.PVGD.View



--------------------
-- covariant mapping with a generic definition

class Covariant (t :: k) where
  covmap :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
             NLong (CountArgs ('KindProxy :: KindProxy k)) ps'
            ) => Maps (CountArgs ('KindProxy :: KindProxy k)) ps ps' ->
                 W t ps -> W t ps'

  default covmap :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
                     NLong (CountArgs ('KindProxy :: KindProxy k)) ps',
                     Generic t, CovariantR (Rep t) (CountArgs ('KindProxy :: KindProxy k))
                    ) => Maps (CountArgs ('KindProxy :: KindProxy k)) ps ps' ->
                         W (t :: k) ps -> W t ps'
  covmap = gen_covmap

-- the argument mappings being extended
data family Maps (n :: Nat) :: [*] -> [*] -> *
data instance Maps Z ps ps' = Maps
-- use a GADT so that the provided functions can determine @ps@ and @ps'@
infixl 5 :::
data instance Maps (S n) (ps :: [*]) (ps' :: [*]) :: * where
  (:::) :: (ps ~ (a ': as), ps' ~ (b ': bs)) =>
           Maps n as bs -> (a -> b) -> Maps (S n) ps ps'

gen_covmap :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
               NLong (CountArgs ('KindProxy :: KindProxy k)) ps',
               Generic t, CovariantR (Rep t) (CountArgs ('KindProxy :: KindProxy k))
              ) => Maps (CountArgs ('KindProxy :: KindProxy k)) ps ps' ->
                   W (t :: k) ps -> W t ps'
gen_covmap maps = frRep . covmapR maps . toRep






-- the variant for representations; n is the expected length of ps
class CovariantR (t :: [*] -> *) (n :: Nat) where
  covmapR :: (NLong n ps, NLong n ps') => Maps n ps ps' -> t ps -> t ps'

instance CovariantR Void n where covmapR _ _ = error "CovariantR @Void"
instance (CovariantR l n, CovariantR r n) => CovariantR (l :+: r) n where
  covmapR fs = foldPlus (L . covmapR fs) (R . covmapR fs)

instance CovariantR U n where covmapR _ _ = U
instance (CovariantR l n, CovariantR r n) => CovariantR (l :*: r) n where
  covmapR fs (l :*: r) = covmapR fs l :*: covmapR fs r

instance NthMap m n => CovariantR (Par m) n where
  covmapR maps (Par x) = Par $ nthMap (Proxy :: Proxy m) maps x



class NthMap (n :: Nat) max where
  nthMap :: Proxy n -> Maps max ps ps' -> Nth n ps -> Nth n ps'

instance (max ~ S dummy) => NthMap Z max where nthMap  _ (_ ::: f) = f

instance (max ~ S max', NthMap n max')
  => NthMap (S n) max where
    nthMap _ (fs ::: _) = nthMap (Proxy :: Proxy n) fs


-- the case for type applications
instance (Lemma_NLongLengthMapEval argReps, Covariant t, NewMaps n argReps,
          -- NB could this next constraint perhaps be built into T?
          CountArgs ('KindProxy :: KindProxy k) ~ Length argReps
         ) => CovariantR (T (t :: k) argReps) n where
  covmapR :: forall ps ps'. (NLong n ps, NLong n ps') =>
             Maps n ps ps' -> T (t :: k) argReps ps -> T (t :: k) argReps ps'
  covmapR maps = -- the lemmas just introduce equality constraints
                 lemma_NLongLengthMapEval (Proxy :: Proxy argReps) (Proxy :: Proxy ps) $
                 lemma_NLongLengthMapEval (Proxy :: Proxy argReps) (Proxy :: Proxy ps') $
                 T . covmap (newMaps maps (Proxy :: Proxy argReps)) . unT



-- builds a map of extensions of the old maps, one for each representation
-- argument
class NewMaps n argReps where
  newMaps :: (NLong n ps, NLong n ps') =>
             Maps n ps ps' -> Proxy argReps ->
             Maps (Length argReps) (MapEval argReps ps) (MapEval argReps ps')

instance NewMaps n '[] where newMaps _ _ = Maps

instance (CovariantR argRep n, NewMaps n argReps, EvalMap argRep n) => NewMaps n (argRep ': argReps) where
  newMaps maps _ = newMaps maps (Proxy :: Proxy argReps) :::
                   evalMap (Proxy :: Proxy argRep) maps




-- the following is clearly dubious... indexed data types are not necessarily
-- covariant

{- NB deprecated; Idxd no longer adds a parameter
instance (EvalMap idx n, CovariantR r (S n)) => CovariantR (Idxd idx r) n where
  covmapR maps = Idxd . covmapR (maps ::: evalMap (Proxy :: Proxy idx) maps) . unIdxd
-}
class EvalMap (idx :: [*] -> *) n where
  evalMap :: (NLong n ps, NLong n ps') =>
             Proxy idx -> Maps n ps ps' -> Eval idx ps -> Eval idx ps'

instance NthMap m n => EvalMap (Par m) n where
  evalMap _ maps = nthMap (Proxy :: Proxy m) maps

instance (WIso t, CovariantR (T t rs) n) =>
  EvalMap (T (t :: k) rs) n where
  evalMap :: forall (ps :: [*]) (ps' :: [*]). (NLong n ps, NLong n ps') =>
             Proxy (T t rs) -> Maps n ps ps' ->
             Eval (T t rs) ps -> Eval (T t rs) ps'
  evalMap _ maps = toApps . unT . covmapR maps .
                   (id :: T t rs ps -> T t rs ps) .
                   T . frApps






instance CovariantR r (S n) => CovariantR (QU r) n where
  covmapR maps (QU x) = QU $ covmapR (maps ::: id) x
