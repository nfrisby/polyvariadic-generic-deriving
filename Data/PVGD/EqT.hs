{-# LANGUAGE TypeFamilies, PolyKinds, DataKinds, TypeOperators, GADTs #-}

{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, InstanceSigs,
  ScopedTypeVariables #-}

module Data.PVGD.EqT where

import Data.PVGD.BasicTypes
import Data.PVGD.W
import Data.PVGD.View

data family Eqs (n :: Nat) (ps :: [*]) (ps' :: [*]) :: *
data instance Eqs Z ps ps' = Eqs
data instance Eqs (S n) ps ps' where
  And :: (Nth n ps ~ Nth n ps') =>
         Eqs n ps ps' -> Eqs (S n) ps ps'




-- TODO how to specify which of the parameters are indices? Only indices are
-- determined type equal by value equivalence; non-indices must be equal to
-- begin with.

-- Currently, EqT only works if all parameters are indices.

class EqT (t :: k) where
  eqT :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
          NLong (CountArgs ('KindProxy :: KindProxy k)) ps') =>
         W t ps -> W t ps' -> Maybe (Eqs (CountArgs ('KindProxy :: KindProxy k)) ps ps')

class EqR (r :: [*] -> *) (n :: Nat) where
  eqR :: (NLong n ps, NLong n ps') => Proxy n -> r ps -> r ps' -> Maybe (Eqs n ps ps')

--instance EqR (Idxd n idx r) (S Z) where



data GADT :: * -> * where
  GADT_Int  :: GADT Int
  GADT_Char :: GADT Char
  GADT_Bool :: GADT Bool
  GADT_List :: GADT a -> GADT [a]
  GADT_Pair :: GADT b -> GADT a -> GADT (b, a)


instance EqT GADT where
  eqT :: forall (ps :: [*]) (ps' :: [*]).
             (NLong (CountArgs ('KindProxy :: KindProxy (* -> *))) ps,
              NLong (CountArgs ('KindProxy :: KindProxy (* -> *))) ps') =>
             W GADT ps -> W GADT ps' -> Maybe (Eqs (CountArgs ('KindProxy :: KindProxy (* -> *))) ps ps')
  eqT (W1 x) (W1 y) = w x y where
    w :: GADT (Nth Z ps) -> GADT (Nth Z ps') -> Maybe (Eqs (S Z) ps ps')
    w GADT_Int  GADT_Int  = Just $ And Eqs
    w GADT_Char GADT_Char = Just $ And Eqs
    w GADT_Bool GADT_Bool = Just $ And Eqs
    w (GADT_List x) (GADT_List y) = case eqT (W1 x) (W1 y) of
      Nothing        -> Nothing
      Just (And Eqs) -> Just $ And Eqs
    w (GADT_Pair xb xa) (GADT_Pair yb ya) = case (eqT (W1 xb) (W1 yb), eqT (W1 xa) (W1 ya)) of
      (Just (And Eqs), Just (And Eqs)) -> Just $ And Eqs
      _                                -> Nothing
    w _                 _                 = Nothing



type instance Rep GADT =
  (Idxd Z (T Int '[]) U  :+:
   Idxd Z (T Char '[]) U :+:
   Idxd Z (T Bool '[]) U)     :+:
  (QE (Idxd (S Z) (T [] '[Par Z])
         (T GADT '[Par Z])) :+:
   QE (QE (Idxd (S (S Z)) (T (,) '[Par Z, Par (S Z)])
         (T GADT '[Par (S Z)] :*: T GADT '[Par Z]))))
