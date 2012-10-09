{-# LANGUAGE TypeFamilies, PolyKinds, MultiParamTypeClasses, DataKinds #-}

{-# LANGUAGE ConstraintKinds, TypeOperators, FlexibleContexts #-}

{-# LANGUAGE GADTs, FlexibleInstances, ScopedTypeVariables, InstanceSigs #-}


{-


This module is incomplete.

  * The basic interface of EqFree seems good.

  * I have no generic definition yet; I suspect Idxd needs to be changed to
    constrain all type variables simultaneously.

  * The EqFree interface cannot be used without fully specifying all ParInfos,
    even if we only need to establish some of the types' equivalence. The
    straight-forward approach via SamesImplies requires a property of NLong that I
    have not yet managed to prove: compositionality, ie NLong (S n) (t ': ts) must
    imply NLong n ts.

-}


module Data.PVGD.EqFree where

import Data.PVGD.BasicTypes
import Data.PVGD.W
import Data.PVGD.View

import GHC.Prim (Constraint)



data ParInfo = Param | Index



type family Sames (sames :: [ParInfo]) (ps :: [k]) (ps' :: [k]) :: Constraint
type instance Sames '[] '[] '[] = ()
type instance Sames ('Param ': sames) (p ': ps) (p' ': ps') =
  Sames sames ps ps'
type instance Sames ('Index ': sames) (p ': ps) (p' ': ps') =
  (p ~ p', Sames sames ps ps')

data SamesDict sames ps ps' where
  SamesDict :: Sames sames ps ps' => SamesDict sames ps ps'

{-
class SamesImplies (antecedent :: [ParInfo]) (consequent :: [ParInfo]) where
  samesImplies :: {-( NLong (Length antecedent) antecedent,
                   NLong (Length antecedent) ps,
                   NLong (Length antecedent) ps') => -}
                  SamesDict antecedent ps ps' -> SamesDict consequent ps ps'

type family Tail (ts :: [k]) :: [k]
type instance Tail (t ': ts) = ts

instance SamesImplies '[] '[] where samesImplies SamesDict = SamesDict
instance (c ~ Param, SamesImplies as cs) =>
  SamesImplies (Param ': as) (c ': cs) where
  samesImplies :: forall ps ps'.
    SamesDict (Param ': as) ps ps' -> SamesDict (c ': cs) ps ps'
  samesImplies SamesDict =
    case samesImplies (SamesDict :: SamesDict as (Tail ps) (Tail ps'))
         :: SamesDict cs (Tail ps) (Tail ps') of
    SamesDict -> SamesDict
instance (c ~ Param, SamesImplies as cs) =>
  SamesImplies (Param ': as) (c ': cs) where
  samesImplies :: forall ps ps'. (NLong (Length (Param ': as)) (Param ': as),
                                  NLong (Length (Param ': as)) ps,
                                  NLong (Length (Param ': as)) ps') =>
    SamesDict (Param ': as) ps ps' -> SamesDict (c ': cs) ps ps'
  samesImplies SamesDict =
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, as, Param)) $
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, Tail ps, Nth Z ps)) $
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, Tail ps', Nth Z ps')) $
    case samesImplies (SamesDict :: SamesDict as (Tail ps) (Tail ps'))
         :: SamesDict cs (Tail ps) (Tail ps') of
    SamesDict -> SamesDict
instance SamesImplies as cs =>
  SamesImplies (Index ': as) (Param ': cs) where
  samesImplies :: forall ps ps'. (NLong (Length (Index ': as)) (Index ': as),
                                  NLong (Length (Index ': as)) ps,
                                  NLong (Length (Index ': as)) ps') =>
    SamesDict (Index ': as) ps ps' -> SamesDict (Param ': cs) ps ps'
  samesImplies SamesDict =
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, as, Index)) $
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, Tail ps, Nth Z ps)) $
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, Tail ps', Nth Z ps')) $
    case samesImplies (SamesDict :: SamesDict as (Tail ps) (Tail ps'))
         :: SamesDict cs (Tail ps) (Tail ps') of
    SamesDict -> SamesDict
instance SamesImplies as cs =>
  SamesImplies (Index ': as) (Index ': cs) where
  samesImplies :: forall ps ps'. (NLong (Length (Index ': as)) (Index ': as),
                                  NLong (Length (Index ': as)) ps,
                                  NLong (Length (Index ': as)) ps') =>
    SamesDict (Index ': as) ps ps' -> SamesDict (Index ': cs) ps ps'
  samesImplies SamesDict =
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, as, Index)) $
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, Tail ps, Nth Z ps)) $
    lemma_NLong_compositional (Proxy :: Proxy '(Length as, Tail ps', Nth Z ps')) $
    case samesImplies (SamesDict :: SamesDict as (Tail ps) (Tail ps'))
         :: SamesDict cs (Tail ps) (Tail ps') of
    SamesDict -> SamesDict
-}


type family ParInfos (t :: k) :: [ParInfo]

class EqFree (t :: k) where
  eqFree :: (NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
             NLong (CountArgs ('KindProxy :: KindProxy k)) ps',
             NLong (CountArgs ('KindProxy :: KindProxy k)) (ParInfos t)) =>
            W t ps -> W t ps' -> Maybe (SamesDict (ParInfos t) ps ps')
{-
eqFreeP :: (EqFree t,
            NLong (CountArgs ('KindProxy :: KindProxy k)) ps,
            NLong (CountArgs ('KindProxy :: KindProxy k)) ps',
            NLong (CountArgs ('KindProxy :: KindProxy k)) (ParInfos t),
            SamesImplies (ParInfos t) pis,
            Length (ParInfos t) ~ CountArgs ('KindProxy :: KindProxy k),
            NLong (Length (ParInfos t)) (ParInfos t)) =>
           Proxy pis -> W (t :: k) ps -> W t ps' -> Maybe (SamesDict pis ps ps')
eqFreeP _ x y = samesImplies `fmap` eqFree x y



-- example applications of EqFree
data Box tag where Box :: (Eq a, Eq b) => tag a b -> a -> b -> Box tag

-- inferred equivalent: test ::
--   (EqFree t,
--    NLong (S (S Z)) (ParInfos t),
--    SamesImplies (ParInfos t) '[Index, Index]) =>
--   Box t -> Box t -> Bool
test (Box tag1 a1 b1) (Box tag2 a2 b2) =
  case eqFreeP (Proxy :: Proxy '[Index, Index]) (W2 tag1) (W2 tag2) of
  Nothing -> False
  Just SamesDict -> a1 == a2 && b1 == b2

-- example applications of EqFree
data Box' tag where Box' :: Eq b => tag (a :: *) b (c :: *) -> b -> Box' tag

-- inferred equivalent: test' ::
--   (EqFree t,
--    NLong (S (S (S Z))) (ParInfo t),
--    SamesImplies (ParInfo t) '[Param, Index, Param]) =>
--   Box' t -> Box' t -> Bool
test' (Box' tag1 b1) (Box' tag2 b2) =
  case eqFreeP (Proxy :: Proxy '[Param, Index, Param]) (W3 tag1) (W3 tag2) of
  Nothing -> False
  Just SamesDict -> b1 == b2
-}


type instance ParInfos Maybe = '[Param]



data Example0 :: * where Example0 :: Example0

type instance ParInfos Example0 = '[]
instance EqFree Example0 where
  eqFree (W0 Example0) (W0 Example0) = Just SamesDict


data Example1 :: * -> * where Example1 :: a -> Example1 a

type instance ParInfos Example1 = '[Param]
instance EqFree Example1 where
  eqFree (W1 (Example1 _)) (W1 (Example1 _)) = Just SamesDict


data Example2 :: * -> * where
  Example2_Int  :: Example2 Int
  Example2_Char :: Example2 Char

type instance ParInfos Example2 = '[Index]
instance EqFree Example2 where
  eqFree (W1 Example2_Int)  (W1 Example2_Int)  = Just SamesDict
  eqFree (W1 Example2_Char) (W1 Example2_Char) = Just SamesDict
  eqFree _                  _                    = Nothing


data Example3 :: * -> * where
  Example3_Int  :: Example3 Int
  Example3_Char :: Example3 Char
  Example3_List :: Example3 a -> Example3 [a]

type instance ParInfos Example3 = '[Index]
instance EqFree Example3 where
  eqFree (W1 Example3_Int)      (W1 Example3_Int)    = Just SamesDict
  eqFree (W1 Example3_Char)     (W1 Example3_Char)   = Just SamesDict
  eqFree (W1 (Example3_List l)) (W1 (Example3_List r)) =
    case eqFree (W1 l) (W1 r) of
    Just SamesDict -> Just SamesDict
    Nothing        -> Nothing
  eqFree _                      _                      = Nothing


data Example4 :: * -> * where
  Example4_Any  :: Example4 a
  Example4_Int  :: Example4 Int
  Example4_Char :: Example4 Char
  Example4_List :: Example4 a -> Example4 [a]

type instance ParInfos Example4 = '[Param]
instance EqFree Example4 where
  eqFree (W1 Example4_Any)      (W1 Example4_Any)    = Just SamesDict
  eqFree (W1 Example4_Int)      (W1 Example4_Int)    = Just SamesDict
  eqFree (W1 Example4_Char)     (W1 Example4_Char)   = Just SamesDict
  eqFree (W1 (Example4_List l)) (W1 (Example4_List r)) =
    case eqFree (W1 l) (W1 r) of
    Just SamesDict -> Just SamesDict
    Nothing        -> Nothing
  eqFree _                      _                      = Nothing


data Example5 :: * -> * where
  Example5_Int  :: Example5 Int
  Example5_Char :: Example5 Char
  Example5_Bool :: Example5 Bool
  Example5_List :: Example5 a -> Example5 [a]
  Example5_Pair :: Example5 b -> Example5 a -> Example5 (b, a)

type instance ParInfos Example5 = '[Index]
instance EqFree Example5 where
  eqFree (W1 Example5_Int)      (W1 Example5_Int)    = Just SamesDict
  eqFree (W1 Example5_Char)     (W1 Example5_Char)   = Just SamesDict
  eqFree (W1 Example5_Bool)     (W1 Example5_Bool)   = Just SamesDict
  eqFree (W1 (Example5_List l)) (W1 (Example5_List r)) =
    case eqFree (W1 l) (W1 r) of
    Just SamesDict -> Just SamesDict
    Nothing        -> Nothing
  eqFree (W1 (Example5_Pair lb la)) (W1 (Example5_Pair rb ra)) =
    case (eqFree (W1 lb) (W1 rb), eqFree (W1 la) (W1 ra)) of
    (Just SamesDict, Just SamesDict) -> Just SamesDict
    _                                -> Nothing
  eqFree _                      _                      = Nothing

type instance Rep Example5 =
  (Idxd Z (T Int '[]) U  :+:
   Idxd Z (T Char '[]) U :+:
   Idxd Z (T Bool '[]) U)     :+:
  (QE (Idxd (S Z) (T [] '[Par Z])
         (T Example5 '[Par Z])) :+:
   QE (QE (Idxd (S (S Z)) (T (,) '[Par Z, Par (S Z)])
         (T Example5 '[Par (S Z)] :*: T Example5 '[Par Z]))))


data Example6 :: * -> * -> * where
  Example6_Base  :: Example6 Int Char
  Example6_List :: Example6 a b -> Example6 [a] [b]

type instance Rep Example6 =
    Idxd Z (T Char '[]) (Idxd (S Z)
      (T Int '[]) U)                         :+:
  QE (QE
   (Idxd (S (S Z))     (T [] '[Par    Z ])
    (Idxd (S (S (S Z))) (T [] '[Par (S Z)])
     (T Example6 '[Par Z, Par (S Z)]))))

instance Generic Example6 where
  toRep (W2 Example6_Base) = L $ Idxd $ Idxd $ U
  toRep (W2 (Example6_List ab)) = R $ QE $ QE $ Idxd $ Idxd $ T $ W2 ab
  frRep (L (Idxd (Idxd U))) = W2 Example6_Base
  frRep (R (QE (QE (Idxd (Idxd (T (W2 ab))))))) = W2 $ Example6_List ab

type instance ParInfos Example6 = '[Index, Index]
instance EqFree Example6 where
  eqFree (W2 Example6_Base)     (W2 Example6_Base)     = Just SamesDict
  eqFree (W2 (Example6_List l)) (W2 (Example6_List r)) =
    case eqFree (W2 l) (W2 r) of
    Just SamesDict -> Just SamesDict
    Nothing        -> Nothing
  eqFree _                      _                      = Nothing
