{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators #-}

{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}

module Examples where

-- basic type stuff
import Data.PVGD.BasicTypes (Nat(S, Z))

-- the tricky W data family
import Data.PVGD.W (W(W0, W1, W2), unW1, unW2, asW1, asW2)

-- the generic view
import Data.PVGD.View
  (Rep, Generic, toRep, frRep,
   U(U), (:*:)((:*:)), (:+:)(L, R), foldPlus, Par(Par), unPar,
   T(T), unT)

-- the interesting T representation type and the Covariant class with a generic
-- definition
import Data.PVGD.Covariant (Covariant, covmap, Maps(Maps, (:::)))



--------------------
-- representations for simple types: non-recursive with only parameters as
-- fields
type instance Rep Bool = U :+: U
instance Generic Bool where
  toRep (W0 b) = if b then L U else R U
  frRep = W0 . foldPlus (const True) (const False)

type instance Rep Maybe = U :+: Par Z
instance Generic Maybe where
  toRep = maybe (L U) (R . Par) . unW1
  frRep = W1 . foldPlus (const Nothing) (Just . unPar)

type instance Rep (,) = Par (S Z) :*: Par Z
instance Generic (,) where
  toRep (W2 (b, a)) = Par b :*: Par a
  frRep (Par b :*: Par a) = W2 (b, a)

type instance Rep Either = Par (S Z) :+: Par Z
instance Generic Either where
  toRep = either (L . Par) (R . Par) . unW2
  frRep = W2 . foldPlus (Left . unPar) (Right . unPar)

type instance Rep [] = U   :+:   Par Z :*: T [] '[Par Z]
instance Generic [] where
  toRep (W1 x) = case x of
    [] -> L U
    a : as -> R $ Par a :*: T (W1 (map Par as))
  frRep (L U) = W1 []
  frRep (R (Par a :*: T (W1 as))) = W1 $ a : map unPar as

instance Covariant Bool -- NB non-sensical, but well-typed
instance Covariant Maybe
instance Covariant (,)
instance Covariant Either
instance Covariant []





--------------------
-- generic deciable equality is easy
gen_eq :: (Generic t, Eq (Rep t '[])) => t -> t -> Bool -- same inferred
gen_eq x y = toRep (W0 x) == toRep (W0 y)

gen_eq1 :: (Generic t, Eq (Rep t '[a])) => t a -> t a -> Bool -- same inferred
gen_eq1 x y = toRep (W1 x) == toRep (W1 y)   where _ = x `asTypeOf` y

gen_eq2 :: (Generic t, Eq (Rep t '[a, b])) => t b a -> t b a -> Bool -- same inferred
gen_eq2 x y = toRep (W2 x) == toRep (W2 y)   where _ = x `asTypeOf` y





--------------------
-- X involves a type application and has two parameters

data X f (b :: *) (a :: *) = X Int (f a b) deriving Show

-- the arguments to T f are reversed
type instance Rep (X f) = T Int '[] :*: T f '[Par (S Z), Par Z]
instance Covariant f => Generic (X f) where
  toRep (W2 (X i fba)) =
    T (W0 i) :*: T (covmap (Maps ::: Par ::: Par) $ W2 fba)
  frRep (T (W0 i) :*: T fba) =
    W2 $ X i $ unW2 $ covmap (Maps ::: unPar ::: unPar) fba

instance Covariant Int where covmap Maps (W0 x) = W0 x
instance Covariant f => Covariant (X f)

instance (Covariant f, Eq (Rep (X f) '[a, b])) => Eq (X f b a) where (==) = gen_eq2

--------------------
-- another rich example with non-regular mutual recursion

data Flip (b :: *) (a :: *) = Stop b a | Flip (Flop a b) deriving Show
newtype Flop (b :: *) (a :: *) = Flop (Flip a b) deriving Show

type instance Rep Flip = Par (S Z) :*: Par Z   :+:   T Flop '[Par (S Z), Par Z]
instance Generic Flip where
  toRep (W2 (Stop b a)) = L $ Par b :*: Par a
  toRep (W2 (Flip x))   = R $ T $ covmap (Maps ::: Par ::: Par) $ W2 x
  frRep (L (Par b :*: Par a)) = W2 $ Stop b a
  frRep (R (T x)) = W2 $ Flip $ unW2 $ covmap (Maps ::: unPar ::: unPar) x

type instance Rep Flop = T Flip '[Par (S Z), Par Z]
instance Generic Flop where
  toRep (W2 (Flop x)) = T $ covmap (Maps ::: Par ::: Par) $ W2 x
  frRep = W2 . Flop . unW2 . covmap (Maps ::: unPar ::: unPar) . unT

instance Covariant Flip
instance Covariant Flop

instance (Eq b, Eq a) => Eq (Flip b a) where (==) = gen_eq2
instance (Eq b, Eq a) => Eq (Flop b a) where (==) = gen_eq2





example0   = X 0 ("foo", True) == X 0 ("bar", False)
example1 f = covmap (Maps ::: f ::: id) `asW2` X 0 ((), ["foo", "baz", "bar"])
example2   = covmap (Maps ::: reverse ::: map (+1)) `asW2` ("foo", [0..5])
example3   = covmap (error "testing inference") `asW1` [0..5] -- inferred :: [t]
example4   =
   (==) (Flip $ Flop $ Flip $ Flop $ Stop False "oof") $
   covmap (Maps ::: not ::: reverse) `asW2` (Flip $ Flop $ Flip $ Flop $ Stop True "foo")