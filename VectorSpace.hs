{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module VectorSpace where

import Prelude hiding ((.), id)
import Data.List
import Data.Maybe

import Common hiding (Scalable (..))

-- ------------------------------------------------------------------------

class (Fractional (Scalar a), Eq (Basis a), Additive a) => VectorSpace a where
  type Scalar a
  type Basis a
  scale :: Scalar a -> a -> a
  decompose :: a -> [(Basis a, Scalar a)]
  basisValue :: Basis a -> a

linComb :: VectorSpace a => [(a, Scalar a)] -> a
linComb xs = foldl' (.+.) zero [scale s a | (a,s) <- xs]

compose :: VectorSpace a => [(Basis a, Scalar a)] -> a
compose xs = linComb [(basisValue a, s) | (a,s) <- xs]

instance VectorSpace Double where
  type Scalar Double = Double
  type Basis Double = ()
  scale = (*)
  decompose x = [((), x)]
  basisValue () = 1

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => VectorSpace (a, b) where
  type Scalar (a, b) = Scalar a
  type Basis (a, b) = Either (Basis a) (Basis b)
  scale s (a,b) = (scale s a, scale s b)
  decompose (a,b) = [(Left x, s) | (x,s) <- decompose a] ++ [(Right x, s) | (x,s) <- decompose b]
  basisValue (Left x) = (basisValue x, zero)
  basisValue (Right x) = (zero, basisValue x)

-- ------------------------------------------------------------------------

newtype LinMap s a b = LinMap (Basis a -> b)

asFun :: (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => (LinMap s a b) -> (a -> b)
asFun (LinMap f) x = linComb [(f b, s) | (b,s) <- decompose x]

instance Category (LinMap s) where
  type Obj (LinMap s) a = (VectorSpace a, Scalar a ~ s)
  id = LinMap basisValue
  g . LinMap f = LinMap (asFun g . f)

instance Additive b => Additive (LinMap s a b) where
  zero = LinMap (const zero)
  LinMap f .+. LinMap g = LinMap (\x -> f x .+. g x)

instance Monoidal (LinMap s) where
  LinMap f >< LinMap g = LinMap h
    where
      h (Left a) = (f a, zero)
      h (Right b) = (zero, g b)
  monObj = ObjR

instance Cartesian (LinMap s) where
  exl = LinMap f
    where
      f (Left a) = basisValue a
      f (Right _b) = zero
  exr = LinMap f
    where
      f (Left _a) = zero
      f (Right b) = basisValue b
  dup = LinMap (\a -> (basisValue a, basisValue a))

instance Cocartesian (LinMap s) where
  inl = LinMap (\a -> (basisValue a, zero))
  inr = LinMap (\b -> (zero, basisValue b))
  jam = LinMap f
    where
      f (Left a) = basisValue a
      f (Right b) = basisValue b

-- ------------------------------------------------------------------------

-- | Dual vector space
newtype Dual a = Dual (LinMap (Scalar a) a (Scalar a))

-- Scalar a について Additive ではなく Num で計算しているので注意
instance VectorSpace a => Additive (Dual a) where
  zero = Dual (LinMap (const 0))
  Dual (LinMap f) .+. Dual (LinMap g) = Dual $ LinMap (\x -> f x + g x)

instance VectorSpace a => VectorSpace (Dual a) where
  type Scalar (Dual a) = Scalar a
  type Basis (Dual a) = Basis a
  scale s (Dual (LinMap f)) = Dual (LinMap ((s*) . f))
  decompose (Dual (LinMap f)) = [(x, f x) | (x, _) <- decompose (zero :: a)]
  basisValue b = Dual (LinMap (\b' -> if b == b' then 1 else 0))

toDual :: VectorSpace a => a -> Dual a
toDual a = Dual $ LinMap $ \x -> fromMaybe 0 (lookup x m)
  where
    m = decompose a

toDualMap :: forall a b s. (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => LinMap s a b -> LinMap s (Dual b) (Dual a)
toDualMap (LinMap f) = LinMap g
  where
    -- f :: Basis a -> b
    g :: Basis (Dual b) -> Dual a
    g b' = Dual (LinMap h)
      where
        h :: Basis a -> s
        h a = sum [s | (b :: Basis b, s) <- decompose (f a), b == b']

fromDual :: forall a. VectorSpace a => Dual a -> a
fromDual (Dual (LinMap f)) = compose [(x, f x) | (x, _) <- decompose (zero :: a)]

fromDualMap :: forall a b s. (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => LinMap s (Dual b) (Dual a) -> LinMap s a b
fromDualMap (LinMap f) = LinMap g
  where
    -- f :: Basis (Dual b) -> Dual a    
    g :: Basis a -> b
    g a = compose [(b, h a) | (b, _) <- decompose (zero :: b), let Dual (LinMap (h :: Basis a -> s)) = f b]

-- ------------------------------------------------------------------------

test = (asFun f (2,1) == 7, asFun f2 (2,1) == 7)
  where
    f :: LinMap Double (Double, Double) Double
    f = LinMap f'
      where
        f' (Left _) = 2
        f' (Right _) = 3
    f2 = fromDualMap (toDualMap f)
