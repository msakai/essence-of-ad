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

toDual :: (VectorSpace a) => a -> LinMap (Scalar a) a (Scalar a)
toDual a = LinMap (\x -> fromMaybe 0 (lookup x m))
  where
    m = decompose a

fromDual :: forall a. VectorSpace a => LinMap (Scalar a) a (Scalar a) -> a
fromDual (LinMap f) = foldl' (.+.) zero [scale (f x) (basisValue x) | (x, _) <- decompose (zero :: a)]
