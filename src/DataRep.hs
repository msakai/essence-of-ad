{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module DataRep where

import Prelude hiding ((.), id, curry, uncurry)
import Control.Exception (assert)
import Data.List
import Data.Proxy
import qualified Data.Vector.Generic as VG
import Foreign.Storable
import qualified Numeric.LinearAlgebra as HM

import qualified Base
import Base hiding (Scalable (..))

-- ------------------------------------------------------------------------

class (Fractional (Scalar a), Storable (Scalar a), HM.Numeric (Scalar a), Additive a) => VectorSpace a where
  type Scalar a
  scale :: Scalar a -> a -> a
  dim :: Proxy a -> Int
  toVector :: a -> HM.Vector (Scalar a)
  fromVector :: HM.Vector (Scalar a) -> a

linComb :: VectorSpace a => [(a, Scalar a)] -> a
linComb xs = foldl' (.+.) zero [scale s a | (a,s) <- xs]

instance VectorSpace Double where
  type Scalar Double = Double
  scale = (*)
  dim _ = 1
  toVector = VG.singleton
  fromVector = (VG.! 0)

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => VectorSpace (a, b) where
  type Scalar (a, b) = Scalar a
  scale s (a,b) = (scale s a, scale s b)
  dim _ = dim (Proxy :: Proxy a) + dim (Proxy :: Proxy b)
  toVector (a,b) = toVector a <> toVector b
  fromVector v =
    case VG.splitAt (dim (Proxy :: Proxy a)) v of
      (v1, v2) -> (fromVector v1, fromVector v2)

-- ------------------------------------------------------------------------

newtype LinMap s a b = LinMap (HM.Matrix s)

{-
infixr 0 ⊸

data a ⊸ b where
  LinMap :: (Scalar a ~ Scalar b) => !(HM.Matrix (Scalar a))

と書けると格好良いが、スカラー型の異なるベクトル空間の直積とかで困ったことになる。
-}

asFun :: (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => (LinMap s a b) -> (a -> b)
asFun (LinMap m) a = fromVector (m HM.#> toVector a)

instance Category (LinMap s) where
  type Obj (LinMap s) a = (VectorSpace a, Scalar a ~ s)

  id :: forall a. Obj (LinMap s) a => LinMap s a a
  id = LinMap $ HM.ident $ dim (Proxy :: Proxy a)

  LinMap m1 . LinMap m2 = LinMap (m1 HM.<> m2)

instance (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => Additive (LinMap s a b) where
  zero = LinMap $ HM.konst 0 (m, n)
    where
      m = dim (Proxy :: Proxy a)
      n = dim (Proxy :: Proxy b)
  LinMap m1 .+. LinMap m2 = LinMap $ HM.add m1 m2

instance (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => VectorSpace (LinMap s a b) where
  type Scalar (LinMap s a b) = s
  scale s (LinMap m) = LinMap (HM.scale s m)
  dim _ = dim (Proxy :: Proxy a) * dim (Proxy :: Proxy b)
  toVector (LinMap m) = HM.flatten m
  fromVector v = LinMap (HM.reshape (dim (Proxy :: Proxy b)) v)

instance Monoidal (LinMap s) where
  LinMap m1 >< LinMap m2 = LinMap $ HM.diagBlock [m1, m2]
  monObj = ObjR

instance Cartesian (LinMap s) where
  exl :: forall a b. (Obj (LinMap s) a, Obj (LinMap s) b) => LinMap s (a,b) a
  exl = LinMap $ HM.ident m HM.||| HM.konst 0 (m, n)
    where
      m = dim (Proxy :: Proxy a)
      n = dim (Proxy :: Proxy b)

  exr :: forall a b. (Obj (LinMap s) a, Obj (LinMap s) b) => LinMap s (a,b) b
  exr = LinMap $ HM.konst 0 (n, m) HM.||| HM.ident n
    where
      m = dim (Proxy :: Proxy a)
      n = dim (Proxy :: Proxy b)

  dup :: forall a. Obj (LinMap s) a => LinMap s a (a,a)
  dup = LinMap $
      HM.ident n
      HM.===
      HM.ident n
    where
      n = dim (Proxy :: Proxy a)

instance Cocartesian (LinMap s) where
  inl :: forall a b. (Obj (LinMap s) a, Obj (LinMap s) b) => LinMap s a (a,b)
  inl = LinMap $
      HM.ident m
      HM.===
      HM.konst 0 (n, m)
    where
      m = dim (Proxy :: Proxy a)
      n = dim (Proxy :: Proxy b)

  inr :: forall a b. (Obj (LinMap s) a, Obj (LinMap s) b) => LinMap s b (a,b)
  inr = LinMap $
      HM.konst 0 (n, m)
      HM.===
      HM.ident m
    where
      m = dim (Proxy :: Proxy a)
      n = dim (Proxy :: Proxy b)

  jam :: forall a. (Obj (LinMap s) a) => LinMap s (a,a) a
  jam = LinMap $ HM.ident n HM.||| HM.ident n
    where
      n = dim (Proxy :: Proxy a)

instance (VectorSpace s, Scalar s ~ s) => Base.Scalable (LinMap s) s where
  scale s = assert (dim (Proxy :: Proxy s) == 1) $ LinMap ((1 HM.>< 1) [s])

-- ------------------------------------------------------------------------

-- | Dual vector space
newtype Dual a = Dual (LinMap (Scalar a) a (Scalar a))

instance VectorSpace a => Additive (Dual a) where
  zero = Dual $ LinMap $ HM.konst 0 (n, 1)
    where
      n = dim (Proxy :: Proxy a)
  Dual (LinMap m1) .+. Dual (LinMap m2) = Dual $ LinMap $ HM.add m1 m2

instance VectorSpace a => VectorSpace (Dual a) where
  type Scalar (Dual a) = Scalar a
  scale s (Dual (LinMap m)) = Dual (LinMap (HM.scale s m))
  dim _ = dim (Proxy :: Proxy a)
  toVector (Dual (LinMap m)) = HM.flatten m
  fromVector v = Dual (LinMap (HM.reshape 1 v))

toDual :: VectorSpace a => a -> Dual a
toDual a = Dual $ LinMap $ HM.asRow (toVector a)

toDualMap :: forall a b s. (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => LinMap s a b -> LinMap s (Dual b) (Dual a)
toDualMap (LinMap m) = LinMap (HM.tr' m)

fromDual :: forall a. VectorSpace a => Dual a -> a
fromDual (Dual (LinMap m)) = fromVector $ HM.flatten m

fromDualMap :: forall a b s. (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => LinMap s (Dual b) (Dual a) -> LinMap s a b
fromDualMap (LinMap m) = LinMap (HM.tr' m)

instance (VectorSpace u, VectorSpace s, Scalar u ~ s, Scalar s ~ s) => Base.HasDot (LinMap s) s u where
  dot x = case toDual x of Dual f -> f
  undot f = fromDual (Dual f)

-- ------------------------------------------------------------------------

testDual = (asFun f (2,1) == 7, asFun f2 (2,1) == 7)
  where
    f :: LinMap Double (Double, Double) Double
    f = LinMap $ HM.asRow (VG.fromList [2,3])
    f2 = fromDualMap (toDualMap f)

-- ------------------------------------------------------------------------

data a :⊗ b where
  TensorProd :: (Scalar a ~ s, Scalar b ~ s) => HM.Matrix s -> a :⊗ b

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => Additive (a :⊗ b) where
  zero = TensorProd (HM.konst 0 (m, n))
    where
      m = dim (Proxy :: Proxy a)
      n = dim (Proxy :: Proxy b)
  TensorProd m1 .+. TensorProd m2 = TensorProd $ m1 `HM.add` m2

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => VectorSpace (a :⊗ b) where
  type Scalar (a :⊗ b) = Scalar a
  scale s (TensorProd m) = TensorProd $ HM.scale s m
  dim _ = dim (Proxy :: Proxy a) * dim (Proxy :: Proxy b)
  toVector (TensorProd m) = HM.flatten m
  fromVector v = TensorProd (HM.reshape (dim (Proxy :: Proxy b)) v)


curry
  :: forall a b c s. (VectorSpace a, VectorSpace b, VectorSpace c, Scalar a ~ s, Scalar b ~ s, Scalar c ~ s)
  => LinMap s (a :⊗ b) c -> LinMap s a (LinMap s b c)
curry (LinMap m) = LinMap $ HM.reshape (nb*nc) $ HM.flatten m
  where
    nb = dim (Proxy :: Proxy b)
    nc = dim (Proxy :: Proxy c)

uncurry
  :: forall a b c s. (VectorSpace a, VectorSpace b, VectorSpace c, Scalar a ~ s, Scalar b ~ s, Scalar c ~ s)
  => LinMap s a (LinMap s b c) -> LinMap s (a :⊗ b) c
uncurry (LinMap m) = LinMap $ HM.reshape nc $ HM.flatten m
  where
    nc = dim (Proxy :: Proxy c)

mapTensor
  :: forall a b c d s.
     (VectorSpace a, VectorSpace b, VectorSpace c, VectorSpace d, Scalar a ~ s, Scalar b ~ s, Scalar c ~ s, Scalar d ~ s)
  => LinMap s a b -> LinMap s c d -> LinMap s (a :⊗ c) (b :⊗ d)
mapTensor (LinMap m1) (LinMap m2) = LinMap $ ((na*nc) HM.>< (nb*nd)) [(m1 `HM.atIndex` (i, k)) * (m2 `HM.atIndex` (j, l)) | i <- [0..na-1], j <- [0..nc-1], k <- [0..nb-1], l <- [0..nd-1]]
  where
    na = dim (Proxy :: Proxy a)
    nb = dim (Proxy :: Proxy b)
    nc = dim (Proxy :: Proxy c)
    nd = dim (Proxy :: Proxy d)

TensorProd test_Tensor = asFun h t
  where
    f, g :: LinMap Double Double Double
    f = Base.scale 2
    g = Base.scale 3
    h :: LinMap Double (Double :⊗ Double) (Double :⊗ Double)
    h = mapTensor f g

    t :: Double :⊗ Double
    t = TensorProd $ (1 HM.>< 1) [4]
