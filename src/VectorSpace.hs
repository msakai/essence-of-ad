{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module VectorSpace where

import Prelude hiding ((.), id, curry, uncurry)
import Data.List
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import qualified Common as C
import Common hiding (Scalable (..))

-- ------------------------------------------------------------------------

class (Fractional (Scalar a), Ord (Basis a), Additive a) => VectorSpace a where
  type Scalar a
  type Basis a
  scale :: Scalar a -> a -> a
  decompose :: a -> Map (Basis a) (Scalar a)
  basisValue :: Basis a -> a

linComb :: VectorSpace a => [(a, Scalar a)] -> a
linComb xs = foldl' (.+.) zero [scale s a | (a,s) <- xs]

compose :: VectorSpace a => Map (Basis a) (Scalar a) -> a
compose m = linComb [(basisValue ba, s) | (ba,s) <- Map.toList m]

instance VectorSpace Double where
  type Scalar Double = Double
  type Basis Double = ()
  scale = (*)
  decompose x = Map.singleton () x
  basisValue () = 1

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => VectorSpace (a, b) where
  type Scalar (a, b) = Scalar a
  type Basis (a, b) = Either (Basis a) (Basis b)
  scale s (a,b) = (scale s a, scale s b)
  decompose (a,b) = Map.mapKeysMonotonic Left (decompose a) `Map.union` Map.mapKeysMonotonic Right (decompose b)
  basisValue (Left ba) = (basisValue ba, zero)
  basisValue (Right bb) = (zero, basisValue bb)

-- ------------------------------------------------------------------------

newtype LinMap s a b = LinMap (Basis a -> b)
{-
infixr 0 ⊸

data a ⊸ b where
  LinMap :: (Scalar a ~ Scalar b) => !(Basis a -> b) -> a ⊸ b

と書けると格好良いが、スカラー型の異なるベクトル空間の直積とかで困ったことになる。
-}

asFun :: (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => (LinMap s a b) -> (a -> b)
asFun (LinMap f) a = linComb [(f ba, s) | (ba,s) <- Map.toList (decompose a)]

instance Category (LinMap s) where
  type Obj (LinMap s) a = (VectorSpace a, Scalar a ~ s)
  id = LinMap basisValue
  g . LinMap f = LinMap (asFun g . f)

instance Additive b => Additive (LinMap s a b) where
  zero = LinMap (const zero)
  LinMap f .+. LinMap g = LinMap (\x -> f x .+. g x)

instance (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => VectorSpace (LinMap s a b) where
  type Scalar (LinMap s a b) = s
  type Basis (LinMap s a b) = (Basis a, Basis b)
  scale s (LinMap f) = LinMap (scale s . f)
  decompose (LinMap f) = Map.fromList $ do
    (ba, _) <- Map.toList $ decompose (zero :: a)
    (bb, s) <- Map.toList $ decompose (f ba)
    return ((ba,bb), s)
  basisValue (ba,bb) = LinMap (\ba' -> if ba == ba' then basisValue bb else zero)

instance Monoidal (LinMap s) where
  LinMap f >< LinMap g = LinMap h
    where
      h (Left ba) = (f ba, zero)
      h (Right bb) = (zero, g bb)
  monObj = ObjR

instance Cartesian (LinMap s) where
  exl = LinMap f
    where
      f (Left ba) = basisValue ba
      f (Right _bb) = zero
  exr = LinMap f
    where
      f (Left _ba) = zero
      f (Right bb) = basisValue bb
  dup = LinMap (\ba -> (basisValue ba, basisValue ba))

instance Cocartesian (LinMap s) where
  inl = LinMap (\ba -> (basisValue ba, zero))
  inr = LinMap (\bb -> (zero, basisValue bb))
  jam = LinMap f
    where
      f (Left ba) = basisValue ba
      f (Right bb) = basisValue bb

instance (VectorSpace s, Basis s ~ (), Scalar s ~ s) => C.Scalable (LinMap s) s where
  scale s = LinMap (\() -> s)

test_LinMap_VectorSpace = m
  where
    f :: LinMap Double (Double, Double) (Double, Double)
    f = LinMap f'
      where
        f' (Left _) = (1, 2)
        f' (Right _) = (3, 4)
    m = decompose f
{-
(1 3)
(2 4)
という行列
-}

-- ------------------------------------------------------------------------

-- | Dual vector space
newtype Dual a = Dual (LinMap (Scalar a) a (Scalar a))

-- Scalar a について Additive ではなく Num で計算しているので注意
instance VectorSpace a => Additive (Dual a) where
  zero = Dual (LinMap (const 0))
  Dual (LinMap f) .+. Dual (LinMap g) = Dual $ LinMap (\ba -> f ba + g ba)

instance VectorSpace a => VectorSpace (Dual a) where
  type Scalar (Dual a) = Scalar a
  type Basis (Dual a) = Basis a
  scale s (Dual (LinMap f)) = Dual (LinMap ((s*) . f))
  decompose (Dual (LinMap f)) = Map.mapWithKey (\ba _ -> f ba) $ decompose (zero :: a)
  basisValue ba = Dual (LinMap (\ba' -> if ba == ba' then 1 else 0))

toDual :: VectorSpace a => a -> Dual a
toDual a = Dual $ LinMap $ \ba -> Map.findWithDefault 0 ba m
  where
    m = decompose a

toDualMap :: forall a b s. (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => LinMap s a b -> LinMap s (Dual b) (Dual a)
toDualMap (LinMap f) = LinMap g
  where
    -- f :: Basis a -> b
    g :: Basis (Dual b) -> Dual a
    g bb = Dual (LinMap h)
      where
        h :: Basis a -> s
        h = Map.findWithDefault 0 bb . decompose . f

fromDual :: forall a. VectorSpace a => Dual a -> a
fromDual (Dual (LinMap f)) = compose $ Map.mapWithKey (\ba _ -> f ba) $ decompose (zero :: a)

fromDualMap :: forall a b s. (VectorSpace a, VectorSpace b, Scalar a ~ s, Scalar b ~ s) => LinMap s (Dual b) (Dual a) -> LinMap s a b
fromDualMap (LinMap f) = LinMap g
  where
    -- f :: Basis (Dual b) -> Dual a    
    g :: Basis a -> b
    g ba = compose $ Map.mapWithKey (\bb _ -> let Dual (LinMap (h :: Basis a -> s)) = f bb in h ba) $ decompose (zero :: b)

instance (VectorSpace u, VectorSpace s, Scalar u ~ s, Scalar s ~ s) => C.HasDot (LinMap s) s u where
  dot x = case toDual x of Dual f -> f
  undot f = fromDual (Dual f)

-- ------------------------------------------------------------------------

testDual = (asFun f (2,1) == 7, asFun f2 (2,1) == 7)
  where
    f :: LinMap Double (Double, Double) Double
    f = LinMap f'
      where
        f' (Left _) = 2
        f' (Right _) = 3
    f2 = fromDualMap (toDualMap f)

-- ------------------------------------------------------------------------

data a :⊗ b where
  TensorProd :: (Scalar a ~ s, Scalar b ~ s) => Map (Basis a, Basis b) s -> a :⊗ b

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => Additive (a :⊗ b) where
  zero = TensorProd $ Map.fromList $ do
    (ba, _) <- Map.toList $ decompose (zero :: a)
    (bb, _) <- Map.toList $ decompose (zero :: b)
    return ((ba,bb), 0)
  TensorProd m1 .+. TensorProd m2 = TensorProd $ Map.unionWith (+) m1 m2

instance (VectorSpace a, VectorSpace b, Scalar a ~ Scalar b) => VectorSpace (a :⊗ b) where
  type Scalar (a :⊗ b) = Scalar a
  type Basis (a :⊗ b) = (Basis a, Basis b)
  scale s (TensorProd m) = TensorProd $ Map.map (*s) m
  decompose (TensorProd m) = m
  basisValue bab = TensorProd $ Map.fromList $ do
    (ba,_) <- Map.toList $ decompose (zero :: a)
    (bb,_) <- Map.toList $ decompose (zero :: b)
    return ((ba,bb), if (ba,bb) == bab then 1 else 0)

curry
  :: forall a b c s. (VectorSpace a, VectorSpace b, VectorSpace c, Scalar a ~ s, Scalar b ~ s, Scalar c ~ s)
  => LinMap a (a :⊗ b) c -> LinMap s a (LinMap s b c)
curry (LinMap f) = LinMap g
  where
    g :: Basis a -> LinMap s b c
    g ba = LinMap (\bb -> f (ba,bb))

uncurry
  :: forall a b c s. (VectorSpace a, VectorSpace b, VectorSpace c, Scalar a ~ s, Scalar b ~ s, Scalar c ~ s)
  => LinMap s a (LinMap s b c) -> LinMap a (a :⊗ b) c
uncurry (LinMap f) = LinMap g
  where
    g (ba,bb) =
      case f ba of
        LinMap h -> h bb

mapTensor
  :: forall a b c d s.
     (VectorSpace a, VectorSpace b, VectorSpace c, VectorSpace d, Scalar a ~ s, Scalar b ~ s, Scalar c ~ s, Scalar d ~ s)
  => LinMap s a b -> LinMap s c d -> LinMap s (a :⊗ c) (b :⊗ d)
mapTensor (LinMap f) (LinMap g) = LinMap h
  where
    h :: Basis (a :⊗ c) -> (b :⊗ d)
    h (ba, bc) = TensorProd m
      where
        m1 :: Map (Basis b) s
        m1 = decompose (f ba)
        m2 :: Map (Basis d) s
        m2 = decompose (g bc)
        m :: Map (Basis (b :⊗ d)) s
        m = Map.fromList [((bb,bd), s1*s2) | (bb, s1) <- Map.toList m1, (bd, s2) <- Map.toList m2]

TensorProd test_Tensor = asFun h t
  where
    f, g :: LinMap Double Double Double
    f = LinMap (const 2)
    g = LinMap (const 3)
    h :: LinMap Double (Double :⊗ Double) (Double :⊗ Double)
    h = mapTensor f g

    t :: Double :⊗ Double
    t = TensorProd (Map.singleton ((),()) 4)
