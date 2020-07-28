{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding ((.), id)
import Generalized
import qualified VectorSpace as VS

-- ------------------------------------------------------------------------

sqr :: Num a => a -> a
sqr a = a * a

sqr' :: Num a => a -> a -> a
sqr' a da = 2 * a * da

magSqr :: Num a => (a, a) -> a
magSqr (a, b) = sqr a + sqr b

magSqr' :: Num a => (a, a) -> (a, a)
magSqr' (a,b) = (g (1,0), g (0,1))
  where
    g (da,db) = 2 * a * da + 2 * b * db

cosSinProd :: Floating a => (a, a) -> (a, a)
cosSinProd (x,y) = (cos z, sin z)
  where z = x * y

cosSinProd' :: Floating a => (a, a) -> ((a, a), (a,a))
cosSinProd' (x,y) = tr (g (1,0), g (0,1))
  where
    z = x * y
    g (dx,dy) = (- sin z * dz, cos z * dz)
      where dz = y * dx + x * dy

tr :: ((a,b), (c,d)) -> ((a,c),(b,d))
tr ((a,b), (c,d)) = ((a,c),(b,d))

-- ------------------------------------------------------------------------

sqrC :: forall k a. (Cartesian k, NumCat k a) => a `k` a
-- sqrC = mulC . dup
sqrC =
  case monObj :: ObjR k (a, a) of
    ObjR -> mulC . dup

magSqrC :: forall k a. (Cartesian k, NumCat k a) => (a, a) `k` a
-- magSqrC = addC . ((mulC . (exl △ exl)) △ (mulC . (exr △ exr)))
magSqrC =
  case monObj :: ObjR k (a, a) of
    ObjR ->
      case monObj :: ObjR k ((a, a), (a, a)) of
        ObjR ->
          addC . ((mulC . (exl △ exl)) △ (mulC . (exr △ exr)))

cosSinProdC :: forall k a. (Cartesian k, NumCat k a, FloatingCat k a) => (a, a) `k` (a, a)
-- cosSinProdC = (cosC △ sinC) . mulC
cosSinProdC =
  case monObj :: ObjR k (a, a) of
    ObjR -> (cosC △ sinC) . mulC

-- ------------------------------------------------------------------------

test_LinMap_sqrC :: Double -> (Double, Double)
test_LinMap_sqrC x = (z, VS.asFun f' 1)
  where
    D f = sqrC
    (z, f') = f x

test_LinMap_magSqrC :: (Double, Double) -> (Double, (Double, Double))
test_LinMap_magSqrC (x,y) = (z, (VS.asFun f' (1,0), VS.asFun f' (0,1)))
  where
    D f = magSqrC
    (z, f') = f (x,y)

test_LinMap_cosSinProdC :: (Double, Double) -> ((Double,Double), ((Double, Double), (Double, Double)))
test_LinMap_cosSinProdC (x,y) = (z, tr (VS.asFun f' (1,0), VS.asFun f' (0,1)))
  where
    D f = cosSinProdC
    (z, f') = f (x,y)

-- ------------------------------------------------------------------------

test_Cont_sqrC :: Double -> (Double, Double)
test_Cont_sqrC x = (z, g 1)
  where
    D f = sqrC
    (z, Cont k) = f x
    g = VS.asFun (k id)

test_Cont_magSqrC :: (Double, Double) -> (Double, (Double, Double))
test_Cont_magSqrC (x,y) = (z, (g (1,0), g (0,1)))
  where
    D f = magSqrC
    (z, Cont k) = f (x,y)
    g = VS.asFun (k id)

test_Cont_cosSinProdC :: (Double, Double) -> ((Double,Double), ((Double,Double),(Double,Double)))
test_Cont_cosSinProdC (x,y) = (z, ((g1 (1,0), g1 (0,1)), (g2 (1,0), g2 (0,1))))
  where
    D f = cosSinProdC
    (z, Cont k) = f (x,y)
    g1 = VS.asFun (k exl)
    g2 = VS.asFun (k exr)

-- ------------------------------------------------------------------------

test_Dual'_sqrC :: Double -> (Double, Double)
test_Dual'_sqrC x = (z, k 1)
  where
    D f = (sqrC :: D (Dual' Double (VS.LinMap Double)) Double Double)
    (z, Dual' k) = f x

test_Dual'_magSqrC :: (Double, Double) -> (Double, (Double, Double))
test_Dual'_magSqrC (x,y) = (z, k 1)
  where
    D f = (magSqrC :: D (Dual' Double (VS.LinMap Double)) (Double,Double) Double)
    (z, Dual' k) = f (x,y)

test_Dual'_cosSinProdC :: (Double, Double) -> ((Double,Double), ((Double,Double), (Double,Double)))
test_Dual'_cosSinProdC (x,y) = (z, (k (1,0), k (0,1)))
  where
    D f = (cosSinProdC :: D (Dual' Double (VS.LinMap Double)) (Double,Double) (Double,Double))
    (z, Dual' k) = f (x,y)

-- ------------------------------------------------------------------------

test_Begin_sqrC :: Double -> (Double, Double)
test_Begin_sqrC x = (z, VS.asFun (k id) 1)
  where
    D f = sqrC
    (z, Begin k) = f x

test_Begin_magSqrC :: (Double, Double) -> (Double, (Double, Double))
test_Begin_magSqrC (x,y) = (z, (VS.asFun (k inl) 1, VS.asFun (k inr) 1))
  where
    D f = magSqrC
    (z, Begin k) = f (x,y)

test_Begin_cosSinProdC :: (Double, Double) -> ((Double,Double), ((Double,Double), (Double,Double)))
test_Begin_cosSinProdC (x,y) = (z, tr (VS.asFun (k inl) 1, VS.asFun (k inr) 1))
  where
    D f = cosSinProdC
    (z, Begin k) = f (x,y)

-- ------------------------------------------------------------------------
