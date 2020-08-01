{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding ((.), id)
import Generalized
import qualified VectorSpace as VS

import Test.Tasty
import Test.Tasty.HUnit

-- ------------------------------------------------------------------------

sqr :: Num a => a -> a
sqr a = a * a

sqr' :: Num a => a -> a
sqr' a = 2 * a * da
  where
    da = 1

magSqr :: Num a => (a, a) -> a
magSqr (a, b) = sqr a + sqr b

magSqr' :: Num a => (a, a) -> (a, a)
magSqr' (a,b) = (g (1,0), g (0,1))
  where
    g (da,db) = 2 * a * da + 2 * b * db

cosSinProd :: Floating a => (a, a) -> (a, a)
cosSinProd (x,y) = (cos z, sin z)
  where z = x * y

cosSinProd' :: Floating a => (a, a) -> ((a, a), (a, a))
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

sqrC'_LinMap :: Double -> (Double, Double)
sqrC'_LinMap x = (z, VS.asFun f' 1)
  where
    D f = sqrC
    (z, f') = f x

magSqrC'_LinMap :: (Double, Double) -> (Double, (Double, Double))
magSqrC'_LinMap (x,y) = (z, (VS.asFun f' (1,0), VS.asFun f' (0,1)))
  where
    D f = magSqrC
    (z, f') = f (x,y)

cosSinProdC'_LinMap :: (Double, Double) -> ((Double,Double), ((Double, Double), (Double, Double)))
cosSinProdC'_LinMap (x,y) = (z, tr (VS.asFun f' (1,0), VS.asFun f' (0,1)))
  where
    D f = cosSinProdC
    (z, f') = f (x,y)

test_sqrC'_LinMap :: Assertion
test_sqrC'_LinMap = sqrC'_LinMap 3 @?= (sqr 3, sqr' 3)

test_magSqrC'_LinMap :: Assertion
test_magSqrC'_LinMap = magSqrC'_LinMap (3,4) @?= (magSqr (3,4), magSqr' (3,4))

test_cosSinProdC'_LinMap :: Assertion
test_cosSinProdC'_LinMap = cosSinProdC'_LinMap (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))

-- ------------------------------------------------------------------------

sqrC'_Cont :: Double -> (Double, Double)
sqrC'_Cont x = (z, g 1)
  where
    D f = sqrC
    (z, Cont k) = f x
    g = VS.asFun (k id)

magSqrC'_Cont :: (Double, Double) -> (Double, (Double, Double))
magSqrC'_Cont (x,y) = (z, (g (1,0), g (0,1)))
  where
    D f = magSqrC
    (z, Cont k) = f (x,y)
    g = VS.asFun (k id)

cosSinProdC'_Cont :: (Double, Double) -> ((Double,Double), ((Double,Double),(Double,Double)))
cosSinProdC'_Cont (x,y) = (z, ((g1 (1,0), g1 (0,1)), (g2 (1,0), g2 (0,1))))
  where
    D f = cosSinProdC
    (z, Cont k) = f (x,y)
    g1 = VS.asFun (k exl)
    g2 = VS.asFun (k exr)

test_sqrC'_Cont :: Assertion
test_sqrC'_Cont = sqrC'_Cont 3 @?= (sqr 3, sqr' 3)

test_magSqrC'_Cont :: Assertion
test_magSqrC'_Cont = magSqrC'_Cont (3,4) @?= (magSqr (3,4), magSqr' (3,4))

test_cosSinProdC'_Cont :: Assertion
test_cosSinProdC'_Cont = cosSinProdC'_Cont (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))

-- ------------------------------------------------------------------------

sqrC'_Dual' :: Double -> (Double, Double)
sqrC'_Dual' x = (z, k 1)
  where
    D f = (sqrC :: D (Dual' Double (VS.LinMap Double)) Double Double)
    (z, Dual' k) = f x

magSqrC'_Dual' :: (Double, Double) -> (Double, (Double, Double))
magSqrC'_Dual' (x,y) = (z, k 1)
  where
    D f = (magSqrC :: D (Dual' Double (VS.LinMap Double)) (Double,Double) Double)
    (z, Dual' k) = f (x,y)

cosSinProdC'_Dual' :: (Double, Double) -> ((Double,Double), ((Double,Double), (Double,Double)))
cosSinProdC'_Dual' (x,y) = (z, (k (1,0), k (0,1)))
  where
    D f = (cosSinProdC :: D (Dual' Double (VS.LinMap Double)) (Double,Double) (Double,Double))
    (z, Dual' k) = f (x,y)

test_sqrC'_Dual' :: Assertion
test_sqrC'_Dual' = sqrC'_Dual' 3 @?= (sqr 3, sqr' 3)

test_magSqrC'_Dual' :: Assertion
test_magSqrC'_Dual' = magSqrC'_Dual' (3,4) @?= (magSqr (3,4), magSqr' (3,4))

test_cosSinProdC'_Dual' :: Assertion
test_cosSinProdC'_Dual' = cosSinProdC'_Dual' (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))

-- ------------------------------------------------------------------------

sqrC'_Begin :: Double -> (Double, Double)
sqrC'_Begin x = (z, VS.asFun (k id) 1)
  where
    D f = sqrC
    (z, Begin k) = f x

magSqrC'_Begin :: (Double, Double) -> (Double, (Double, Double))
magSqrC'_Begin (x,y) = (z, (VS.asFun (k inl) 1, VS.asFun (k inr) 1))
  where
    D f = magSqrC
    (z, Begin k) = f (x,y)

cosSinProdC'_Begin :: (Double, Double) -> ((Double,Double), ((Double,Double), (Double,Double)))
cosSinProdC'_Begin (x,y) = (z, tr (VS.asFun (k inl) 1, VS.asFun (k inr) 1))
  where
    D f = cosSinProdC
    (z, Begin k) = f (x,y)

test_sqrC'_Begin :: Assertion
test_sqrC'_Begin = sqrC'_Begin 3 @?= (sqr 3, sqr' 3)

test_magSqrC'_Begin :: Assertion
test_magSqrC'_Begin = magSqrC'_Begin (3,4) @?= (magSqr (3,4), magSqr' (3,4))

test_cosSinProdC'_Begin :: Assertion
test_cosSinProdC'_Begin = cosSinProdC'_Begin (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))

-- ------------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testGroup "LinMap"
      [ testCase "sqr" test_sqrC'_LinMap
      , testCase "magSqr" test_magSqrC'_LinMap
      , testCase "cosSinProd" test_cosSinProdC'_LinMap
      ]
  , testGroup "Cont"
      [ testCase "sqr" test_sqrC'_Cont
      , testCase "magSqr" test_magSqrC'_Cont
      , testCase "cosSinProd" test_cosSinProdC'_Cont
      ]
  , testGroup "Dual'"
      [ testCase "sqr" test_sqrC'_Dual'
      , testCase "magSqr" test_magSqrC'_Dual'
      , testCase "cosSinProd" test_cosSinProdC'_Dual'
      ]
  , testGroup "Begin"
      [ testCase "sqr" test_sqrC'_Begin
      , testCase "magSqr" test_magSqrC'_Begin
      , testCase "cosSinProd" test_cosSinProdC'_Begin
      ]
  ]
