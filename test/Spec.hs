{-# OPTIONS_GHC -Wall -Wno-partial-type-signatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

import Prelude hiding ((.), id)
import Data.Proxy

import Generalized
import qualified VectorSpace
import qualified DataRep

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

class (ToFun k, Cartesian k, Cocartesian k, Scalable k Double, (forall a. Obj k a => Additive (a `k` Double)), HasDot k Double Double) => IsLinMap k
instance IsLinMap (->⁺)
instance IsLinMap (VectorSpace.LinMap Double)
instance IsLinMap (DataRep.LinMap Double)

sqrC'_LinMap :: forall k. IsLinMap k => Proxy k -> Double -> (Double, Double)
sqrC'_LinMap _ x = (z, toFun f' 1)
  where
    (z, f' :: k _ _) = unD sqrC x

magSqrC'_LinMap :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> (Double, (Double, Double))
magSqrC'_LinMap _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR -> (z, (toFun f' (1,0), toFun f' (0,1)))
  where
    (z, f' :: k _ _) = unD magSqrC (x,y)

cosSinProdC'_LinMap :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> ((Double,Double), ((Double, Double), (Double, Double)))
cosSinProdC'_LinMap _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR -> (z, tr (toFun f' (1,0), toFun f' (0,1)))
  where
    (z, f' :: k _ _) = unD cosSinProdC (x,y)

-- ------------------------------------------------------------------------

sqrC'_Cont :: forall k. IsLinMap k => Proxy k -> Double -> (Double, Double)
sqrC'_Cont _ x = (z, g 1)
  where
    (z, Cont k :: Cont _ k _ _) = unD sqrC x
    g = toFun (k id)

magSqrC'_Cont :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> (Double, (Double, Double))
magSqrC'_Cont _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR ->
      let g = toFun (k id)
       in (z, (g (1,0), g (0,1)))
  where
    (z, Cont k :: Cont Double k (Double,Double) Double) = unD magSqrC (x,y)

cosSinProdC'_Cont :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> ((Double,Double), ((Double,Double),(Double,Double)))
cosSinProdC'_Cont _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR ->
      let g1 = toFun (k exl)
          g2 = toFun (k exr)
       in (z, ((g1 (1,0), g1 (0,1)), (g2 (1,0), g2 (0,1))))
  where
    (z, Cont k :: Cont Double k (Double,Double) (Double,Double)) = unD cosSinProdC (x,y)

-- ------------------------------------------------------------------------

sqrC'_Dual' :: forall k. IsLinMap k => Proxy k -> Double -> (Double, Double)
sqrC'_Dual' _ x = (z, k 1)
  where
    (z, Dual' k :: Dual' Double k _ _) = unD sqrC x

magSqrC'_Dual' :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> (Double, (Double, Double))
magSqrC'_Dual' _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR -> (z, k 1)
  where
    (z, Dual' k :: Dual' Double k _ _) = unD magSqrC (x,y)

cosSinProdC'_Dual' :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> ((Double,Double), ((Double,Double), (Double,Double)))
cosSinProdC'_Dual' _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR -> (z, (k (1,0), k (0,1)))
  where
    (z, Dual' k :: Dual' Double k _ _) = unD cosSinProdC (x,y)

-- ------------------------------------------------------------------------

sqrC'_Begin :: forall k. IsLinMap k => Proxy k -> Double -> (Double, Double)
sqrC'_Begin _ x = (z, toFun (k id) 1)
  where
    (z, Begin k :: Begin _ k _ _) = unD sqrC x

magSqrC'_Begin :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> (Double, (Double, Double))
magSqrC'_Begin _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR -> (z, (toFun (k inl) 1, toFun (k inr) 1))
  where
    (z, Begin k :: Begin Double k (Double,Double) Double) = unD magSqrC (x,y)

cosSinProdC'_Begin :: forall k. IsLinMap k => Proxy k -> (Double, Double) -> ((Double,Double), ((Double,Double), (Double,Double)))
cosSinProdC'_Begin _ (x,y) =
  case monObj :: ObjR k (Double,Double) of
    ObjR -> (z, tr (toFun (k inl) 1, toFun (k inr) 1))
  where
    (z, Begin k :: Begin Double k (Double,Double) (Double,Double)) = unD cosSinProdC (x,y)

-- ------------------------------------------------------------------------

group1 :: forall k. IsLinMap k => Proxy k -> String -> TestTree
group1 proxy name = testGroup name
  [ testGroup "LinMap"
      [ testCase "sqr" $ sqrC'_LinMap proxy 3 @?= (sqr 3, sqr' 3)
      , testCase "magSqr" $ magSqrC'_LinMap proxy (3,4) @?= (magSqr (3,4), magSqr' (3,4))
      , testCase "cosSinProd" $ cosSinProdC'_LinMap proxy (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))
      ]
  , testGroup "Cont"
      [ testCase "sqr" $ sqrC'_Cont proxy 3 @?= (sqr 3, sqr' 3)
      , testCase "magSqr" $ magSqrC'_Cont proxy (3,4) @?= (magSqr (3,4), magSqr' (3,4))
      , testCase "cosSinProd" $ cosSinProdC'_Cont proxy (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))
      ]
  , testGroup "Dual'"
      [ testCase "sqr" $ sqrC'_Dual' proxy 3 @?= (sqr 3, sqr' 3)
      , testCase "magSqr" $ magSqrC'_Dual' proxy (3,4) @?= (magSqr (3,4), magSqr' (3,4))
      , testCase "cosSinProd" $ cosSinProdC'_Dual' proxy (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))
      ]
  , testGroup "Begin"
      [ testCase "sqr" $ sqrC'_Begin proxy 3 @?= (sqr 3, sqr' 3)
      , testCase "magSqr" $ magSqrC'_Begin proxy (3,4) @?= (magSqr (3,4), magSqr' (3,4))
      , testCase "cosSinProd" $ cosSinProdC'_Begin proxy (3,4) @?= (cosSinProd (3,4), cosSinProd' (3,4))
      ]
  ]

main :: IO ()
main = defaultMain $ testGroup "Tests" $
  [ group1 (Proxy :: Proxy (VectorSpace.LinMap Double)) "VectorSpace"
  , group1 (Proxy :: Proxy (DataRep.LinMap Double)) "DataRep"
  , group1 (Proxy :: Proxy (->⁺)) "AddFun"
  ]
