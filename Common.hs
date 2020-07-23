{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Common where

import Prelude hiding ((.), id)
import qualified Prelude as P
import Data.Kind

infixr 0 ->⁺
infixr 9 .
infixl 6 .+.

-- ------------------------------------------------------------------------

class Additive a where
  zero :: a
  (.+.) :: a -> a -> a

instance (Additive a, Additive b) => Additive (a, b) where
  zero = (zero, zero)
  (a1,a2) .+. (b1,b2) = (a1 .+. b1, a2 .+. b2)

instance Additive Double where
  zero = 0
  a .+. b = a + b

-- ------------------------------------------------------------------------

class Category k where
  type Obj k a :: Constraint
  id :: Obj k a => k a a
  (.) :: (Obj k a, Obj k b, Obj k c) => k b c -> k a b -> k a c

-- class (Category k, forall a b. (Obj k a, Obj k b) => Obj k (a,b)) => Monoidal k
-- としたいが、 Quantified predicate must have a class or type variable head というエラーになるので、
-- 代わりに monObj を用意した。
class Category k => Monoidal k where
  (><) :: (Obj k a, Obj k b, Obj k c, Obj k d) => (a `k` c) -> (b `k` d) -> ((a, b) `k` (c, d))
  monObj :: (Obj k a, Obj k b) => ObjR k (a, b)

-- Reified Obj constraint
data ObjR k a where
  ObjR :: Obj k a => ObjR k a

class Monoidal k => Cartesian k where
  exl :: (Obj k a, Obj k b) => (a, b) `k` a
  exr :: (Obj k a, Obj k b) => (a, b) `k` b
  dup :: Obj k a => a `k` (a, a)

(△) :: forall k a b c. (Cartesian k, Obj k a, Obj k b, Obj k c) => (a `k` b) -> (a `k` c) -> (a `k` (b,c))
-- f △ g = (f >< g) . dup
f △ g =
  case (monObj :: ObjR k (a,a), monObj :: ObjR k (b,c)) of
    (ObjR, ObjR) -> (f >< g) . dup

fork :: (Cartesian k, Obj k a, Obj k b, Obj k c) => (a `k` b, a `k` c) -> (a `k` (b,c))
fork (f, g) = f △ g

unfork :: forall k a b c. (Cartesian k, Obj k a, Obj k b, Obj k c) => (a `k` (b,c)) -> (a `k` b, a `k` c)
-- unfork h = (exl . h, exr . h)
unfork h = case monObj :: ObjR k (b, c) of
             ObjR -> (exl . h, exr . h)

-- 論文では Monoidal ではなく Category だけを要求していたが、
-- ここでは monObj を使う都合から Monoidal を要求することにした。
class Monoidal k => Cocartesian k where
  inl :: (Obj k a, Obj k b) => a `k` (a, b)
  inr :: (Obj k a, Obj k b) => b `k` (a, b)
  jam :: Obj k a => (a, a) `k` a

(▽) :: forall k a b c. (Monoidal k, Cocartesian k, Obj k a, Obj k b, Obj k c) => (a `k` c) -> (b `k` c) -> ((a,b) `k` c)
-- f ▽ g = jam . (f >< g)
f ▽ g =
  case (monObj :: ObjR k (a,b), monObj :: ObjR k (c,c)) of
    (ObjR, ObjR) -> jam . (f >< g)

join :: (Monoidal k, Cocartesian k, Obj k a, Obj k b, Obj k c) => (a `k` c, b `k` c) -> ((a,b) `k` c)
join (f, g) = f ▽ g

unjoin :: forall k a b c. (Monoidal k, Cocartesian k, Obj k a, Obj k b, Obj k c) => ((a,b) `k` c) -> (a `k` c, b `k` c)
-- unjoin h = (h . inl, h . inr)
unjoin h = case monObj :: ObjR k (a, b) of
             ObjR -> (h . inl, h . inr)

{-
If (,) is a biproduct in k, then
(1) exl = id ▽ zero
(2) exr = zero ▽ id
(3) inl = id △ zero
(4) inr = zero △ id

Proof:

(1)
  exl :: (a,b) `k` a
= (exl :: (a,b) `k` a) . (id :: (a,b) `k` (a,b))
= (exl :: (a,b) `k` a) . ((inl :: a `k` (a,b)) ▽ (inr :: b `k` (a,b)))
= (exl . inl :: a `k` a) ▽ (exl . inr :: b `k` a)
= (id :: a `k` a) ▽ (zero :: b `k` a)

(3)
  inl :: a `k` (a, b)
= (id :: (a,b) `k` (a,b)) . (inl :: a `k` (a, b))
= ((exl :: (a,b) `k` a) △ (exr :: (a,b) `k` b)) . (inl :: a `k` (a, b))
= (exl . inl :: a `k` a) △ (exr . inl :: a `k` b)
= (id :: a `k` a) △ (zero :: a `k` b)
-}

zeroBP :: forall k a b. (Cartesian k, Cocartesian k, Obj k a, Obj k b) => (a `k` b)
zeroBP =
  case monObj :: ObjR k (a,b) of
    ObjR -> exr . inl

addBP :: forall k a b. (Cartesian k, Cocartesian k, Obj k a, Obj k b) => (a `k` b) -> (a `k` b) -> (a `k` b)
addBP f g =
  case (monObj :: ObjR k (a, a), monObj :: ObjR k (b, b)) of
    (ObjR, ObjR) -> jam . (f >< g) . dup

{-
Forall f :: (a, a) `k` b, f . dup = addBP (f . inl) (f . inr).

Proof:

  addBP (f . inl) (f . inr)
= jam . ((f . inl) >< (f . inr)) . dup
= (id ▽ id) . ((f . inl) >< (f . inr)) . dup
= ((f . inl) ▽ (f . inr)) . dup
= f . (inl ▽ inr) . dup
= f . dup
-}

-- ------------------------------------------------------------------------

class (Category k, Obj k a) => Scalable k a where
  scale :: a -> (a `k` a)

class (Monoidal k, Obj k a) => NumCat k a where
  negateC :: a `k` a
  addC :: (a, a) `k` a
  mulC :: (a, a) `k` a

class (Category k, Obj k a) => FloatingCat k a where
  sinC :: a `k` a
  cosC :: a `k` a
  expC :: a `k` a

-- ------------------------------------------------------------------------

instance Category (->) where
  type Obj (->) a = ()
  id = P.id
  (.) = (P..)

instance Monoidal (->) where
  f >< g = \(a,b) -> (f a, g b)
  monObj = ObjR

instance Cartesian (->) where
  exl (a, _b) = a
  exr (_a, b) = b
  dup a = (a, a)

instance Num a => Scalable (->) a where
  scale a x = a * x

instance Num a => NumCat (->) a where
  negateC = negate
  addC = uncurry (+)
  mulC = uncurry (*)

instance Floating a => FloatingCat (->) a where
  sinC = sin
  cosC = cos
  expC = exp

-- ------------------------------------------------------------------------

newtype a ->⁺ b = AddFun (a -> b)

instance Category (->⁺) where
  type Obj (->⁺) a = Additive a
  id = AddFun id
  AddFun g . AddFun f = AddFun (g . f)

instance Monoidal (->⁺) where
  AddFun g >< AddFun f = AddFun (g >< f)
  monObj = ObjR

instance Cartesian (->⁺) where
  exl = AddFun exl
  exr = AddFun exr
  dup = AddFun dup

instance Cocartesian (->⁺) where
  inl = AddFun inlF
  inr = AddFun inrF
  jam = AddFun jamF

inlF :: Additive b => a -> (a, b)
inlF a = (a, zero)

inrF :: Additive a => b -> (a, b)
inrF b = (zero, b)

jamF :: Additive a => (a, a) -> a
jamF (a,b) = a .+. b

instance (Additive a, Num a) => Scalable (->⁺) a where
  scale a = AddFun (\da -> a * da)

-- 論文では抜けていた(?)定義
-- Cartesian (Cont r k) を inlF/inrF/jamF を使って定義するには必要
instance (Obj (->⁺) a, Obj (->⁺) b) => Additive (a ->⁺ b) where
  zero = zeroBP
  (.+.) = addBP
