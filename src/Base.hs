{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
module Base where

import Prelude hiding ((.), id, zipWith)
import qualified Prelude as P
import Data.Foldable
import Data.Kind

import Data.Functor.Rep
import Data.Pointed

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

-- This class is not defined in the paper.
class Category k => ToFun k where
  toFun :: (Obj k a, Obj k b) => (a `k` b) -> (a -> b)

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

unAddFun :: (a ->⁺ b) -> (a -> b)
unAddFun (AddFun f) = f

instance Category (->⁺) where
  type Obj (->⁺) a = Additive a
  id = AddFun id
  AddFun g . AddFun f = AddFun (g . f)

instance ToFun (->⁺) where
  toFun = unAddFun

instance Monoidal (->⁺) where
  AddFun g >< AddFun f = AddFun (g >< f)
  monObj = ObjR

instance Cartesian (->⁺) where
  exl = AddFun exl
  exr = AddFun exr
  dup = AddFun dup

{-
Category (->⁺) は対象を Additive なものに制限しているだけでなく、
射も f(a .+. b) = f a .+. f b を満たすものに制限しているはず。

これを満たしていれば、
AddFun h . inl = AddFun f
AddFun h . inr = AddFun g
を満たす h は
h (x, y) = h (x, zero) .+. h (zero, y)  = f x .+. g y
で一意に決まる。

これを満たさない h (a,b) = a * b のような関数を考えると、
AddFun h . inl = AddFun (const 0)
AddFun h . inr = AddFun (const 0)
かつ
AddFun (const 0) . inl = AddFun (const 0)
AddFun (const 0) . inr = AddFun (const 0)
だが
AddFun h ≠ AddFun (const 0)
なので直和の普遍性を満たさない。
-}
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

-- ------------------------------------------------------------------------

{-
HasDotという名前に反して、内積ではなく、双対空間との同型性ではないか?
* 一般の内積だと dot に inverse が存在するとは限らない
* 正定値性の要求などがない
* Dual に対する Scalable のインスタンスの定義時に
  dot . scale a = (. scale a) . dot
  が期待されていると思うが、内積だとしたら、複素数上のベクトル空間の場合にはその代わりに
  dot . scale a = (. scale (conjugate a)) . dot 
  が成り立つことを期待したい。
-}
class (Category k, Obj k s, Obj k u, Additive u) => HasDot k s u where
  dot :: u -> (u `k` s)
  undot :: (u `k` s) -> u

instance (Scalable (->⁺) s, Num s) => HasDot (->⁺) s s where
  dot = scale
  undot (AddFun f) = f 1

instance (Cocartesian k, HasDot k s a, HasDot k s b, Obj k (a,b)) => HasDot k s (a, b) where
  dot (a,b) = dot a ▽ dot b
  undot f = (undot (f . inl), undot (f . inr))

-- 論文では結果の型は b ⊸ a だったけど b → a になってしまう
onDot :: (HasDot k s a , HasDot k s b) => ((b `k` s) -> (a `k` s)) -> (b -> a)
onDot f = undot . f . dot

-- ------------------------------------------------------------------------

class Functor h => Zip h where
  zipWith :: (a -> b -> c) -> h a -> h b -> h c

unzip :: Functor h => h (a, b) -> (h a, h b)
unzip = fmap exl △ fmap exr

-- @Functor h@ is not required in the paper. But I think it should.
class (Category k, Functor h) => MonoidalI k h where
  crossI :: (Obj k a, Obj k b) => h (a `k` b) -> (h a `k` h b)
  monObjI :: Obj k a => ObjR k (h a)

class MonoidalI k h => CartesianI k h where
  exI :: Obj k a => h (h a `k` a)
  replI :: Obj k a => a `k` h a -- why not dupI?

class MonoidalI k h => CocartesianI k h where
  inI :: Obj k a => h (a `k` h a)
  jamI :: Obj k a => h a `k` a

forkI :: forall k h a b. (CartesianI k h, Obj k a, Obj k b) => h (a `k` b) -> (a `k` h b)
forkI fs =
  case (monObjI :: ObjR k (h a), monObjI :: ObjR k (h b)) of
    (ObjR, ObjR) -> crossI fs . replI

-- why not name "unforkI"?
unforkF :: forall k h a b. (CartesianI k h, Obj k a, Obj k b) => (a `k` h b) -> h (a `k` b)
unforkF f = 
  case monObjI :: ObjR k (h b) of
    ObjR -> fmap (. f) exI

joinI :: forall k h a b. (CocartesianI k h, Obj k a, Obj k b) => h (b `k` a) -> (h b `k` a)
joinI fs =
  case (monObjI :: ObjR k (h a), monObjI :: ObjR k (h b)) of
    (ObjR, ObjR) -> jamI . crossI fs

-- why not name "unjoinI"?
unjoinPF :: forall k h a b. (CocartesianI k h, Obj k a, Obj k b) => (h b `k` a) -> h (b `k` a)
unjoinPF f =
  case monObjI :: ObjR k (h b) of
    ObjR -> fmap (f .) inI

-- ------------------------------------------------------------------------

instance Zip h => MonoidalI (->) h where
  crossI = zipWith id
  monObjI = ObjR

instance (Representable h, Zip h, Pointed h) => CartesianI (->) h where
  exI = tabulate (flip index)
  replI = point

-- "Foldable h" is required in the paper, but "Representable h" and "Eq (Rep h)" are required instead.
inIF :: (Additive a, Representable h, Eq (Rep h)) => h (a -> h a)
inIF = tabulate (\i a -> tabulate (\j -> if i == j then a else zero))

-- referred as "sum" in the paper
jamIF :: (Additive a, Foldable h) => h a -> a
jamIF = foldl' (.+.) zero

-- ------------------------------------------------------------------------

-- type Additive1 h = forall a. Additive a => Additive (h a)

instance (Zip h, forall a. Additive a => Additive (h a)) => MonoidalI (->⁺) h where
  crossI = AddFun . crossI . fmap unAddFun
  monObjI = ObjR

instance (Representable h, Zip h, Pointed h, forall a. Additive a => Additive (h a)) => CartesianI (->⁺) h where
  exI = fmap AddFun exI
  replI = AddFun replI

-- "Representable h" and "Eq (Rep h)" are missing in the paper.
-- "Zip h" (arising from the superclasses of an instance declaration) is missing in the paper.
instance (Representable h, Eq (Rep h), Foldable h, Zip h, forall a. Additive a => Additive (h a)) => CocartesianI (->⁺) h where
  inI = fmap AddFun inIF
  jamI = AddFun jamIF

-- ------------------------------------------------------------------------
