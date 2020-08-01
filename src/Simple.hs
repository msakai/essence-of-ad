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
module Simple where

import Prelude hiding ((.), id)

import Common
import qualified Generalized as G

infixr 0 ⊸

type a ⊸ b = a ->⁺ b

type D = G.D (->⁺)

linearD :: (a ⊸ b) -> D a b
linearD g@(AddFun f) = G.D (\a -> (f a, g))
