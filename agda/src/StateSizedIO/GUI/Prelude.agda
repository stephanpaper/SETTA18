{-# OPTIONS --sized-types --guardedness #-}
module StateSizedIO.GUI.Prelude where

open import Size public renaming (Size to AgdaSize)

open import Data.Nat.Base public
open import Data.Bool.Base hiding (_<_;_≤_) public
open import Data.List.Base public

open import Function public  hiding (force)
open import Data.Integer.Base public hiding (_*_; _+_; _-_; _⊓_; _⊔_; pred; suc;_≤_;_<_;_>_;_≥_;_≮_;_≯_;_≰_;_≱_;_<′_;_>′_;_≤ᵇ_;>-nonZero;NonZero;≢-nonZero)
open import Agda.Builtin.Equality public
open import Data.Product public using (_×_; _,_)

open import NativeIO public

open import StateSizedIO.GUI.WxBindingsFFI public
open import StateSizedIO.GUI.VariableList public

open import SizedIO.Base public
open import StateSizedIO.GUI.BaseStateDependent public


-- test : {!!}
-- test = refl
