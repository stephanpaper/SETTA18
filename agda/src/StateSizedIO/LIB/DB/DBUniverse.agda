
module StateSizedIO.LIB.DB.DBUniverse where

open import Function
open import Data.Bool
open import Data.String hiding (_==_; show)
open import Data.Nat renaming (_≟_ to _≟Nat_)
open import Data.List
open import Data.Vec
open import Data.Product
open import Data.Maybe hiding (maybe)
open import Relation.Nullary

open import StateSizedIO.LIB.DB.Schema

open import Relation.Unary as R
open import Agda.Builtin.String using (primStringEquality)
open import lib.libraryBool

-- Overloaded equality

data Type : Set where
  fieldType : Type
  string    : Type
  nat       : Type
  bool      : Type
  list      : Type -> Type
  pair      : Type -> Type -> Type
  vec       : Type -> ℕ -> Type
  maybe     : Type -> Type

El : Type -> Set
El fieldType  = FieldType
El string     = String
El nat        = ℕ
El bool       = Bool
El (list a)   = List (El a)
El (pair a b) = El a × El b
El (vec a n)  = Vec (El a) n
El (maybe a)  = Maybe (El a)

infix 20 _==_

_==_ : {a : Type} -> El a -> El a -> Bool
_==_ {fieldType} string string = true
_==_ {fieldType} integer integer = true
_==_ {fieldType} _ _ = false
_==_ {string} x y = primStringEquality x y
_==_ {nat} x y with x ≟Nat y
_==_ {nat} x y | yes p = true
_==_ {nat} x y | no ¬p = false
_==_ {bool} false false = true
_==_ {bool} true true = true
_==_ {bool} _ _ = false

_==_ {list a} []        [] = true
_==_ {list a} (x ∷ xs) (y ∷ ys) = (x == y) ∧ (xs == ys)
_==_ {list a} _         _ = false

_==_ {pair a b} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ ∧ y₁ == y₂

_==_ {vec a ._} []        []        = true
_==_ {vec a ._} (x ∷ xs) (y ∷ ys) = (x == y) ∧ (xs == ys)

_==_ {maybe a} nothing  nothing  = true
_==_ {maybe a} (just x) (just y) = x == y
_==_ {maybe a} _        _        = false


show : {a : Type} -> El a -> String
show {a} x = "<exercise>"


nub : {a : Type} -> List (El a) -> List (El a)
nub [] = []
nub (x ∷ xs) = x ∷ boolFilter (not ∘ _==_ x) xs
