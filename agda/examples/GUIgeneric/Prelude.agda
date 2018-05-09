module GUIgeneric.Prelude where

open import Data.Bool public
open import Data.Empty public
open import Data.List public
open import Data.Maybe.Base hiding (map) public
open import Data.Nat hiding (_≟_; _≤_; _≤?_) public
open import Data.Product hiding (map; zip) public
open import Data.String hiding (decSetoid ; concat ; length ; replicate) renaming (_++_ to _++Str_; _==_ to _==Str_; _≟_ to _≟Str_) public
open import Data.Sum public hiding (map;swap)
open import Data.Unit hiding (_≟_; decSetoid; setoid) public

open import Function public
open import Level renaming (_⊔_ to _⊔Level_; suc to sucLevel; zero to zeroLevel) public
open import Size public

open import Relation.Binary.PropositionalEquality.Core public
open import Relation.Binary.PropositionalEquality hiding (setoid ; preorder ; decSetoid; [_]) public
open import Relation.Binary.Core using (Decidable) public

open import Relation.Nullary using (Dec) public
open import Relation.Nullary.Decidable using (⌊_⌋) public
