{-# OPTIONS --sized-types --guardedness #-}
module GUIgeneric.Prelude where

open import Data.Bool public hiding (_<_;_<?_)
open import Data.Empty public
open import Data.List public hiding (align;alignWith;fromMaybe;zip;zipWith)
open import Data.Maybe.Base hiding (map;_>>=_) public
open import Data.Nat hiding (_≟_; _≤_; _≤?_) public
open import Data.Product hiding (map; zip;assocʳ;assocˡ) public
open import Data.String hiding (concat;length;replicate;_<_;_<?_;_≤_;head;intersperse;linesBy;tail;uncons;wordsBy) renaming (_++_ to _++Str_; _==_ to _==Str_; _≟_ to _≟Str_) public
open import Data.Sum public hiding (map;swap;map₁;map₂)
open import Data.Unit hiding (_≟_; decSetoid; setoid;_≤_;_≤?_) public

open import Function public hiding (force)
open import Level renaming (_⊔_ to _⊔Level_; suc to sucLevel; zero to zeroLevel) public
open import Size public

open import Relation.Binary.PropositionalEquality.Core public
open import Relation.Binary.PropositionalEquality hiding (setoid ; preorder ; decSetoid; [_]) public
-- open import Relation.Binary.Core using (Decidable) public

open import Relation.Nullary using (Dec) public
open import Relation.Nullary.Decidable using (⌊_⌋) public
