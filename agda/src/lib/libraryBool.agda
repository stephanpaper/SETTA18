module lib.libraryBool where


open import Data.Bool
open import Data.List
open import Data.Maybe
open import Level


boolFilter : {a : Level}{A : Set a} → (A → Bool) → List A → List A
boolFilter p = mapMaybe (λ x → if p x then just x else nothing)
