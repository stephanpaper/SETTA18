module StateSizedIO.LIB.library where

open import Data.Bool.Base
open import Data.String.Base hiding (length)
open import Function
open import Data.String renaming (_++_ to _++Str_) hiding (length)
open import Data.List
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)

open import Agda.Builtin.Char
open import Data.Maybe hiding (map)

open import Category.Monad
open import Category.Monad.Indexed



open import NativeIO


elemStr : String → List String → Bool
elemStr = any ∘ primStringEquality

concatStr : List String → String
concatStr = foldr _++Str_ ""

-- concatIntersperse ", " ("hey" ∷ "there" ∷ []) ==> "hey, there"
concatIntersperse : (x : String) (y : List String) → String
concatIntersperse intersperseStr list = concatStr (intersperse intersperseStr list)



open import Data.Char
open import Data.Nat

charToDecDigitNat : Char -> ℕ
charToDecDigitNat c = (toNat c) ∸ 48

readNat : List Char -> ℕ                 -- convert from decimal digit chars
readNat =  toN ∘ map charToDecDigitNat ∘ reverse
           where
           toN : List ℕ -> ℕ
           toN []       = 0
           toN (j ∷ js) = j + (10 * (toN js))

isDigit : Char → Bool
isDigit = primIsDigit

strIsNatNumber : String → Bool
strIsNatNumber s = all isDigit (toList s)


stringToNat : String → Maybe ℕ
stringToNat s with (strIsNatNumber s)
... | true = just ((readNat ∘ toList) s)
... | false = nothing


nth : {A : Set} → (l : List A) → Fin (length l) → A
nth [] ()
nth (a ∷ l) zero = a
nth (a ∷ l) (suc n) = nth l n


ioMonad : RawMonad NativeIO
RawIMonad.return ioMonad = nativeReturn
RawIMonad._>>=_ ioMonad = _native>>=_
