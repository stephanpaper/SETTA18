open import Data.Bool

module GUIgeneric.GUIExampleInfiniteBtnsAdvanced   where

open import GUIgeneric.Prelude renaming (inj₁ to secondBtn; inj₂ to firstBtn) hiding (show)

open import GUIgeneric.PreludeGUI renaming (WxColor to Color) hiding (_>>_) -- hding (addButton)



open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib renaming (addButton to addButton')
open import GUIgeneric.GUIExample  hiding (main)
open import Data.Nat.Show
open import Data.Product
open import heap.libraryNat renaming (_≧ℕb_ to _≧_)

open import Data.Nat renaming (_∸_ to _-_)

-- example with infinitely many buttons, and the nth button
--  adds n new buttons

--addButton : String → Frame → Frame
--addButton str fr = addButton' str fr notOptimzed

addButtonNonopt : String → Frame → Frame
addButtonNonopt str fr = addButton' str fr notOptimzed

nFrame : (n : ℕ) → Frame
nFrame 0 = create-frame
nFrame (suc n) = addButtonNonopt (show (suc n)) (nFrame n)

propn : (n : ℕ) → properties (nFrame n)
propn zero = (1 , 10 , 2 , 2) --oneColumnLayout
propn (suc n) = black , (propn n)

mutual
  objnadd : ∀ {j} → (n m : ℕ) → IO GuiInterface ∞ (Σ[ r ∈ returnType (nFrame n ) ] (HandlerObject j (nextStateFrame (nFrame n) r)))
  objnadd n m = return (changedGUI (nFrame (n + m)) (propn (n + m)) , objnaux (n + m))

  objnTom : (n : ℕ) → (m : ℕ) → (methods (nFrame n) (nFrame m)) → ℕ
  objnTom zero k ()
  objnTom (suc n) k (secondBtn x) = 0
  objnTom (suc n) k (firstBtn y) = suc (objnTom n k y)



  objnaux : ∀ {j} → (n : ℕ) → IOObjectˢ GuiInterface
                                  handlerInterface j (nFrame n)
  objnaux {j} n .method {j'} m = objnadd {j'} n (n ∸ objnTom n n m) -- return (changedGUI (nFrame (suc n)) (propn (suc n)) , objnaux (suc n))


main : NativeIO Unit
main = compileProgram (nFrame 1) (propn 1) (objn 1)
  where
     objn : ∀ {j} → (n : ℕ) → HandlerObject j (nFrame n)
     objn n .method x = objnadd n (n ∸ objnTom n n x)
