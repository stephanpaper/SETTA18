open import Data.Bool

module GUIgeneric.GUIExampleInfiniteBtnsGUIdatatype   where

open import GUIgeneric.Prelude renaming (inj₁ to secondBtn; inj₂ to firstBtn) hiding (show)
open import GUIgeneric.PreludeGUI renaming (WxColor to Color) hiding ( _>>_) -- hiding (addButton)


open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib renaming (addButton to addButton')
open import GUIgeneric.GUIExample  hiding (main; changeGUI)
open import Data.Nat.Show
open import Data.Product
open import heap.libraryNat renaming (_≧ℕb_ to _≧_)

open import Data.Nat renaming (_∸_ to _-_)

-- addButton : String → Frame → Frame
-- addButton str fr = addButton' str fr notOptimzed

guifullToReturnType : ∀ {i} {g} → GUI {i} → returnType g
guifullToReturnType f = changedGUI (f .defFrame) (f .property)

guifullToReturnType' : ∀ {i} {g} → GUI {i} →
                       Σ[ r ∈ returnType g ]
                       (IOObjectˢ GuiInterface handlerInterface i
                           (nextStateFrame g r))
guifullToReturnType' {i} {g} f = guifullToReturnType f , f .obj

changeGUI : ∀ {i} {g} → GUI {i} →
                       IO GuiInterface ∞ (Σ[ r ∈ returnType g ]
                       (IOObjectˢ GuiInterface handlerInterface i
                           (nextStateFrame g r)))
changeGUI  f = return (guifullToReturnType' f)



nFrame : (n : ℕ) → Frame
nFrame 0        =  create-frame
nFrame (suc n)  =  addButton (show n) (nFrame n)

nProp : (n : ℕ) → properties (nFrame n)
nProp 0        =  oneColumnLayout
nProp (suc n)  =  (black , nProp n)

nGUI : ∀{i} → (n : ℕ) → GUI {i}
nGUI n .defFrame        =  nFrame n
nGUI n .property        =  nProp n
nGUI n .obj .method m   =  changeGUI (nGUI (suc n))

main : NativeIO Unit
main = compileGUI (nGUI 1)
