module GUIgeneric.GUIModelAdvanced where

open import GUIgeneric.Prelude renaming (inj₁ to secondButton; inj₂ to firstButton)

open import GUIgeneric.PreludeGUI renaming (WxColor to Color) hiding (IOInterfaceˢ)

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add) --; ComponentEls to Frame)
open import GUIgeneric.GUI
open import Data.Sum
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
-- open import StateSizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent
open import GUIgeneric.GUIExample -- hiding (HandlerGUIObject)
open import GUIgeneric.GUIModel
-- open IOInterfaceˢ public

open import Data.Product

infix 3 _goesThru_

_goesThru_  :  {s s' : ModelGuiState}(q : s -gui-> s')(t : ModelGuiState) → Set
_goesThru_  {s}  (execᵢ c f) t  =  s ≡ t ⊎ f _  goesThru t
_goesThru_  {s}  (returnᵢ a) t  =  s ≡ t
goesThruSelf : {s s' : ModelGuiState}(q : s -gui-> s') →  q goesThru s
goesThruSelf (execᵢ c f) = inj₁ refl
goesThruSelf (returnᵢ a) = refl


data  _-eventually->_ : (start final : ModelGuiState) → Set where
  hasReached :  {s : ModelGuiState} → s -eventually-> s
  next  :  {start final : ModelGuiState} (fornext :  (m :  modelGuiCommand start)
           → modelGuiNext start m -eventually-> final) → start -eventually-> final
