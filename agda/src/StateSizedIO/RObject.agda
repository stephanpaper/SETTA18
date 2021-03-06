
module StateSizedIO.RObject where

open import Data.Product
open import StateSizedIO.GUI.BaseStateDependent
-- open import StateSizedIO.Base public
{-
--  This definition was probably moved to StateSizedIO.Base
--  and by accident left here. Delete this.
record Interfaceˢ : Set₁ where
  field
    Stateˢ    : Set
    Methodˢ   : Stateˢ → Set
    Resultˢ   : (s : Stateˢ) → (m : Methodˢ s) → Set
    nextˢ     : (s : Stateˢ) → (m : Methodˢ s) → Resultˢ s m → Stateˢ
open Interfaceˢ public
-}

--\StateSizedRObjectRInterface
record RInterfaceˢ : Set₁ where
  field
    Stateˢ    :  Set
    Methodˢ   :  (s : Stateˢ) → Set
    Resultˢ   :  (s : Stateˢ) → (m : Methodˢ s) → Set
    nextˢ     :  (s : Stateˢ) → (m : Methodˢ s) → (r : Resultˢ s m) → Stateˢ
    RMethodˢ  :  (s : Stateˢ) → Set
    RResultˢ  :  (s : Stateˢ) → (m : RMethodˢ s) → Set

open RInterfaceˢ public



module _ (I : RInterfaceˢ)(let S = Stateˢ I) (let M = Methodˢ I)
         (let R = Resultˢ I) (let next = nextˢ I)
         (let RM = RMethodˢ I)
         (let RR = RResultˢ I)
          where
  -- A simple object just returns for a method the response
  -- and the object itself
--\StateSizedRObjectRObject
  record RObjectˢ (s : S) : Set where
    coinductive 
    field
      objectMethod  :  (m : M s) → Σ[ r ∈ R s m ] RObjectˢ (next s m r)
      readerMethod  :  (m : RM s) → RR s m
  open RObjectˢ public




-- Bisimilation for Objectˢ
{-
module Bisim (I : Interfaceˢ)
  (let S    = Stateˢ  I)
  (let M    = Methodˢ I)
  (let R    = Resultˢ I)
  (let next = nextˢ   I)
  (let O = Objectˢ I)
  where

    mutual

      record _≅_ {s : S} (o o' : O s) : Set where
        coinductive
        field bisimMethod : (m : M s) → objectMethod o m ≡×≅ objectMethod o' m

      data _≡×≅_ {s m} : (p p' :  Σ[ r ∈ R s m ] O (next s m r)) → Set where
        bisim : ∀{r} (let s' = next s m r) {o o' : O s'} (p : o ≅ o')
              → (r , o) ≡×≅ (r , o')

    open _≅_ public

    refl≅ : ∀{s} (o : O s) → o ≅ o
    bisimMethod (refl≅ o) m = bisim (refl≅ (proj₂ (objectMethod o m)))
-}
