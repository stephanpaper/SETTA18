{-# OPTIONS --sized-types --guardedness #-}
module GUIgeneric.GUIDefinitions where

open import GUIgeneric.Prelude

--open import GUIgeneric.PreludeGUI
open import StateSizedIO.GUI.WxBindingsFFI using (WxColor)
open import Relation.Binary.Definitions
-- open import Relation.Nary


open import Relation.Nullary

-- 1. Button
-- 2. Lable
-- 3. Textbox [TextInput] + mechanism to get String when button is pressed
--
data _⊎Comp_ {a b} (A : Set a) (B : Set b) : Set (a ⊔Level b) where
  button : (x : A) → A ⊎Comp B
  txtbox : (y : B) → A ⊎Comp B

data Direction : Set where
  left right : Direction


data Comp : Set where
  frame atomicComp : Comp


SubCompsIndex : Comp → Set
SubCompsIndex frame = ⊤
SubCompsIndex atomicComp = ⊥


data isSubComp : (c c' : Comp) → Set where
 buttonFrame  :  isSubComp  atomicComp frame



subComp : (c : Comp){c' : Comp}
         (is : isSubComp c' c) → Comp
subComp  .frame  {cButton}  buttonFrame  =  cButton




createParameters : Comp → Set
createParameters atomicComp = String ⊎Comp String
createParameters _ = ⊤

data IsOptimized : Set where
  optimized notOptimzed : IsOptimized


data CompEls (c : Comp) :  Set where
 createC  :  createParameters c → CompEls c
 add      :  {c' : Comp}(c'c : isSubComp c' c)
             (e' : CompEls c')(e : CompEls c)(isOpt : IsOptimized)
            → CompEls c


data _<c_  : {c c' : Comp}(e : CompEls c)(e' : CompEls c') → Set where
  addsub : {c' c : Comp}(c'c : isSubComp c' c)
           (e' : CompEls c')
           (e : CompEls c)
           (isOpt : IsOptimized)
           → e' <c add c'c e' e isOpt

  addlift : {c' c : Comp}(c'c : isSubComp c' c)
           (e' : CompEls c')
           (e : CompEls c)
           (isOpt : IsOptimized)
           → e <c add c'c e' e isOpt


data _<c+_  : {c c' : Comp}(e : CompEls c)(e' : CompEls c') → Set where
  in1 : {c c' : Comp} (e : CompEls c)(e' : CompEls c')
        (ee' : e <c e') → e <c+ e'
  in2 : {c c' c'' : Comp} (e : CompEls c)(e' : CompEls c')(e'' : CompEls c'')
        (ee' : e <c e')(e'e'' : e' <c+ e'') → (e <c+ e'')


data _<=c+_ : {c c' : Comp}(e : CompEls c)(e' : CompEls c') → Set where

  in0= : {c : Comp} (e : CompEls c)
        →  e <=c+ e
  in2= : {c c' c'' : Comp} (e : CompEls c)(e' : CompEls c')
                               (e'' : CompEls c'')
        →  e <c e' → e' <=c+ e'' → e <=c+ e''


in1= : {c c' : Comp} (e : CompEls c)(e' : CompEls c')
        (ee' : e <c e') → e <=c+ e'
in1= e e' ee' = in2= e e' e' ee' (in0= e')


trans<=c+ : {c c' c'' : Comp} (e : CompEls c)(e' : CompEls c')
                                   (e'' : CompEls c'')
            (ee' : e <=c+ e')
            (e'e'' : e' <=c+ e'')
            → e <=c+ e''
trans<=c+ {c} {.c} {c''} e .e e'' (in0= .e) e'e'' = e'e''
trans<=c+ {c} {c'} {c''} e e' e'' (in2= .e e'₁ .e' ee'₁ e'₁e') e'e'' = in2= e e'₁ e'' ee'₁ (trans<=c+ e'₁ e' e'' e'₁e' e'e'')


--
--  DEC Equality
--
module _ where
  sameOptimized : IsOptimized → IsOptimized → Bool
  sameOptimized optimized optimized = true
  sameOptimized notOptimzed notOptimzed = true
  sameOptimized _ _ = false

  _≟CompBool_ : {c c' : Comp} → CompEls c → CompEls c' → Bool
  _≟CompBool_ {frame} {frame} (add c₁c₂ c₁ c₂ isOpt) (add c₃c₄ c₃ c₄ isOpt') =
    (c₁ ≟CompBool c₃) ∧ (c₂ ≟CompBool c₄) ∧ (sameOptimized isOpt isOpt')

  _≟CompBool_ {atomicComp} {atomicComp} (add {frame} () _ _ _)
  _≟CompBool_ {atomicComp} {atomicComp} (add {atomicComp} () _ _ _)

  _≟CompBool_ {frame} {frame} (createC tt) (createC tt) = true
  _≟CompBool_ {atomicComp} {atomicComp} (createC (button x)) (createC (button y)) = x ==Str y
  _≟CompBool_ {atomicComp} {atomicComp} (createC (txtbox x)) (createC (txtbox y)) = x ==Str y

  _≟CompBool_ {atomicComp} {atomicComp} (createC (button x)) (createC (txtbox y)) = false
  _≟CompBool_ {atomicComp} {atomicComp} (createC (txtbox x)) (createC (button y)) = false

  _≟CompBool_ {frame} {atomicComp} _ _ = false
  _≟CompBool_ {atomicComp} {frame} _ _ = false

  createC _ ≟CompBool add _ _ _ _ = false
  add _ _ _ _ ≟CompBool createC _ = false


  unused = Dec

{- add buttonFrame a c notOptimzed ≡ add buttonFrame b d notOptimzedadd buttonFrame a c notOptimzed ≡ add buttonFrame b d notOptimzed -}
  lemmaAddEqProj1 : ∀ {a} {c} {opt} {b} {d} {opt'} → add buttonFrame a c opt ≡ add buttonFrame b d opt' → a ≡ b
  lemmaAddEqProj1 refl = refl

  lemmaAddEqProj2 : ∀ {a} {c} {opt} {b} {d} {opt'} → add buttonFrame a c opt ≡ add buttonFrame b d opt' → c ≡ d
  lemmaAddEqProj2 refl = refl


  lemmaCreateCBtnEq : ∀ {s1} {s2} → ((createC (button s1))  ≡ (createC (button s2))) → (s1 ≡ s2)
  lemmaCreateCBtnEq refl = refl

  lemmaCreateCTxtbxEq : ∀ {s1} {s2} → ((createC (txtbox s1))  ≡ (createC (txtbox s2))) → (s1 ≡ s2)
  lemmaCreateCTxtbxEq refl = refl


  mutual
   _≟CompFr_ : Decidable {A = CompEls frame} _≡_
   createC tt ≟CompFr createC tt = yes refl
   createC tt ≟CompFr add  _ _ _ _ = no (λ ())
   add _ _ _ _ ≟CompFr createC _ = no (λ ())
   add _ _ _ optimized ≟CompFr add _ _ _ notOptimzed = no (λ ())
   add _ _ _ notOptimzed ≟CompFr add _ _ _ optimized =  no (λ ())

   add buttonFrame a c optimized ≟CompFr add buttonFrame b d optimized with (a ≟Comp b) | (c ≟Comp d)
   ... | yes p | yes q = yes (cong₂ (λ x y → add buttonFrame x y optimized ) p q)
   ... | yes p | no ¬p = no (λ addp → ¬p (lemmaAddEqProj2 addp))
   ... | no ¬p | _ = no ((λ addp → ¬p (lemmaAddEqProj1 addp)))



   add buttonFrame a c notOptimzed ≟CompFr add buttonFrame b d notOptimzed with (a ≟Comp b) | (c ≟Comp d)
   ... | yes p | yes q = yes (cong₂ (λ x y → add buttonFrame x y notOptimzed ) p q)
   ... | yes p | no ¬p = no (λ addp → ¬p (lemmaAddEqProj2 addp))
   ... | no ¬p | q = no ((λ addp → ¬p (lemmaAddEqProj1 addp)))

   _≟Comp_ : {c : Comp} → Decidable {A = CompEls c} _≡_

   _≟Comp_ (createC _) (add _ _ _ isOpt) = no (λ ())
   _≟Comp_ (add _ _ _ isOpt) (createC _) = no (λ ())

   _≟Comp_ {atomicComp} (add () a b isOpt) (add cd c d isOpt')

   _≟Comp_ {frame} (createC tt) (createC tt) = yes refl

   _≟Comp_ {atomicComp} (createC (button s1)) (createC (button s2)) with (s1 ≟Str s2)
   ... | yes p = yes (cong (createC ∘ button) p)
   ... | no q = no  (λ neq →   q  (lemmaCreateCBtnEq neq)  )

   _≟Comp_ {atomicComp} (createC (txtbox s1)) (createC (txtbox s2)) with (s1 ≟Str s2)
   ... | yes p = yes (cong (createC ∘ txtbox) p)
   ... | no q = no (λ neq →   q  (lemmaCreateCTxtbxEq neq)  )


   _≟Comp_ {atomicComp} (createC (button s1)) (createC (txtbox s2)) = no (λ ())
   _≟Comp_ {atomicComp} (createC (txtbox s1)) (createC (button s2)) = no (λ ())


   _≟Comp_ {frame} (add c'c x x₁ isOpt) (add c'c₁ y y₁ isOpt₁) =
       _≟CompFr_ (add c'c x x₁ isOpt) (add c'c₁ y y₁ isOpt₁)




create-frame : CompEls frame
create-frame = createC{frame} tt

create-button : (s : String) → CompEls atomicComp
create-button s = createC{atomicComp} (button s)

create-txtbox : (s : String) → CompEls atomicComp
create-txtbox s = createC{atomicComp} (txtbox s)


validAdd : (c c' : Comp) → Set
validAdd atomicComp frame = ⊤
validAdd _ _ = ⊥

addReturnType : (c c' : Comp){_ : validAdd c c'} → Set
addReturnType atomicComp frame = CompEls frame
addReturnType frame frame {()}
addReturnType frame atomicComp {()}
addReturnType atomicComp atomicComp {()}


add' : {c c' : Comp}{va : validAdd c c'} → CompEls c → CompEls c'
      → (isOpt : IsOptimized) → addReturnType c c'{va}
add' {atomicComp} {frame} bt fr isOpt = add buttonFrame bt fr isOpt
add' {frame} {frame} {()} isOpt
add' {frame} {atomicComp} {()} isOpt
add' {atomicComp} {atomicComp} {()} isOpt


properties : {c : Comp}(e : CompEls c) → Set
properties {c} (add c'c e e' isOpt) = properties e × properties e'
properties {frame} (createC x) = (ℕ × ℕ × ℕ × ℕ)
properties {atomicComp} (createC x) = WxColor


ComponentEls : Comp → Set
ComponentEls = CompEls

Component : Set
Component = Comp
