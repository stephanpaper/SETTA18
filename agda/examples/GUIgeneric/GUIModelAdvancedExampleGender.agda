
open import Data.Bool
open import Relation.Nullary
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
module GUIgeneric.GUIModelAdvancedExampleGender  where

open import GUIgeneric.Prelude renaming (inj₁ to secondButton; inj₂ to firstButton)
open import GUIgeneric.PreludeGUI renaming (WxColor to Color) hiding (IOInterfaceˢ)

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExample using (oneColumnLayout;propOneBtn)
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)

open import GUIgeneric.GUIModel
open import GUIgeneric.GUIModelAdvanced
open import Data.Sum
open import GUIgeneric.GUIExample using (addTxtBox; black; changeGUI)
                                  renaming (addButton to addBtn)

postulate btn  :  FFIButton
postulate fr   :  FFIFrame
-- private postulate strExample : String

--
-- This exmaple also works with interactivity:
--    first step is "check gender"
--    doctor enters gender
--


frmExam : Frame
frmExam = addBtn "Examination"  create-frame

-- prop1BtnFrm : Color × ℕ × ℕ × ℕ × ℕ
-- prop1BtnFrm = black , oneColumnLayout

{-
propFrmExam  :  Color × ℕ × ℕ × ℕ × ℕ
propFrmExam  =  black , oneColumnLayout
-}

frmPreg : Frame
frmPreg = addBtn "Check for Preg"  create-frame



frmXRay : Frame
frmXRay = addBtn "X-Ray" create-frame

frmTreatm : Frame
frmTreatm = addBtn "Treatment" create-frame

frmFinished : Frame
frmFinished = addTxtBox "Finished" create-frame


{-
propFrmXRay = propFrmExam
propFrmTreatm = propFrmExam
propFrmPreg = propFrmExam
propFrmFinished = propFrmExam
-}

data Sex : Set where
  male female : Sex

bool2Sex : Bool → Sex
bool2Sex true = female
bool2Sex false = male

string2Sex : String → Sex
string2Sex str = bool2Sex (str ==Str "Female")

mutual

 hdlExam : ∀ i → HandlerObject i frmExam
 hdlExam i .method {j} (btn , frm) =
   exec (putStrLn "Female or Male?") λ _ →
   exec getLine λ s →
   hdlExamProgEnd i (string2Sex s)

 hdlExamProgEnd : (i : Size)(g : Sex) → HandlerIOType i frmExam
 hdlExamProgEnd i female  =  changeGUI frmPreg propOneBtn (hdlPreg i)
 hdlExamProgEnd i male    =  changeGUI frmXRay propOneBtn (hdlXRay i)

-- propFrmPreg
-- propFrmXRay

 hdlPreg : ∀ i → HandlerObject i frmPreg
 hdlPreg i .method {j} (btn , frm) =
   changeGUI frmXRay propOneBtn (hdlXRay j)  -- propFrmXRay


 hdlXRay : ∀ i → HandlerObject i frmXRay
 hdlXRay i .method {j} (btn , frm) =
   changeGUI frmTreatm propOneBtn (hdlTreatm j) -- propFrmXRay

 hdlTreatm : ∀ i →  HandlerObject i frmTreatm
 hdlTreatm i  .method {j} (btn , frm) =
   changeGUI frmFinished propOneBtn (hdlFinished j) -- propFrmFinished

 hdlFinished : ∀ i →  HandlerObject i frmFinished
 hdlFinished i .method {j} ()

main : NativeIO Unit
main = compileProgram  frmExam propOneBtn (hdlExam ∞) -- propFrmExam

-- states

stateExam : ModelGuiState
stateExam = state  frmExam propOneBtn (hdlExam ∞) notStarted

stateExam₁ : (c : methodsG frmExam)  → ModelGuiState
stateExam₁ = modelGuiNext stateExam

stateExam₂ : (c : methodsG frmExam) (str : String) → ModelGuiState
stateExam₂ c str = modelGuiNext (stateExam₁ c) str

-- propFrmExam

statePreg : ModelGuiState
statePreg = state  frmPreg propOneBtn  -- propFrmPreg
                  (hdlPreg ∞) notStarted


stateXRay : ModelGuiState
stateXRay = state  frmXRay propOneBtn -- propFrmXRay
                  (hdlXRay ∞) notStarted


stateTreatm : ModelGuiState
stateTreatm = state  frmTreatm propOneBtn -- propFrmTreatm
                       (hdlTreatm ∞) notStarted




mutual

  examGoesThruXRay : (path : stateExam -gui-> stateTreatm) → path goesThru stateXRay
  examGoesThruXRay (execᵢ c f) = inj₂ (exam₁GoesThruXRay c (f _))
  examGoesThruXRay (returnᵢ () )

  exam₁GoesThruXRay : (c : methodsG frmExam)
                       (path : stateExam₁ c -gui-> stateTreatm)
                       → path goesThru stateXRay
  exam₁GoesThruXRay c (execᵢ str f) =
          inj₂ (exam₂GoesThruXRay c str (f _))
  exam₁GoesThruXRay c (returnᵢ ())

  exam₂GoesThruXRay : (c : methodsG frmExam) (str : String)
    (path : stateExam₂ c str -gui-> stateTreatm) → path goesThru stateXRay
  exam₂GoesThruXRay c str path with (string2Sex str)
  ...  |  male    =  XRayGoesThruXRay path
  ...  |  female  =  checkPregGoesThruXRay path




  checkPregGoesThruXRay : (path : statePreg -gui-> stateTreatm) → path goesThru stateXRay
  checkPregGoesThruXRay (execᵢ c f) = inj₂ (XRayGoesThruXRay (f _))
  checkPregGoesThruXRay (returnᵢ ())

  XRayGoesThruXRay : (path : stateXRay -gui-> stateTreatm)
                      → path goesThru stateXRay
  XRayGoesThruXRay path = goesThruSelf path


mutual
  examEventuallyTreatm : stateExam -eventually-> stateTreatm
  examEventuallyTreatm = next λ c → exam₁EventuallyTreatm c

  exam₁EventuallyTreatm :  (c : methodsG frmExam) →
                            stateExam₁ c -eventually-> stateTreatm
  exam₁EventuallyTreatm  c = next λ str → exam₂EventuallyTreatm c str


  exam₂EventuallyTreatm : (c : methodsG frmExam)  (str : String)
       →  (stateExam₂ c str) -eventually-> stateTreatm
  exam₂EventuallyTreatm  c str with (string2Sex str)
  ...  |  female  =  checkPregEventuallyTreatm
  ...  |  male    =  xRayEventuallyTreatm



  checkPregEventuallyTreatm : statePreg -eventually-> stateTreatm
  checkPregEventuallyTreatm  = next λ c → xRayEventuallyTreatm

  xRayEventuallyTreatm : stateXRay -eventually-> stateTreatm
  xRayEventuallyTreatm  = next λ c → treatmEventuallyTreatm

  treatmEventuallyTreatm : stateTreatm -eventually-> stateTreatm
  treatmEventuallyTreatm  = hasReached
