
open import Data.Bool
open import Relation.Nullary
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
module GUIgeneric.GUIModelAdvancedExampleExtended  where

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


oneBtnFrame : String → Frame
oneBtnFrame str = addBtn str create-frame

frmExam : Frame
frmExam = oneBtnFrame "Examination"


frmPainKill : Frame
frmPainKill = oneBtnFrame "Prescribe Painkillers"

frmPreg : Frame
frmPreg = oneBtnFrame "Check for Preg"



frmXRay : Frame
frmXRay = oneBtnFrame "X-Ray"

frmTreatm : Frame
frmTreatm = oneBtnFrame "Treatment"

frmDecideCheckups : Frame
frmDecideCheckups = oneBtnFrame "Decide On Checkups"

frmFinished : Frame
frmFinished = addTxtBox "Finished" create-frame


data Sex : Set where
  male female : Sex

bool2Sex : Bool → Sex
bool2Sex true = female
bool2Sex false = male

string2Sex : String → Sex
string2Sex str = bool2Sex (str ==Str "f")

string2Bool : String → Bool
string2Bool str = (str ==Str "y")

mutual

 hdlExam : ∀ i → HandlerObject i frmExam
 hdlExam i .method {j} (btn , frm) =
   exec (putStrLn "Patient in Pain (y/n)?") λ _ →
   exec getLine λ s →
   hdlAnswerPain i (string2Bool s)

 hdlAnswerPain : (i : Size)(b : Bool)
                   → HandlerIOType i frmExam
 hdlAnswerPain i true =
        changeGUI frmPainKill propOneBtn (hdlPainKill i)
 hdlAnswerPain i false   = hdlCheckMaleFemale i

 hdlCheckMaleFemale : {str : String} (i : Size)
                       → HandlerIOType i (oneBtnFrame str)
 hdlCheckMaleFemale i =
   exec (putStrLn "Female or Male (f/m)?") λ _ →
   exec getLine λ s →
   hdlAnswerMaleFemale i (string2Sex s)

 hdlAnswerMaleFemale : (i : Size){str : String}(g : Sex)
                   → HandlerIOType i (oneBtnFrame str)
 hdlAnswerMaleFemale i female  =
        changeGUI frmPreg propOneBtn (hdlPreg i)
 hdlAnswerMaleFemale i male    =
        changeGUI frmXRay propOneBtn (hdlXRay i)

 hdlPainKill : ∀ i → HandlerObject i frmPainKill
 hdlPainKill i .method {j} (btn , frm) = hdlCheckMaleFemale i




 hdlPreg : ∀ i → HandlerObject i frmPreg
 hdlPreg i .method {j} (btn , frm) =
   changeGUI frmXRay propOneBtn (hdlXRay j)


 hdlXRay : ∀ i → HandlerObject i frmXRay
 hdlXRay i .method {j} (btn , frm) =
   changeGUI frmTreatm propOneBtn (hdlTreatm j)

 hdlTreatm : ∀ i →  HandlerObject i frmTreatm
 hdlTreatm i  .method {j} (btn , frm) =
   changeGUI frmDecideCheckups propOneBtn (hdlDecideCheckups j)

 hdlDecideCheckups : ∀ i →  HandlerObject i frmDecideCheckups
 hdlDecideCheckups i .method {j} (btn , frm) =
   changeGUI frmFinished propOneBtn (hdlFinished j)

 hdlFinished : ∀ i →  HandlerObject i frmFinished
 hdlFinished i .method {j} ()

main : NativeIO Unit
main = compileProgram  frmExam propOneBtn (hdlExam ∞)


stateExam : ModelGuiState
stateExam = state  frmExam propOneBtn
                    (hdlExam ∞) notStarted

stateExam₁ : (c : methodsG frmExam)  → ModelGuiState
stateExam₁ = modelGuiNext stateExam

stateExam₂ : (c : methodsG frmExam) (str : String)
              → ModelGuiState
stateExam₂ c str = modelGuiNext (stateExam₁ c) str


stateExamNoPain₁ : (c : methodsG frmExam)  → ModelGuiState
stateExamNoPain₁ c = (state frmExam propOneBtn (hdlExam ∞)
                      (started c
                       (exec' getLine λ str →
                         fmap ∞
                         (handlerReturnTypeToStateAndGuiObj
                         frmExam
                         propOneBtn (hdlExam ∞))
                        (hdlAnswerMaleFemale ∞ (string2Sex str)))))

stateExamNoPain₂ : (c : methodsG frmExam)
                   (str : String) → ModelGuiState
stateExamNoPain₂ c str = modelGuiNext (stateExamNoPain₁ c) str


statePreg : ModelGuiState
statePreg = state  frmPreg propOneBtn
                  (hdlPreg ∞) notStarted

statePainKill : ModelGuiState
statePainKill = state  frmPainKill propOneBtn
                  (hdlPainKill ∞) notStarted

statePainKill₁ : (c : methodsG frmPainKill)  → ModelGuiState
statePainKill₁ c = modelGuiNext statePainKill c

statePainKill₂ : (c : methodsG frmPainKill)
                 (str : String)  → ModelGuiState
statePainKill₂ c str = modelGuiNext (statePainKill₁ c) str



stateXRay : ModelGuiState
stateXRay = state  frmXRay propOneBtn
                  (hdlXRay ∞) notStarted


stateTreatm : ModelGuiState
stateTreatm = state  frmTreatm propOneBtn
                       (hdlTreatm ∞) notStarted





mutual

  examGoesThruXRay :
     (path : stateExam -gui-> stateTreatm)
     → path goesThru stateXRay
  examGoesThruXRay (execᵢ c f) =
         inj₂ (exam₁GoesThruXRay c (f _))
  examGoesThruXRay (returnᵢ () )

  exam₁GoesThruXRay : (c : methodsG frmExam)
                       (path : stateExam₁ c -gui-> stateTreatm)
                       → path goesThru stateXRay
  exam₁GoesThruXRay c (execᵢ str f) =
          inj₂ (exam₂GoesThruXRay c str (f _))
  exam₁GoesThruXRay c (returnᵢ ())

  exam₂GoesThruXRay :
      (c : methodsG frmExam) (str : String)
      (path : stateExam₂ c str -gui-> stateTreatm)
      → path goesThru stateXRay
  exam₂GoesThruXRay c str path with (string2Bool str)
  ...  |  true    =  painKillGoesThruXRay path
  ...  |  false   =  stateExamNoPain₁GoesThruXRay c path

  stateExamNoPain₁GoesThruXRay : (c : methodsG frmExam)
                                 (path : stateExamNoPain₁ c -gui-> stateTreatm)
                                 → path goesThru stateXRay
  stateExamNoPain₁GoesThruXRay c (execᵢ str f) =
                 inj₂ (stateExamNoPain₂GoesThruXRay c str (f _))
  stateExamNoPain₁GoesThruXRay c (returnᵢ ())

  stateExamNoPain₂GoesThruXRay : (c : methodsG frmExam)(str : String)
                                 (path : stateExamNoPain₂ c str -gui-> stateTreatm)
                                 → path goesThru stateXRay

  stateExamNoPain₂GoesThruXRay c str path with (string2Sex str)
  ... | male = XRayGoesThruXRay path
  ... | female = checkPregGoesThruXRay path

  painKillGoesThruXRay : (path : statePainKill -gui-> stateTreatm)
                               → path goesThru stateXRay
  painKillGoesThruXRay (execᵢ c f) = inj₂ (painKill₁GoesThruXRay c (f _))
  painKillGoesThruXRay (returnᵢ ())

  painKill₁GoesThruXRay : (c : methodsG frmPainKill)
                          (path : statePainKill₁ c -gui-> stateTreatm)
                          → path goesThru stateXRay
  painKill₁GoesThruXRay c (execᵢ str f) = inj₂ (painKill₂GoesThruXRay c str (f _))
  painKill₁GoesThruXRay c (returnᵢ ())

  painKill₂GoesThruXRay : (c : methodsG frmPainKill)
                          (str : String)
                          (path : statePainKill₂ c str -gui-> stateTreatm)
                          → path goesThru stateXRay
  painKill₂GoesThruXRay c str path with (string2Sex str)
  ... | male = XRayGoesThruXRay path
  ... | female = checkPregGoesThruXRay path




  checkPregGoesThruXRay : (path : statePreg -gui-> stateTreatm)
                               → path goesThru stateXRay
  checkPregGoesThruXRay (execᵢ c f) = inj₂ (XRayGoesThruXRay (f _))
  checkPregGoesThruXRay (returnᵢ ())

  XRayGoesThruXRay : (path : stateXRay -gui-> stateTreatm)
                      → path goesThru stateXRay
  XRayGoesThruXRay path = goesThruSelf path


mutual
  examEventuallyTreatm
          : stateExam -eventually-> stateTreatm
  examEventuallyTreatm =  next λ c →
                          exam₁EventuallyTreatm c

  exam₁EventuallyTreatm :  (c : methodsG frmExam) →
                            stateExam₁ c -eventually-> stateTreatm
  exam₁EventuallyTreatm  c = next λ str → exam₂EventuallyTreatm c str


  exam₂EventuallyTreatm :
       (c : methodsG frmExam)  (str : String)
       →  (stateExam₂ c str) -eventually-> stateTreatm
  exam₂EventuallyTreatm  c str with (string2Bool str)
  ...  |  true  =  painKillEventuallyTreatm
  ...  |  false  =  examNoPain₁EventuallyTreatm c

  painKillEventuallyTreatm : statePainKill -eventually-> stateTreatm
  painKillEventuallyTreatm = next λ c → painKill₁EventuallyTreatm c

  painKill₁EventuallyTreatm : (c : methodsG frmPainKill)
                              → statePainKill₁ c -eventually-> stateTreatm
  painKill₁EventuallyTreatm c = next λ str → painKill₂EventuallyTreatm  c str

  painKill₂EventuallyTreatm : (c : methodsG frmPainKill)
                              (str : String)
                              → statePainKill₂ c str -eventually-> stateTreatm
  painKill₂EventuallyTreatm  c str with (string2Sex str)
  ... | male   = xRayEventuallyTreatm
  ... | female = checkPregEventuallyTreatm


  examNoPain₁EventuallyTreatm : (c : methodsG frmExam)
                                → (stateExamNoPain₁ c) -eventually-> stateTreatm
  examNoPain₁EventuallyTreatm c = next λ str →
                                 examNoPain₂EventuallyTreatm c str

  examNoPain₂EventuallyTreatm : (c : methodsG frmExam)
                                (str : String)
                                → (stateExamNoPain₂ c str) -eventually-> stateTreatm
  examNoPain₂EventuallyTreatm  c str with (string2Sex str)
  ...  | male   = xRayEventuallyTreatm
  ...  | female = checkPregEventuallyTreatm



  checkPregEventuallyTreatm : statePreg -eventually-> stateTreatm
  checkPregEventuallyTreatm  = next λ c → xRayEventuallyTreatm

  xRayEventuallyTreatm : stateXRay -eventually-> stateTreatm
  xRayEventuallyTreatm  = next λ c → treatmEventuallyTreatm

  treatmEventuallyTreatm : stateTreatm -eventually-> stateTreatm
  treatmEventuallyTreatm  = hasReached
