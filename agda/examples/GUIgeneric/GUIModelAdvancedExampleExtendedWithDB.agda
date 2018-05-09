open import Data.Bool
open import Relation.Nullary
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
module GUIgeneric.GUIModelAdvancedExampleExtendedWithDB  where

open import GUIgeneric.Prelude renaming (inj₁ to secondButton; inj₂ to firstButton)
open import GUIgeneric.PreludeGUIWithDBTmp renaming (WxColor to Color) hiding (IOInterfaceˢ)

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUIWithDB
open import GUIgeneric.GUIExampleWithDB using (oneColumnLayout;propOneBtn)
open import GUIgeneric.GUIExampleLibWithDB
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)

open import GUIgeneric.GUIModelWithDB
open import GUIgeneric.GUIModelAdvancedWithDB
open import Data.Sum hiding (map)
open import GUIgeneric.GUIExampleWithDB using (addTxtBox; black; changeGUI)
                                  renaming (addButton to addBtn)

open import Data.Integer
open import Data.Fin

-- DB imports
--
open import StateSizedIO.LIB.DB.Schema
open import StateSizedIO.LIB.DB.Serialization
open import StateSizedIO.LIB.DB.Query
open import  StateSizedIO.LIB.DB.Interface
open import StateSizedIO.LIB.HDBC.HDBC


--
-- Database
--
dbFile : String
dbFile = "/tmp/patients.db"


patientTable : TableType
patientTable = ("name"   , string , notNull  , isPrimKey) ∷
               ("gender" , string , notNull  , notPrimKey) ∷
               ("pain"   , string , notNull  , notPrimKey) ∷
               []


patientSchema : Schema
patientSchema = ("patients" , patientTable) ∷
                []

onlyTable : Fin 1
onlyTable = zero

--
-- Low level DB
--
createTables : Connection → NativeIO Unit
createTables conn =
  -- drop tables
  dropTableIfExisits conn "patients"       native>>= λ _ →

  nativeRun conn "CREATE TABLE patients (
	name STRING NOT NULL,
        gender STRING NOT NULL,
        pain STRING NOT NULL,
	PRIMARY KEY(name))"
        [] native>>= λ _ →

  nativeReturn _


insertPatientData : Connection → NativeIO Unit
insertPatientData conn = insertRows conn patientSchema onlyTable list
  where
    list : List (String × String × String × ⊤)
    list = ("Isabelle" , "f" , "n" , tt) ∷
           ("Mary"     , "f" , "y" , tt) ∷
           ("Peter"    , "m" , "y" , tt) ∷
           ("John"     , "m" , "n" , tt) ∷
           []

PatientTuples : Set
PatientTuples = List (String × String × String)




getPatientFromDB : (name : String) →
                    IO GuiLev1Interface ∞ (Maybe (String × String)) -- (List (List (String × SqlVal)))
getPatientFromDB = (\ (name : String) →
    exec (dbCmd (connect dbFile)) λ conn →
    exec (dbCmd (prepare conn ("SELECT * from patients where name = '" ++Str name ++Str "'"))) λ statement →
    exec (dbCmd (execute statement [])) λ _ →
    exec (dbCmd (fetchAllRowsAL' statement)) λ res →

    exec (dbCmd (printList res)) λ _ →
    return (convert res)-- res
    )
    where
    convert : List (List (String × SqlVal)) → Maybe (String × String)  -- gender × pain
    convert [] = nothing
    convert ([] ∷ xs₁) = nothing
    convert ((x ∷ []) ∷ xs₁) = nothing
    convert ((x ∷ x₁ ∷ []) ∷ xs₁) = nothing
    convert (((fieldname1 , value1) ∷ (fieldname2 , value2) ∷ (fieldname3 , value3) ∷ xs) ∷ xs₁) = just (toStringSqlVal  value2 , toStringSqlVal value3)

{- ([] ∷ []) = {!!}
    convert (((fieldName , valueGender) ∷ (fieldName , valueGender) ∷ []) ∷ xs) = {!xs!}
-}

maybeStringString2Sting1 : Maybe (String × String) → Maybe String
maybeStringString2Sting1 (just (s0 , s1)) = just s0
maybeStringString2Sting1 nothing = nothing

maybeStringString2Sting2 : Maybe (String × String) → Maybe String
maybeStringString2Sting2 (just (s0 , s1)) = just s1
maybeStringString2Sting2 nothing = nothing

getGenderFromDB : (name : String) →
                    IO GuiLev1Interface ∞ (Maybe String)
getGenderFromDB name = getPatientFromDB name >>= λ s →
                       return (maybeStringString2Sting1 s)


getPainInfoFromDB : (name : String) →
                    IO GuiLev1Interface ∞ (Maybe String)
getPainInfoFromDB name = getPatientFromDB name >>= λ s →
                       return (maybeStringString2Sting2 s)
--
--  START  GUI   CODE
--
--

postulate btn  :  FFIButton
postulate fr   :  FFIFrame
-- private postulate strExample : String


frmBtnTxtBox : Frame
frmBtnTxtBox = addBtn "OK" (addTxtBox "Enter Name" create-frame)

-- mypropBtnTxtBox' : properties frmBtnTxtBox
-- mypropBtnTxtBox' : black , propOneBtn

oneBtnFrame : String → Frame
oneBtnFrame str = addBtn str create-frame

frmExam : Frame
frmExam = oneBtnFrame "Examination"

frmErrorPain : Frame
frmErrorPain = oneBtnFrame "Error in Db - no pain info"


frmErrorGender : Frame
frmErrorGender = oneBtnFrame "Error in Db - no gender info"



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
 hdlErrorPain : ∀ i → (name : String) → HandlerObject i frmErrorPain
 hdlErrorPain i name .method {j} (btn , frm) =
     changeGUI frmBtnTxtBox (black , propOneBtn) (hdlBtnTxtBox j)-- frmExam propOneBtn (hdlExam j name)

 hdlErrorGender : ∀ i → (name : String) → HandlerObject i frmErrorGender
 hdlErrorGender i name .method {j} (btn , frm) =
     changeGUI frmBtnTxtBox (black , propOneBtn) (hdlBtnTxtBox j)-- frmExam propOneBtn (hdlExam j name)
--     changeGUI frmExam propOneBtn (hdlExam j name)

 hdlBtnTxtBox : ∀ i → HandlerObject i frmBtnTxtBox
 hdlBtnTxtBox i .method {j} (btn , ffitxtbox , frm) =
   exec (getTextFromTxtBox ffitxtbox) λ name →
   exec (putStrLn name) λ _ →
   changeGUI frmExam propOneBtn (hdlExam i name)
--   return (noChange , hdlBtnTxtBox j)


 hdlExam : ∀ i → (name : String) → HandlerObject i frmExam
 hdlExam i name .method {j} (btn , frm) =
--   exec (putStrLn "Patient in Pain (y/n)?") λ _ →
--   exec getLine λ s →
     getPainInfoFromDB name
     >>= λ {(just pain)  →
                hdlAnswerPain i name (string2Bool pain) ;
            nothing → changeGUI frmErrorPain propOneBtn (hdlErrorPain i name) }

 hdlAnswerPain : (i : Size)(name : String)(b : Bool)
                   → HandlerIOType i frmExam
 hdlAnswerPain i name true =
        changeGUI frmPainKill propOneBtn (hdlPainKill i name)
 hdlAnswerPain i name false   = hdlCheckMaleFemale i name

 hdlCheckMaleFemale : {str : String} (i : Size) (name : String)
                       → HandlerIOType i (oneBtnFrame str)
 hdlCheckMaleFemale i name =
--   exec (putStrLn "Female or Male (f/m)?") λ _ →
--    exec getLine λ s →
    getGenderFromDB name
   >>= λ {(just gender) →
             hdlAnswerMaleFemale i name (string2Sex gender);
          nothing → changeGUI frmErrorGender propOneBtn (hdlErrorGender i name) }

--   hdlAnswerMaleFemale i name (string2Sex s)

 hdlAnswerMaleFemale : (i : Size){str : String}(name : String)(g : Sex)
                   → HandlerIOType i (oneBtnFrame str)
 hdlAnswerMaleFemale i name female  =
        changeGUI frmPreg propOneBtn (hdlPreg i name )
 hdlAnswerMaleFemale i name male    =
        changeGUI frmXRay propOneBtn (hdlXRay i name)

 hdlPainKill : ∀ i → (name : String) → HandlerObject i frmPainKill
 hdlPainKill i name .method {j} (btn , frm) = hdlCheckMaleFemale i name




 hdlPreg : ∀ i → (name : String) → HandlerObject i frmPreg
 hdlPreg i name .method {j} (btn , frm) =
   changeGUI frmXRay propOneBtn (hdlXRay j name)


 hdlXRay : ∀ i → (name : String) → HandlerObject i frmXRay
 hdlXRay i name .method {j} (btn , frm) =
   changeGUI frmTreatm propOneBtn (hdlTreatm j name)

 hdlTreatm : ∀ i →  (name : String) → HandlerObject i frmTreatm
 hdlTreatm i  name .method {j} (btn , frm) =
   changeGUI frmDecideCheckups propOneBtn (hdlDecideCheckups j name)

 hdlDecideCheckups : ∀ i →  (name : String) → HandlerObject i frmDecideCheckups
 hdlDecideCheckups i name .method {j} (btn , frm) =
     changeGUI frmBtnTxtBox (black , propOneBtn) (hdlBtnTxtBox j)


 hdlFinished : ∀ i →  (name : String) → HandlerObject i frmFinished
 hdlFinished i name .method {j} ()




prepareDB : NativeIO Unit
prepareDB =

  -- connect
  nativeConnectDB dbFile    native>>= λ conn →

  createTables conn native>>= λ _ →

  insertPatientData conn native>>= λ _ →

  nativeReturn _


main : NativeIO Unit
main = prepareDB native>>= λ _ →
       compileProgram  frmBtnTxtBox (black , propOneBtn) (hdlBtnTxtBox ∞)



{-
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
-}
