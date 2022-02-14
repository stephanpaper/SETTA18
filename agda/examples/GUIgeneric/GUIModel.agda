{-# OPTIONS --sized-types --guardedness  #-}
module GUIgeneric.GUIModel where

open import GUIgeneric.Prelude renaming (inj₁ to secondButton; inj₂ to firstButton)

open import GUIgeneric.PreludeGUI renaming (WxColor to Color) hiding (IOInterfaceˢ)

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add) --; ComponentEls to Frame)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods
-- open import StateSizedIO.Base
open import StateSizedIO.GUI.BaseStateDependent
open import GUIgeneric.GUIExample -- hiding (HandlerGUIObject)

open IOInterfaceˢ public

open import Data.Product

-- How many trivial io commands such as putStrLn are ignored in the model
skippedIOcmds : ℕ
skippedIOcmds = 2

data MethodStarted (f : Frame) (prop : properties f)
                   (obj : HandlerObject ∞ f) : Set where
   notStarted : MethodStarted f prop obj
   started :    (m    : methodsG f) (pr : IO' GuiInterface ∞ StateAndGuiObj)
                → MethodStarted f prop obj

data ModelGuiState : Set where
   state : (f       : Frame) (prop    : properties f) (obj     : HandlerObject ∞ f)
           (m       : MethodStarted f prop obj) → ModelGuiState

modelGuiCommand : (s : ModelGuiState) → Set
modelGuiCommand  (state g prop obj notStarted)               =  methodsG g
modelGuiCommand  (state g prop obj (started m (exec' c f)))  =  GuiResponse c
modelGuiCommand  (state g prop obj (started m (return' a)))  =  ⊤

-- modelGuiResponse : Set
-- modelGuiResponse = ⊤

handlerReturnTypeToStateAndGuiObj :
          (g       : Frame)
          (prop    : properties g)
          (obj     : HandlerObject ∞ g)
          (res :  Σ[ r ∈ returnType g ]
                  IOObjectˢ GuiInterface handlerInterface ∞ (nextStateFrame g r))
           → StateAndGuiObj
handlerReturnTypeToStateAndGuiObj g prop obj (noChange , obj') = g , prop , obj'
handlerReturnTypeToStateAndGuiObj g prop obj (changedAttributes prop' , obj') = g , prop' , obj'
handlerReturnTypeToStateAndGuiObj g prop obj (changedGUI g' prop' , obj') = g' , prop' , obj'

intermediateProg2ModelState : (g : Frame)
                              (prop : properties g)
                              (obj  : HandlerObject ∞ g)
                              (prog : HandlerIOType ∞  g)
                              → IO GuiInterface ∞  StateAndGuiObj
intermediateProg2ModelState g prop obj prog =
  fmap ∞ (handlerReturnTypeToStateAndGuiObj g prop obj ) prog


modelGuiNextProgramStarted : (g : Frame)
                             (prop : properties g)
                             (obj  : HandlerObject ∞ g)
                             (m    : methodsG g)
                             → IO GuiInterface ∞ StateAndGuiObj
modelGuiNextProgramStarted g prop obj m =
     intermediateProg2ModelState g prop obj (obj .method m)


modelGuiNextProgramStarted' : (g : Frame)
                             (prop : properties g)
                             (obj  : HandlerObject ∞ g)
                             (m    : methodsG g)
                             → IO' GuiInterface ∞ StateAndGuiObj
modelGuiNextProgramStarted' s prop obj m = force (modelGuiNextProgramStarted s prop obj m)


modelGuiNextaux : (g : Frame)(prop : properties g)(obj : HandlerObject ∞ g)
                  (m : methodsG g)(pr : IO' GuiInterface ∞ StateAndGuiObj)
                  (skippedCms : ℕ)
                  → ModelGuiState
modelGuiNextaux g prop obj m (exec' (putStrLn s) f) (suc n) =
    modelGuiNextaux g prop obj m (force (f _)) n
modelGuiNextaux g prop obj m (exec' c' f) n =
        state g prop obj (started m (exec' c' f))
modelGuiNextaux g prop obj m (return' (gNew , propNew , objNew)) n =
        state gNew propNew objNew notStarted

modelGuiNext : (s : ModelGuiState) (c : modelGuiCommand s) → ModelGuiState
modelGuiNext (state g prop obj notStarted) m     =
       modelGuiNextaux g prop obj m  (modelGuiNextProgramStarted' g prop obj m) skippedIOcmds
modelGuiNext (state g prop obj (started m (exec' c' f))) c =
       modelGuiNextaux g prop obj m (force (f c)) skippedIOcmds
modelGuiNext (state g prop obj (started m (return' (gNew , propNew , objNew)))) c =
       state gNew propNew objNew notStarted

modelGuiInterface : IOInterfaceˢ
modelGuiInterface  .Stateˢ            =  ModelGuiState
modelGuiInterface  .Commandˢ          =  modelGuiCommand
modelGuiInterface  .Responseˢ  s m    =  ⊤
modelGuiInterface  .nextˢ      s m r  =  modelGuiNext s m

_-gui->_ : (s s' : ModelGuiState ) → Set
s -gui-> s' = IOˢindₚ₀ modelGuiInterface s s'

data _-gui->¹_ (s : ModelGuiState ) : (s' : ModelGuiState)→ Set where
   step :  (c : modelGuiCommand s) → s -gui->¹ modelGuiNext s c

nextGui : (s : ModelGuiState)(c : modelGuiCommand s) → ModelGuiState
nextGui s c = modelGuiNext s c


modelToIOprog : (s : ModelGuiState) → Maybe (IO' GuiInterface ∞ StateAndGuiObj)
modelToIOprog (state g prop obj notStarted) = nothing
modelToIOprog (state g prop obj (started s pr)) = just pr

nextGuiProg : (s : ModelGuiState)(c : modelGuiCommand s)
              → Maybe (IO' GuiInterface ∞ StateAndGuiObj)
nextGuiProg s c = modelToIOprog (nextGui s c)


modelGuiNext' : (s : ModelGuiState)(c : modelGuiCommand s)-- (r : modelGuiResponse)
               → ModelGuiState
modelGuiNext' (state g attr obj notStarted) m     =
       state g attr obj (started m (modelGuiNextProgramStarted' g attr obj m))
modelGuiNext' (state g attr obj (started m (exec' c' f))) c =
       state g attr obj (started m (force (f c)))
modelGuiNext' (state g attr obj (started m (return' (gNew , attrNew , objNew)))) c =
       state gNew attrNew objNew notStarted


data _-gui->¹'_ (m : ModelGuiState ) : (m' : ModelGuiState)→ Set where
   step : (c : modelGuiCommand m) → m -gui->¹' modelGuiNext' m c

nextGui' : (m : ModelGuiState)(c : modelGuiCommand m) → ModelGuiState
nextGui' m c = modelGuiNext' m c
