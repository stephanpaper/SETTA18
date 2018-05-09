
module StateSizedIO.GUI.WxGraphicsLibLevel3 where


open import StateSizedIO.GUI.Prelude

-- Note this file contains only commands for console I/O and creating and modifying
--  gui elements
-- The file
-- WxGraphicsLibLevel3WithDBPrime.agda
--
-- contains the extended set which includes database commands.

data GuiCommand  : Set where
  putStrLn     : String  →  GuiCommand
  getLine      : GuiCommand
  createFrame  : GuiCommand
  addButtonCmd    : Frame → Button → GuiCommand
  createTextCtrl     : Frame    → String → GuiCommand
  getTextFromTxtBox  : TextCtrl → GuiCommand
  fireCustomEvent    : Frame   → GuiCommand
  setAttribButton    : Button  → WxColor → GuiCommand
  setAttribTextCtrl  : TextCtrl  → WxColor → GuiCommand
  setChildredLayout  : Frame   → ℕ → ℕ → ℕ → ℕ → GuiCommand
  createButton       : Frame   → String → GuiCommand
  deleteButton       : Button  → GuiCommand
  deleteTextCtrl     : TextCtrl → GuiCommand
  drawBitmap         : DC      → Bitmap → Point → Bool → GuiCommand
  repaint            : Frame   → GuiCommand
  bitmapGetWidth     : Bitmap  → GuiCommand


GuiResponse : GuiCommand → Set 
GuiResponse  createFrame         = Frame
GuiResponse  (createButton _ _)    = Button
GuiResponse  (bitmapGetWidth _)  = ℤ
GuiResponse  (createTextCtrl _ _)    = TextCtrl
GuiResponse  (getTextFromTxtBox _)   = String
GuiResponse  getLine             =  String
GuiResponse _                    =  Unit

GuiInterface  :  IOInterface
GuiInterface  .Command   =  GuiCommand
GuiInterface  .Response  =  GuiResponse





GuiLev2State : Set₁
GuiLev2State = VarList

data GuiLev2Command (s :  GuiLev2State) : Set₁ where
  level1C        : GuiCommand → GuiLev2Command s
  createVar      : {A : Set} → A → GuiLev2Command s
  setButtonHandler :
    Button
    → List (prod s → IO GuiInterface ∞ (prod s))
    → GuiLev2Command s
  setTimer          : Frame → ℤ → List (prod s → IO GuiInterface ∞ (prod s))
                      → GuiLev2Command s
  setKeyHandler     : Button
                      → List (prod s → IO GuiInterface ∞ (prod s))
                      → List (prod s → IO GuiInterface ∞ (prod s))
                      → List (prod s → IO GuiInterface ∞ (prod s))
                      → List (prod s → IO GuiInterface ∞ (prod s))
                      → GuiLev2Command s
  setOnPaint        : Frame
                     → List (prod s → DC → Rect → IO GuiInterface ∞ (prod s))
                     → GuiLev2Command s

GuiLev2Response : (s : GuiLev2State)
                  → GuiLev2Command s → Set
GuiLev2Response _ (level1C c) = GuiResponse c
GuiLev2Response _ (createVar {A} a) = Var A
GuiLev2Response _ (setTimer fra x p) = Timer
GuiLev2Response _ _ = Unit


GuiLev2Next : (s : GuiLev2State) (c : GuiLev2Command s)
              → GuiLev2Response s c
              → GuiLev2State
GuiLev2Next s (createVar {A} a) var = addVar A var s
GuiLev2Next s _  _                  = s

GuiLev2Interface : IOInterfaceˢ
Stateˢ     GuiLev2Interface = GuiLev2State
Commandˢ   GuiLev2Interface = GuiLev2Command
Responseˢ  GuiLev2Interface = GuiLev2Response
nextˢ      GuiLev2Interface = GuiLev2Next

translateLev1Local :  (c : GuiCommand)
                      → NativeIO (GuiResponse c)
translateLev1Local createFrame            = nativeCreateFrame

translateLev1Local (setChildredLayout win a b c d) = nativeSetChildredLayout win a b c d
translateLev1Local (createButton fra str)   = nativeMakeButton fra str
translateLev1Local (deleteButton bt)      = nativeDeleteButton bt
translateLev1Local (deleteTextCtrl txt)   = nativeDeleteTextCtrl txt
translateLev1Local (addButtonCmd fra bt)     = nativeAddButton fra bt
translateLev1Local (getTextFromTxtBox txt)   = nativeGetTextFromTxtBox txt
translateLev1Local (setAttribButton bt col) = nativeSetColorButton bt col

translateLev1Local (setAttribTextCtrl txt col) = nativeSetColorTextCtrl txt col
translateLev1Local (drawBitmap dc bm p b) = nativeDrawBitmap dc bm p b
translateLev1Local (repaint fra)          = nativeRepaint fra
translateLev1Local (bitmapGetWidth b)     = nativeBitmapGetWidth b
translateLev1Local (putStrLn s)           = nativePutStrLn s
translateLev1Local getLine                = nativeGetLine
translateLev1Local (fireCustomEvent fr)   = nativeFireCustomEvent fr
translateLev1Local (createTextCtrl f str) = nativeMakeTextCtrl f str


translateLev1 : {A : Set} → IO GuiInterface ∞ A → NativeIO A
translateLev1 = translateIO translateLev1Local


translateLev1List : {A : Set} → List (IO GuiInterface ∞ A) → List (NativeIO A)
translateLev1List l = map translateLev1 l




translateLev2Local : (s : GuiLev2State)
                          → (c : GuiLev2Command s)
                          → NativeIO (GuiLev2Response s c)
translateLev2Local s (level1C c) = translateLev1Local c

translateLev2Local s (createVar {A} a)   = nativeNewVar {A} a
translateLev2Local s (setButtonHandler bt proglist)
    = nativeSetButtonHandler bt
            (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglist))

translateLev2Local s (setTimer fra interv proglist)
    = nativeSetTimer fra interv (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglist))


translateLev2Local s (setKeyHandler bt proglistRight proglistLeft proglistUp proglistDown)
    =  nativeSetKeyHandler bt
           (λ key -> case (showKey key) of λ
                 { "Right" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistRight))
                 ; "Left" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistLeft))
                 ; "Up" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistUp))
                 ; "Down" → (dispatchList s (map (λ prog → translateLev1 ∘ prog)  proglistDown))
                 ; _  → nativeReturn unit
                 } )



translateLev2Local s (setOnPaint fra proglist)
    = nativeSetOnPaint fra (λ dc rect → (dispatchList s
         (map (λ prog aa → translateLev1 (prog aa dc rect)) proglist)))


translateLev2 : {s : GuiLev2State} → {A : Set}
                     → IOˢ GuiLev2Interface ∞ (λ _ → A) s → NativeIO A
translateLev2 = translateIOˢ {I = GuiLev2Interface} translateLev2Local


data GuiLev3Command (s :  GuiLev2State) : Set₂ where
  level2C : GuiLev2Command s → GuiLev3Command s
  setCustomEvent :  Frame
    →  List  (prod s
               → IOˢ  GuiLev2Interface ∞
                       (λ _ → prod s) s)
    →  GuiLev3Command s


  setRightClick     : Frame → List ( (x : prod s) → IOˢ GuiLev2Interface ∞ (λ _ → prod s) s)
                     → GuiLev3Command s




GuiLev3Response : (s : GuiLev2State) → GuiLev3Command s → Set
GuiLev3Response s (level2C c)         = GuiLev2Response s c
GuiLev3Response _ _                   = Unit

GuiLev3Next : (s : GuiLev2State) → (c : GuiLev3Command s)
              → GuiLev3Response s c
              → GuiLev2State
GuiLev3Next s (level2C c) r = GuiLev2Next s c r
GuiLev3Next s (setRightClick _ _) _ = s
GuiLev3Next s (setCustomEvent _ _) _ = s

GuiLev3Interface : IOInterfaceˢ
GuiLev3Interface .Stateˢ = GuiLev2State
GuiLev3Interface .Commandˢ = GuiLev3Command
GuiLev3Interface .Responseˢ = GuiLev3Response
GuiLev3Interface .nextˢ = GuiLev3Next

translateLev3Local : (s : GuiLev2State)
                          → (c : GuiLev3Command s)
                          → NativeIO (GuiLev3Response s c)
translateLev3Local s (level2C c) = translateLev2Local s c
translateLev3Local s (setRightClick f proglist) =
    nativeSetClickRight f
           (dispatchList s (map (λ prog → translateLev2{s} ∘ prog ) proglist))

translateLev3Local s (setCustomEvent f proglist) =

    nativeRegisterCustomEvent f
           (dispatchList s (map (λ prog → translateLev2{s} ∘ prog ) proglist))


translateLev3 : {s : GuiLev2State} → {A : Set}
                     → IOˢ GuiLev3Interface ∞ (λ _ → A) s → NativeIO A
translateLev3 = translateIOˢ {I = GuiLev3Interface} translateLev3Local

mutual
  translateLev1toLev2∞ : ∀{s : GuiLev2State} → {A : Set}
                       → IO' GuiInterface ∞ A → IOˢ' GuiLev2Interface ∞ (λ _ → A) s
  translateLev1toLev2∞ (exec' c f) = execˢ' (level1C c) λ r → translateLev1toLev2 (f r)
  translateLev1toLev2∞ (return' a) = returnˢ' a


  translateLev1toLev2ₚ∞ : ∀{s : GuiLev2State} → {A : Set} → IO' GuiInterface ∞ A
                                      → IOₚˢ' GuiLev2Interface ∞ A s s
  translateLev1toLev2ₚ∞ (exec' c f) = execˢ' (level1C c) (λ r → translateLev1toLev2ₚ (f r))
  translateLev1toLev2ₚ∞ (return' a) = returnˢ' (refl , a)

  translateLev1toLev2 : ∀{s : GuiLev2State} → {A : Set}
                       → IO GuiInterface ∞ A → IOˢ GuiLev2Interface ∞ (λ _ → A) s
  translateLev1toLev2 x .forceˢ = translateLev1toLev2∞ (x .force)


  translateLev1toLev2ₚ : ∀{s : GuiLev2State} → {A : Set}
                       → IO GuiInterface ∞ A → IOₚˢ GuiLev2Interface ∞ A s s
  translateLev1toLev2ₚ x .forceˢ = translateLev1toLev2ₚ∞ (x .force)



mutual
  translateLev2toLev3∞ : ∀{α}{s : GuiLev2State} → {A : GuiLev2State → Set α}
                     → IOˢ' GuiLev2Interface ∞ A s → IOˢ' GuiLev3Interface ∞ A s
  translateLev2toLev3∞ (execˢ'{s} c f) = execˢ' (level2C c) λ r → translateLev2toLev3 (f r)
  translateLev2toLev3∞ (returnˢ' a) = returnˢ' a



  translateLev2toLev3 : ∀{α}{s : GuiLev2State} → {A : GuiLev2State → Set α}
                       → IOˢ GuiLev2Interface ∞ A s → IOˢ GuiLev3Interface ∞ A s
  translateLev2toLev3 x .forceˢ = translateLev2toLev3∞ (x .forceˢ)




--
-- Example
--
example : IO GuiInterface ∞ Frame
example = exec  createFrame                 λ frame  →
          exec  (putStrLn "Frame created")  λ _      →
          return frame
-- private
main : NativeIO Frame
main = translateIO translateLev1Local example
