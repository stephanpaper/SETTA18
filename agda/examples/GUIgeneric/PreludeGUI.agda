module GUIgeneric.PreludeGUI where


--
-- ooAgda Imports
--
open import NativeIO public
-- open import StateSizedIO.Base hiding (IOInterfaceˢ; IOˢ; IOˢ'; IOˢ+; delayˢ; execˢ; fmapˢ; fmapˢ'; returnˢ) public
open import SizedIO.Base public

-- Graphic lib
--
open import StateSizedIO.GUI.WxGraphicsLibLevel3 {-WithDB-} public renaming (createFrame to createWxFrame) hiding (main)

-- WxHaskell
--
open import StateSizedIO.GUI.WxBindingsFFI  renaming (Frame to FFIFrame; Button to FFIButton; TextCtrl to FFITextCtrl) public

--
--
open import StateSizedIO.GUI.BaseStateDependent public
open import StateSizedIO.GUI.VariableList renaming (addVar to addVar'; addVar' to addVar) public


-- test : {!!}
-- test = IOˢ
