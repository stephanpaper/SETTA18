module GUIgeneric.PreludeGUIWithDBTmp where


--
-- ooAgda Imports
--
open import NativeIO public
-- open import StateSizedIO.BaseNonPoly hiding (IOInterfaceˢ; IOˢ; IOˢ'; IOˢ+; delayˢ; execˢ; fmapˢ; fmapˢ'; returnˢ; IOObjectˢ;IOObjectˢ-bjectˢ-) public
open import SizedIO.Base public

-- Graphic lib
--
open import StateSizedIO.GUI.WxGraphicsLibLevel3WithDBPrime public renaming (createFrame to createWxFrame) hiding (main)

-- WxHaskell
--
open import StateSizedIO.GUI.WxBindingsFFI  renaming (Frame to FFIFrame; Button to FFIButton; TextCtrl to FFITextCtrl) public

--
--
open import StateSizedIO.GUI.BaseStateDependent public
open import StateSizedIO.GUI.VariableList renaming (addVar to addVar'; addVar' to addVar) public
