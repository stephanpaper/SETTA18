module GUIgeneric.loadAllSETTA18 where


-- this file loads the files containing the code examples in the
-- CPP18 paper, ordered by sections

-- Abstract
-- 1. Introduction
-- 2. Background

import SizedIO.Base

-- 3. A Library for State-Dependent GUI Applications
-- 3.1 Introductory Example

import GUIgeneric.GUIExample

-- 3.2 GUI Interface

import StateSizedIO.GUI.WxGraphicsLibLevel3

-- 3.3. State-dependent Objects

import StateSizedIO.BaseNonPoly

-- 3.4 Implementation of Generic GUIs

import GUIgeneric.GUI

-- 3.5 A GUI with Infinitely Many States

import GUIgeneric.GUIExampleInfiniteBtnsGUIdatatype


-- example mentioned, where the nth button adds n new buttons
--    instead of just one:

import GUIgeneric.GUIExampleInfiniteBtnsAdvanced


-- 4. Proof of Correctness Properties of GUIs
-- 4.1. Reasoning about Coinductive Programs

import GUIgeneric.GUIModel

-- 5.State Transition Properties
-- 5.1 Intermediate-State Properties

import GUIgeneric.GUIModelAdvancedExampleGender
import GUIgeneric.GUIModelAdvanced
import GUIgeneric.GUIModelAdvancedExampleGender

-- 5.2 Final-State Properties

import GUIgeneric.GUIModelAdvanced
import GUIgeneric.GUIModelAdvancedExampleGender

-- a more advanced example corresponding to the system in Fig 2 can
--    be found here:

import GUIgeneric.GUIModelAdvancedExampleExtended

-- Even more advanced example as presented in README.md using
--  database


import GUIgeneric.GUIModelAdvancedExampleExtendedWithDB

-- 6. Related Work
-- 7. Conclusion
-- References
