------------------------------------------------------------------------
-- Kopt — A from-scratch Agda formalization of
--
--   Bian & Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis of
--   Two-Qubit Clifford+CS Operators."
--
-- Sections of the paper map to files in this library:
--
--   Section 2 (Algebra)              → Kopt.Algebra
--   Section 3 (Special unitaries)    → Kopt.SpecialUnitaries
--   Section 4 (Synthesis algorithm)  → Kopt.Synthesis
--   Section 5 (Optimality)           → Kopt.Optimality
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Kopt where

open import Kopt.Algebra
open import Kopt.SpecialUnitaries
open import Kopt.Synthesis
open import Kopt.Optimality
