import Mathlib.Data.Set.Image
import Mathlib.Tactic.LibrarySearch

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 8: Composition of Functions and Diagrams

-- does mathlib4 have tools to express diagrams?
-- a quick search yields results in category theory
-- can these be used to formalize these exercises more thoroughly?

-- Question 1)

-- Question 2)

-- Question 3)

-- Question 4)
example (A B C : Type) (f : A → B) (g : B → C) :
  ∀ Z, (g ∘ f)⁻¹' Z = f⁻¹' (g⁻¹' Z) := by
    exact fun Z ↦ rfl
