import Mathlib.Init.Set

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao

-- Section 1: Introduction

-- There are no exercises in this section

-- Section 2: Sets and subsets

-- Question 1a)
example (T : Type) : ∀ A : Set T, A ∈ Set.powerset A := by
  intro A
  unfold Set.powerset
  sorry

-- Question 1b)

-- Uncomment code below to see Lean catch the false statement

--example (T : Type) : ∀ A : Set T, A ⊂ Set.powerset A := by
--  sorry

-- Question 1c)
-- idk how to fix this...
example (T : Type) : ∀ A : Set T, {A} ⊂ Set.powerset A := by
  sorry

-- Question 1d)
example (T : Type) : ∀ A : Set T, ∅ ∈ Set.powerset A := by
  intro A
  unfold Set.powerset
  sorry

-- Question 1e)
example (T : Type) : ∀ A : Set T, ∅ ⊂ Set.powerset A := by
  sorry

-- Question 1f)
example (T : Type) : ∃ A : Set T, A ∈ {∅} := by
  sorry

-- Question 1g)
example (T : Type) (A B : Set T) : A ⊂ B → Set.powerset A ⊂ Set.powerset B := by
  sorry

-- Question 1h)
example (T : Type) : ∃ A B : Set T, A ≠ B → A ∈ {∅, {∅}} → B ∈ {∅, {∅}} := by
  sorry

-- Question 2)
example (T: Type) (A B C : Set T) : A ⊂ B → B ⊂ C → A ⊂ C := by
  sorry

-- Question 3)
-- i have no idea how to express this question
example (T : Type) (n : ℕ) : True := by
  simp

-- Section 3: Set operations: union, intersection, and complement

-- Section 4: Indexed families of sets

-- Section 5: Products of sets

-- Section 6: Functions

-- Section 7: Relations

-- Section 8: Composition of functions and diagrams

-- Section 9: Inverse functions, extensions, and restrictions

-- Section 10: Arbitrary products

