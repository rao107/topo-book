import Mathlib.Init.Set

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 2: Sets and subsets

def T := Type

-- Question 1a)
example : ∀ A : Set T, A ∈ Set.powerset A := by
  intro A
  unfold Set.powerset
  sorry

-- Question 1b)

-- Uncomment code below to see Lean catch the false statement

--example (T : Type) : ∀ A : Set T, A ⊂ Set.powerset A := by
--  sorry

-- Question 1c)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example : ∀ A : Set T, {A} ⊆ Set.powerset A := by
  intro A
  unfold Set.powerset
  
  sorry

-- Question 1d)
example : ∀ A : Set T, ∅ ∈ Set.powerset A := by
  intro A
  unfold Set.powerset
  sorry

-- Question 1e)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example : ∀ A : Set T, ∅ ⊆ Set.powerset A := by
  sorry

-- Question 1f)
example : ∃ A : Set T, A ∈ {∅} := by
  sorry

-- Question 1g)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B : Set T) : A ⊆ B → Set.powerset A ⊆ Set.powerset B := by
  sorry

-- Question 1h)
example : ∃ A B : Set T, A ≠ B → A ∈ {∅, {∅}} → B ∈ {∅, {∅}} := by
  sorry

-- Question 2)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B C : Set T) : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h0 h1
  sorry

-- Question 3)
-- i have no idea how to express this question
example (n : ℕ) : True := by
  simp