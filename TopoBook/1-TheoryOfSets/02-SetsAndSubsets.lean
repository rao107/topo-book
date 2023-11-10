import Mathlib.Data.Set.Basic

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 2: Sets and subsets

def T := Type

-- Question 1a)
example : ∀ A : Set T, A ∈ 𝒫 A := by
  intro A
  simp
  apply subset_rfl

-- Question 1b)

-- Uncomment code below to see Lean catch the false statement

--example (T : Type) : ∀ A : Set T, A ⊂ 𝒫 A := by
--  sorry

-- Question 1c)
example : ∀ A : Set T, {A} ⊂ 𝒫 A := by
  intro A
  unfold Set.powerset
  sorry

-- Question 1d)
example : ∀ A : Set T, ∅ ∈ 𝒫 A := by
  simp

-- Question 1e)
example : ∀ A : Set T, ∅ ⊂ 𝒫 A := by
  simp

-- Question 1f)
example : ∃ A : Set T, A ∈ {∅} := by
  sorry

-- Question 1g)
example (A B : Set T) : A ⊂ B → 𝒫 A ⊂ 𝒫 B := by
  intro h
  sorry

-- Question 1h)
example : Set.Nontrivial {∅, {∅}} := by
  sorry

-- Question 2)
example (A B C : Set T) : A ⊂ B → B ⊂ C → A ⊂ C := by
  intro h0 h1
  sorry

-- Question 3)
-- i have no idea how to express this question
example (n : ℕ) : True := by
  simp