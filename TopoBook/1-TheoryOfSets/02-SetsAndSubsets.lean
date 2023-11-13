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

--example (T : Type) : ∀ A : Set T, A ⊆ 𝒫 A := by
--  sorry

-- Question 1c)
example : ∀ A : Set T, {A} ⊆ 𝒫 A := by
  intro A
  simp
  apply subset_rfl

-- Question 1d)
example : ∀ A : Set T, ∅ ∈ 𝒫 A := by
  simp

-- Question 1e)
example : ∀ A : Set T, ∅ ⊆ 𝒫 A := by
  simp

-- Question 1f)
example : Set.Nonempty {(∅ : Set T)} := by
  simp

-- Question 1g)
example (A B : Set T) : A ⊆ B → 𝒫 A ⊆ 𝒫 B := by
  simp

-- Question 1h)
example : Set.Nontrivial { (∅ : Set (Set T)), {(∅ : Set T)} } := by
  unfold Set.Nontrivial
  simp

-- Question 2)
example (A B C : Set T) : A ⊆ B → B ⊆ C → A ⊆ C := by
  apply subset_trans

-- Question 3)
-- i have no idea how to express this question
example (n : ℕ) (A : ℕ → Set T) : ∀ i, A i ⊆ A (i + 1) ∧ A n ⊆ A 1 → ∀ i, A i = A 1 := by
  intro i
  sorry
