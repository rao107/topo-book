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
example : ∀ A : Set T, {A} ⊆ 𝒫 A := by
  intro A
  simp
  apply subset_rfl

-- Question 1d)
example : ∀ A : Set T, ∅ ∈ 𝒫 A := by
  simp

-- Question 1e)
example : ∀ A : Set T, ∅ ⊂ 𝒫 A := by
  simp

-- Question 1f)
example : Set.Nonempty {(∅ : Set T)} := by
  simp

-- Question 1g)
-- if ⊆ instead of ⊂, very easy
example (A B : Set T) : A ⊂ B → 𝒫 A ⊂ 𝒫 B := by
  intro h
  
  sorry

#check Set.powerset_mono

-- Question 1h)
-- is it possible for a set in Lean to contain multiple types?
example : Set.Nontrivial { (∅ : Set T), {(∅ : Set T)} } := by
  sorry

-- Question 2)
example (A B C : Set T) : A ⊂ B → B ⊂ C → A ⊂ C := by
  intro h0 h1

  sorry

-- Question 3)
-- i have no idea how to express this question
example (n : ℕ) : True := by
  sorry
