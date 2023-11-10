import Mathlib.Data.Set.Basic

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 3: Set operations: union, intersection, and complement

def T := Type

-- Question 1a)
example (A B : Set T) : A ⊆ B ↔ A ∪ B = B := by
  simp


-- Question 1b)
example (A B : Set T) : A ⊆ B ↔ A ∩ B = A := by
  simp

-- Question 1c)
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ Bᶜ ↔ A ∩ B = ∅ := by
  
  sorry

-- Question 1d)
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : Aᶜ ⊆ B ↔ A ∪ B = S := by
  
  sorry

-- Question 1e)
example (A B : Set T) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  simp

-- Question 1f)
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ Bᶜ ↔ B ⊆ Aᶜ := by

  sorry

-- Question 2a)
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : (Y \ X) ⊂ (Z \ X) := by

  sorry

-- Question 2b)
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : Z \ (Y \ X) = X ∪ (Z \ Y) := by
  
  sorry
