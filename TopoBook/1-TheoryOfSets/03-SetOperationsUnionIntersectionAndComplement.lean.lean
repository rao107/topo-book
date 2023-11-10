import Mathlib.Init.Set

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 3: Set operations: union, intersection, and complement

def T := Type

-- Question 1a)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ B ↔ A ∪ B = B := by
  sorry

-- Question 1b)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ B ↔ A ∩ B = A := by
  sorry

-- Question 1c)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ (univ \ B) ↔ A ∩ B = ∅ := by
  sorry

-- Question 1d)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : (univ \ A) ⊆ B ↔ A ∪ B = S := by
  sorry

-- Question 1e)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ B ↔ (univ \ B) ⊆ (univ \ A) := by
  sorry

-- Question 1f)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ (univ \ B) ↔ B ⊆ (univ \ A) := by
  sorry

-- Question 2a)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : (Y \ X) ⊆ (Z \ X) := by
  sorry

-- Question 2b)
-- the original question uses ⊂ not ⊆ but Lean does not like ⊂ here?
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : Z \ (Y \ X) = X ∪ (Z \ Y) := by
  sorry
