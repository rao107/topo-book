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
example (A B S : Set T) (h0: A ⊆ S) (h1 : B ⊆ S) : A ⊆ B ↔ A ∪ B = B := by
  sorry

-- Question 1b)
example (A B S : Set T) (h0: A ⊆ S) (h1 : B ⊆ S) : A ⊆ B ↔ A ∩ B = A := by
  sorry
