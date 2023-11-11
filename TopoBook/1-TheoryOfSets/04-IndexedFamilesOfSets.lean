import Mathlib.Data.Set.Basic

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 4: Indexed Families of Sets

def T := Type

-- Question 1a)

-- Question 1b)

-- Question 1c)

-- Question 1d)

-- Question 1e)

-- Question 1f)

-- Question 2)
example (A B D : Set T) : A ∩ (B ∪ D) = (A ∩ B) ∪ (A ∩ D) := by
  apply Set.inter_distrib_left

example (A B D : Set T) : A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by
  apply Set.union_inter_distrib_left

-- Question 3a)

-- Question 3b)

-- Question 4a)

-- Question 4b)

-- Question 5)
