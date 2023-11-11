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
example (A B : Set T) : A ⊆ Bᶜ ↔ A ∩ B = ∅ := by
  apply Iff.intro
  {
    intro h
    apply Disjoint.inter_eq
    apply Set.disjoint_left.mpr
    apply h
  }
  {
    intro h
    apply Disjoint.subset_compl_right
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply h
  }

-- Question 1d)
example (A B : Set T) : Aᶜ ⊆ B ↔ A ∪ B = Set.univ := by
  apply Set.compl_subset_iff_union

-- Question 1e)
example (A B : Set T) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  simp

-- Question 1f)
example (A B : Set T) : A ⊆ Bᶜ ↔ B ⊆ Aᶜ := by
  apply Set.subset_compl_comm

-- Question 2a)
example (X Y Z : Set T) (h1: Y ⊆ Z) : (Y \ X) ⊆ (Z \ X) := by
  apply Set.diff_subset_diff_left h1

-- Question 2b)
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : Z \ (Y \ X) = X ∪ (Z \ Y) := by
  rw [Set.union_comm]
  apply Set.diff_diff_eq_sdiff_union
  apply subset_trans h0 h1
