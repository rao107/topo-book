import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

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
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ (S \ B) ↔ A ∩ B = ∅ := by
  apply Iff.intro
  {
    intro h2
    apply Set.eq_empty_iff_forall_not_mem.mpr
    simp
    intro x h3
    apply Set.not_mem_of_mem_diff (h2 h3)
  }
  {
    intro h2
    apply Set.subset_diff.mpr
    apply (and_iff_right h0).mpr
    apply Set.disjoint_iff_inter_eq_empty.mpr h2
  }

-- Question 1d)
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : (S \ A) ⊆ B ↔ A ∪ B = S := by
  apply Iff.intro
  {
    intro h2
    apply subset_antisymm_iff.mpr
    apply (and_iff_left (Set.diff_subset_iff.mp h2)).mpr
    apply Set.union_subset h0 h1
  }
  {
    intro h2
    apply Set.diff_subset_iff.mpr
    apply Eq.subset (id h2.symm)
  }

-- Question 1e)
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ B ↔ (S \ B) ⊆ (S \ A) := by
  apply Iff.intro
  {
    intro h2
    apply Set.diff_subset_diff_right h2
  }
  {
    intro h2
    
    sorry
  }

-- Question 1f)
example (A B S : Set T) (h0 : A ⊆ S) (h1 : B ⊆ S) : A ⊆ (S \ B) ↔ B ⊆ (S \ A) := by
  apply Iff.intro
  {
    intro h2
    apply Set.subset_diff.mpr
    apply (and_iff_right h1).mpr
    apply Set.disjoint_iff.mpr
    sorry
  }
  {
    intro h2
    apply Set.subset_diff.mpr
    apply (and_iff_right h0).mpr
    sorry
  }

-- Question 2a)
example (X Y Z : Set T) (h1: Y ⊆ Z) : (Y \ X) ⊆ (Z \ X) := by
  apply Set.diff_subset_diff_left h1

-- Question 2b)
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : Z \ (Y \ X) = X ∪ (Z \ Y) := by
  rw [Set.union_comm]
  apply Set.diff_diff_eq_sdiff_union
  apply subset_trans h0 h1
