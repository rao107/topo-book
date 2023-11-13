import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.LibrarySearch

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 4: Indexed Families of Sets

def I := Sort
def T := Type

-- Question 1a)
example (A : I → Set T) : ∀ β, A β ⊆ ⋃ α, A α := by
  intro β
  apply Set.subset_iUnion A β

-- Question 1b)
example (A : I → Set T) : ∀ β, ⋂ α, A α ⊆ A β := by
  intro β
  apply Set.iInter_subset (fun i ↦ A i) β

-- Question 1c)
example (A B : I → Set T) : ⋃ α, (A α ∪ B α) = (⋃ α, A α) ∪ (⋃ α, B α) := by
  apply Set.iUnion_union_distrib (fun i ↦ A i) fun i ↦ B i

-- Question 1d)
example (A B : I → Set T) : ⋂ α, (A α ∩ B α) = (⋂ α, A α) ∩ (⋂ α, B α) := by
  apply Set.iInter_inter_distrib (fun i ↦ A i) fun i ↦ B i

-- Question 1e)
example (A B : I → Set T) : ∀ β, A β ⊆ B β → ⋃ α, A α ⊆ ⋃ α, B α := by
  intro β h
  sorry

example (A B : I → Set T) : ∀ β, A β ⊆ B β → ⋂ α, A α ⊆ ⋂ α, B α := by
  intro β h
  sorry

-- Question 1f)
example (A : I → Set T) (D : Set T) : ⋃ α, (A α ∩ D) = (⋃ α, A α) ∩ D := by
  apply (Set.iUnion_inter D fun i ↦ A i).symm

example (A : I → Set T) (D : Set T) : ⋂ α, (A α ∪ D) = (⋂ α, A α) ∪ D := by
  apply (Set.iInter_union (fun i ↦ A i) D).symm

-- Question 2)
example (A B D : Set T) : A ∩ (B ∪ D) = (A ∩ B) ∪ (A ∩ D) := by
  apply Set.inter_distrib_left

example (A B D : Set T) : A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by
  apply Set.union_inter_distrib_left

-- Question 3a)

-- Question 3b)

-- Question 4a)
example (A : I → Set T) (B : Set T) : B ⊆ ⋂ α, A α ↔ ∀ β, B ⊆ A β := by
  apply Set.subset_iInter_iff

-- Question 4b)
example (A : I → Set T) (B : Set T) : ⋃ α, A α ⊆ B ↔ ∀ β, A β ⊆ B := by
  apply Set.iUnion_subset_iff

-- Question 5)
