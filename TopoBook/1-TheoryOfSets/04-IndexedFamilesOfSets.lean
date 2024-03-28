import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.LibrarySearch

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 4: Indexed Families of Sets
-/

/- Question 1 -/

/- Part a) -/
example (A : I → Set T) : ∀ β, A β ⊆ ⋃ α, A α := by
  intro β
  exact Set.subset_iUnion A β

/- Part b) -/
example (A : I → Set T) : ∀ β, ⋂ α, A α ⊆ A β := by
  intro β
  exact Set.iInter_subset (fun i ↦ A i) β

/- Part c) -/
example (A B : I → Set T) : ⋃ α, (A α ∪ B α) = (⋃ α, A α) ∪ (⋃ α, B α) := by
  exact Set.iUnion_union_distrib (fun i ↦ A i) fun i ↦ B i

/- Part d) -/
example (A B : I → Set T) : ⋂ α, (A α ∩ B α) = (⋂ α, A α) ∩ (⋂ α, B α) := by
  exact Set.iInter_inter_distrib (fun i ↦ A i) fun i ↦ B i

/- Part e) -/
example (A B : I → Set T) (h: ∀ β, A β ⊆ B β) : ⋃ α, A α ⊆ ⋃ α, B α := by
  simp only [Set.iUnion_subset_iff]
  exact fun i ↦ Set.subset_iUnion_of_subset i (h i)

example (A B : I → Set T) (h: ∀ β, A β ⊆ B β) : ⋂ α, A α ⊆ ⋂ α, B α := by
  simp only [Set.subset_iInter_iff]
  exact fun i ↦ Set.iInter_subset_of_subset i (h i)

/- Part f) -/
example (A : I → Set T) : ⋃ α, (A α ∩ D) = (⋃ α, A α) ∩ D := by
  exact (Set.iUnion_inter D fun i ↦ A i).symm

example (A : I → Set T) : ⋂ α, (A α ∪ D) = (⋂ α, A α) ∪ D := by
  exact (Set.iInter_union (fun i ↦ A i) D).symm

/- Question 2) -/
example (A B D : Set T) : A ∩ (B ∪ D) = (A ∩ B) ∪ (A ∩ D) := by
  apply Set.inter_distrib_left

example (A B D : Set T) : A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by
  exact Set.union_inter_distrib_left

/- Question 3 -/

/- Part a) -/
example (I J : Set ι) (A : ι → Set T) (h : J ⊆ I) : ⋂ α ∈ J, A α ⊇ ⋂ α ∈ I, A α := by
  exact Set.biInter_subset_biInter_left h

/- Part b) -/
example (I J : Set ι) (A : ι → Set T) (h : J ⊆ I) : ⋃ α ∈ J, A α ⊆ ⋃ α ∈ I, A α := by
  exact Set.biUnion_subset_biUnion_left h

/- Question 4 -/

/- Part a) -/
example (A : I → Set T) (B : Set T) : B ⊆ ⋂ α, A α ↔ ∀ β, B ⊆ A β := by
  exact Set.subset_iInter_iff

/- Part b) -/
example (A : I → Set T) (B : Set T) : ⋃ α, A α ⊆ B ↔ ∀ β, A β ⊆ B := by
  exact Set.iUnion_subset_iff

/- Question 5) -/
--idk how to express this
