import Mathlib.Data.Set.Basic

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 3: Set operations: union, intersection, and complement
-/

/- Question 1 -/

/- Part a) -/
example (A B : Set T) : A ⊆ B ↔ A ∪ B = B := by
  simp only [Set.union_eq_right]

/- Part b) -/
example (A B : Set T) : A ⊆ B ↔ A ∩ B = A := by
  simp only [Set.inter_eq_left]

/- Part c) -/
example (A B : Set T) : A ⊆ Bᶜ ↔ A ∩ B = ∅ := by
  apply Iff.intro
  · intro h2; apply Disjoint.inter_eq; exact Set.disjoint_left.mpr h2
  · intro h2; apply Disjoint.subset_compl_right;
    exact Set.disjoint_iff_inter_eq_empty.mpr h2

/- Part d) -/
example (A B : Set T) : Aᶜ ⊆ B ↔ A ∪ B = Set.univ := by
  exact Set.compl_subset_iff_union

/- Part e) -/
example (A B : Set T) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  exact Iff.symm Set.compl_subset_compl

/- Part f) -/
example (A B : Set T) : A ⊆ Bᶜ ↔ B ⊆ Aᶜ := by
  exact Set.subset_compl_comm

/- Question 2 -/

/- Part a) -/
example (X Y Z : Set T) (h1: Y ⊆ Z) : (Y \ X) ⊆ (Z \ X) := by
  apply Set.diff_subset_diff_left h1

/- Part b) -/
example (X Y Z : Set T) (h0 : X ⊆ Y) (h1: Y ⊆ Z) : Z \ (Y \ X) = X ∪ (Z \ Y) := by
  rw [Set.union_comm]
  apply Set.diff_diff_eq_sdiff_union
  apply subset_trans h0 h1
