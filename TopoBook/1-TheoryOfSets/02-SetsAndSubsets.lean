import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Range

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 2: Sets and subsets
-/

/- Question 1 -/

/- Part a) -/
example : ∀ A : Set T, A ∈ 𝒫 A := by
  intro A
  simp only [Set.mem_powerset_iff]
  apply subset_rfl

/- Part b) -/

/- Uncomment code below to see Lean catch the false statement -/

/-
example : ∀ A : Set T, A ⊆ 𝒫 A := by
  sorry
-/

/- Part c) -/
example : ∀ A : Set T, {A} ⊆ 𝒫 A := by
  intro A
  simp only [Set.singleton_subset_iff, Set.mem_powerset_iff]
  apply subset_rfl

/- Part d) -/
example : ∀ A : Set T, ∅ ∈ 𝒫 A := by
  simp only [Set.mem_powerset_iff, Set.empty_subset, forall_const]

/- Part e) -/
example : ∀ A : Set T, ∅ ⊆ 𝒫 A := by
  simp only [Set.empty_subset, forall_const]

/- Part f) -/
example : Set.Nonempty {(∅ : Set T)} := by
  simp only [Set.singleton_nonempty]

/- Part g) -/
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B := by
  simp only [Set.powerset_mono, imp_self]

/- Part h) -/
example : Set.Nontrivial { (∅ : Set (Set T)), {∅} } := by
  unfold Set.Nontrivial
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, ne_eq,
    exists_eq_or_imp, exists_eq_left, not_true, false_or,
    Set.singleton_ne_empty, not_false_eq_true, or_false, or_true]

/- Question 2) -/
example (A B C : Set T) : A ⊆ B → B ⊆ C → A ⊆ C := by
  apply subset_trans

/- Question 3) -/
example (A : ℕ → Set T) : ∀ i : Fin n, A i ⊆ A ((i + 1) % n) →
  ∀ j k : Fin n, A j = A k := by
    induction' n with n ih
    · simp only [Nat.zero_eq, Nat.mod_zero, IsEmpty.forall_iff, implies_true]
    {

      sorry
    }
