import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Range

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 2: Sets and subsets
-/

/- Question 1a) -/
example : ∀ A : Set T, A ∈ 𝒫 A := by
  intro A
  simp
  apply subset_rfl

/- Question 1b) -/

/- Uncomment code below to see Lean catch the false statement -/

/-
example : ∀ A : Set T, A ⊆ 𝒫 A := by
  sorry
-/

/- Question 1c) -/
example : ∀ A : Set T, {A} ⊆ 𝒫 A := by
  intro A
  simp
  apply subset_rfl

/- Question 1d) -/
example : ∀ A : Set T, ∅ ∈ 𝒫 A := by
  simp

/- Question 1e) -/
example : ∀ A : Set T, ∅ ⊆ 𝒫 A := by
  simp

/- Question 1f) -/
example : Set.Nonempty {(∅ : Set T)} := by
  simp

/- Question 1g) -/
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B := by
  simp

/- Question 1h) -/
example : Set.Nontrivial { (∅ : Set (Set T)), {∅} } := by
  unfold Set.Nontrivial
  simp

/- Question 2) -/
example (A B C : Set T) : A ⊆ B → B ⊆ C → A ⊆ C := by
  apply subset_trans

/- Question 3) -/
example (A : ℕ → Set T) : ∀ i : Fin n, A i ⊆ A ((i + 1) % n) →
  ∀ j k : Fin n, A j = A k := by
    induction' n with n ih
    · simp
    {
      
      sorry
    }
