import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Image
import Mathlib.Tactic.LibrarySearch

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 6: Functions
-/

/- Question 1) -/

/- Part a) -/
example : ∀ X, X ⊆ f⁻¹' (f '' X) := by
  exact (fun X ↦ Set.subset_preimage_image f X)

/- Part b) -/
example : ∀ Y, Y ⊇ f '' (f⁻¹' Y) := by
  exact (fun Y ↦ Set.image_preimage_subset f Y)

/- Part c) -/
example (h : Function.Injective f) : ∀ X, f⁻¹' (f '' X) = X := by
  exact (fun X ↦ Set.preimage_image_eq X h)

/- Part d) -/
example (h : Function.Surjective f) : ∀ Y, f '' (f⁻¹' Y) = Y := by
  exact (fun Y ↦ Set.image_preimage_eq Y h)

/- Question 2) -/

/- Part a) -/

/- Part b) -/

/- Part c) -/

/- Question 3) -/

/- Part a) -/
example (X : I → Set A) : f '' ⋃ α, X α = ⋃ α, f '' X α := by
  exact Set.image_iUnion

/- Part b) -/
example (X : I → Set A) : f '' (⋂ α, X α) ⊆ ⋂ α, f '' X α := by
  exact Set.image_iInter_subset (fun i ↦ X i) f

/- Part c) -/
example (X : I → Set A) : Function.Injective f → f '' (⋂ α, X α) = ⋂ α, f '' X α := by
  intro h
  apply Set.eq_of_subset_of_subset
  · exact Set.image_iInter_subset (fun i ↦ X i) f
  · sorry

/- Question 4) -/

/- Part a) -/
example (Y : I → Set B) : f⁻¹' ⋃ α, Y α = ⋃ α, f⁻¹' Y α := by
  exact Set.preimage_iUnion

/- Part b) -/
example (Y : I → Set B) : f⁻¹' ⋂ α, Y α = ⋂ α, f⁻¹' Y α := by
  exact Set.preimage_iInter

/- Part c) -/
example : f⁻¹' (Xᶜ) = (f⁻¹' X)ᶜ := by
  simp only [Set.preimage_compl]

/- Part d) -/
example : f '' (X ∩ f⁻¹' Y) = f '' X ∩ Y := by
  exact Set.image_inter_preimage f X Y

/- Question 5) -/

/- Question 6) -/
namespace q6
def A := Type
def B := Type
def j (b : B) : A → A × B := fun a ↦ (a, b)

example : Function.Injective (j b) := by
  intro a₁ a₂
  unfold j
  simp only [Prod.mk.injEq, and_true, imp_self]

example : ∃ jbW, (j b)⁻¹' W = jbW := by
  exists {x | (x, b) ∈ W}

end q6

/- Question 7) -/

/- Part a) -/
namespace q7
def A := Type
def χ (E : Set A) [∀ x : A, Decidable (x ∈ E)] : A → ℕ :=
  fun x ↦ (if x ∈ E then 1 else 0)

example (E F : Set A) [∀ x : A, Decidable (x ∈ E)] [∀ x : A, Decidable (x ∈ F)] : χ (E ∩ F) = χ E * χ F := by
  unfold χ
  simp only [Set.mem_inter_iff]
  ext x
  simp only [Pi.mul_apply, mul_ite, mul_one, mul_zero]
  split <;> rename_i h0
  · simp_all only [ite_true]
  · simp only [not_and] at h0
    split <;> rename_i h1
    · simp_all only [not_true_eq_false]
      split <;> rename_i h2
      · simp_all only [forall_true_left]
      · rfl
    · rfl

/- Part b) -/

example (E F : Set A) [∀ x : A, Decidable (x ∈ E)] [∀ x : A, Decidable (x ∈ F)] : χ (E ∪ F) = χ E + χ F - χ (E ∩ F) := by
  unfold χ
  rename_i inst inst_1
  simp_all only [Set.mem_union, Set.mem_inter_iff]
  ext x
  simp_all only [Pi.sub_apply, Pi.add_apply, ge_iff_le]
  split <;> rename_i h
  · cases h <;> rename_i h
    · simp_all only [ite_true, true_and, ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
    · simp_all only [ite_true, and_true, ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, add_tsub_cancel_left]
  · split
    · simp_all only [true_or, not_true_eq_false]
    · simp_all only [false_or, ite_false, add_zero, and_self, ge_iff_le, le_refl, tsub_eq_zero_of_le]

end q7

/- Question 8) -/
example (h : Finset.card A = n) : Finset.card (Finset.powerset A) = 2^n := by
  simp only [Finset.card_powerset]
  rw [h]
