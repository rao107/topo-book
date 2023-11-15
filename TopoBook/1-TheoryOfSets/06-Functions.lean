import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Image
import Mathlib.Tactic.LibrarySearch

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 6: Functions

-- Question 1a)
example (A B : Type) (f : A → B) :
  ∀ X, X ⊆ f⁻¹' (f '' X) := by
    exact (fun X ↦ Set.subset_preimage_image f X)

-- Question 1b)
example (A B : Type) (f : A → B) :
  ∀ Y, Y ⊇ f '' (f⁻¹' Y) := by
    exact (fun Y ↦ Set.image_preimage_subset f Y)

-- Question 1c)
example (A B : Type) (f : A → B) (h : Function.Injective f) :
  ∀ X, f⁻¹' (f '' X) = X := by
    exact (fun X ↦ Set.preimage_image_eq X h)

-- Question 1d)
example (A B : Type) (f : A → B) (h : Function.Surjective f) :
  ∀ Y, f '' (f⁻¹' Y) = Y := by
    exact (fun Y ↦ Set.image_preimage_eq Y h)

-- Question 2a)

-- Question 2b)

-- Question 2c)

-- Question 3a)
example (A B : Type) (I : Sort) (f : A → B) (X : I → Set A) :
  f '' ⋃ α, X α = ⋃ α, f '' X α := by
    exact Set.image_iUnion

-- Question 3b)
example (A B : Type) (I : Sort) (f : A → B) (X : I → Set A) :
  f '' (⋂ α, X α) ⊆ ⋂ α, f '' X α := by
    exact Set.image_iInter_subset (fun i ↦ X i) f

-- Question 3c)
example (A B : Type) (I : Sort) (f : A → B) (X : I → Set A) :
  Function.Injective f → f '' (⋂ α, X α) = ⋂ α, f '' X α := by
    intro h
    sorry

-- Question 4a)
example (A B : Type) (I : Sort) (f : A → B) (Y : I → Set B) :
  f⁻¹' ⋃ α, Y α = ⋃ α, f⁻¹' Y α := by
    exact Set.preimage_iUnion

-- Question 4b)
example (A B : Type) (I : Sort) (f : A → B) (Y : I → Set B) :
  f⁻¹' ⋂ α, Y α = ⋂ α, f⁻¹' Y α := by
    exact Set.preimage_iInter

-- Question 4c)
example (A B : Type) (f : A → B) (X : Set B) :
  f⁻¹' (Xᶜ) = (f⁻¹' X)ᶜ := by
    simp

-- Question 4d)
example (A B : Type) (f : A → B) (X : Set A) (Y : Set B) :
  f '' (X ∩ f⁻¹' Y) = f '' X ∩ Y := by
    exact Set.image_inter_preimage f X Y

-- Question 5)

-- Question 6)

-- Question 7a)

-- Question 7b)

-- Question 8)
example (n : ℕ) (A : Finset T) (h : Finset.card A = n) :
  Finset.card (Finset.powerset A) = 2^n := by
    simp
    rw [h]
