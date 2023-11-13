import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

-- Introduction to Topology Third Edition by Bert Mendelson
-- Chapter One: Theory of Sets
--
-- Formal Proofs of Exercises
-- Author: Anirudh Rao
--
-- Section 5: Products of Sets

def S := Type
def T := Type

-- Question 1)
example (A B X Y : Set T) (h0 : X ⊆ A) (h1 : Y ⊆ B) : (X ×ˢ Y)ᶜ = (A ×ˢ Yᶜ) ∪ (Xᶜ ×ˢ B) := by
  apply?
  sorry

-- Question 2)
example (m n : ℕ) (A : Finset S) (B : Finset T) (h0 : Finset.card A = m) (h1 : Finset.card B = n) : Finset.card (A ×ˢ B) = n * m := by
  simp
  rw [h0, h1]
  apply mul_comm

-- Question 3)
example (A B X Y : Set T) (h0 : Set.Nontrivial A) (h1 : Set.Nontrivial B) (h2 : X ⊆ A) (h3 : Y ⊆ B) : ∃ W : Set (T × T), W ⊆ A ×ˢ B ∧ ¬ W ⊆ X ×ˢ Y := by
  sorry


