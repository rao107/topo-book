import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite

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
example (A B X Y : Set T) (h0 : X ⊆ A) (h1 : Y ⊆ B) : (X × Y)ᶜ = (A × Yᶜ) ∪ (Xᶜ × B) := by

  sorry

-- Question 2)
example (m n : ℕ) (A : Finset S) (B : Finset T) (h0 : A.card = m) (h1: B.card = n) : (A × B).card = n * m := by
  sorry

-- Question 3)
--example (A B : Set T) (Set.Nontrivial A) (Set.Nontrivial B) : ∃ W : Set T, W ⊆ A × B := by
--  sorry


