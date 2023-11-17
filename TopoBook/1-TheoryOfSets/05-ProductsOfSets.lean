import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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

-- Question 1)
-- This problem is incorrect. I cannot prove this statement but I can prove
-- an if and only if condition for this statement to be true.

example (T : Type) (A B X Y : Set T) (h0 : X ⊆ A) (h1 : Y ⊆ B) :
  A = Set.univ ∨ B = Set.univ ↔ (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B := by
    apply Iff.intro
    {
      intro h2
      rw [Set.compl_prod_eq_union, Set.union_comm]
      nth_rewrite 1 [← Set.union_compl_self A]
      rw [← Set.union_compl_self B]
      rw [Set.union_prod, Set.prod_union, ← Set.union_assoc]
      rcases h2 with h2.l | h2.r
      {
        rw [h2.l]
        simp
        apply Set.subset_union_of_subset_left
        apply Set.prod_mono
        · simp
        · simp; apply h1
      }
      {
        rw [h2.r]
        simp
        rw [Set.union_assoc, Set.union_left_comm]
        simp
        apply Set.subset_union_of_subset_right
        apply Set.prod_mono
        · simp; apply h0
        · simp
      }
    }
    {
      rw [Set.compl_prod_eq_union, Set.union_comm]
      nth_rewrite 1 [← Set.union_compl_self A]
      nth_rewrite 1 [← Set.union_compl_self B]
      rw [Set.union_prod, Set.prod_union, ← Set.union_assoc,
        Set.union_right_comm (A ×ˢ Yᶜ) (Aᶜ ×ˢ Yᶜ) (Xᶜ ×ˢ B),
        Set.union_assoc]
      simp
      intro h2 h3
      have h4 : Disjoint (Aᶜ ×ˢ Yᶜ) (A ×ˢ Yᶜ) := by
        simp; left; exact disjoint_compl_left
      have h5 : (Aᶜ ×ˢ Yᶜ) ⊆ (Xᶜ ×ˢ B) := by
        exact Disjoint.subset_right_of_subset_union h2 h4
      have h6 : (Aᶜ ⊆ Xᶜ ∧ Yᶜ ⊆ B) ∨ Aᶜ = ∅ ∨ Yᶜ = ∅ := by
        exact Set.prod_subset_prod_iff.mp h5
      simp_all
      rcases h6 with h6.l | h6.r
      {
        have h7 : Bᶜ ⊆ Y := by
          exact Set.compl_subset_comm.mp h6.l
        have h8 : Bᶜ ⊆ B := by
          tauto
        have h9 : B ∩ Bᶜ = Bᶜ := by
          exact Set.inter_eq_right.mpr h8
        simp_all
        right
        exact Set.compl_empty_iff.mp (id h9.symm)
      }
      {
        rcases h6.r with h6.rl | h6.rr
        · left; exact h6.rl
        · right; rw [h6.rr] at h1; apply Set.eq_univ_of_univ_subset h1
      }
    }

-- Question 2)
example (m n : ℕ) (S T : Type) (A : Finset S) (B : Finset T)
  (h0 : Finset.card A = m) (h1 : Finset.card B = n) :
  Finset.card (A ×ˢ B) = n * m := by
    simp
    rw [h0, h1]
    apply mul_comm

-- Question 3)
--idk how to express this
--example (A B X Y : Set T) (h0 : Set.Nontrivial A) (h1 : Set.Nontrivial B) (h2 : X ⊆ A) (h3 : Y ⊆ B) : ∃ W : Set (T × T), W ⊆ A ×ˢ B ∧ ¬ W ⊆ X ×ˢ Y := by
--  sorry


