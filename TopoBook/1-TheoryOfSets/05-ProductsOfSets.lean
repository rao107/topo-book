import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 5: Products of Sets
-/

/- Question 1) -/
/-
  This problem is weird. The problem seems to rely on C(X) to be A - X which is not very obvious.
  I've prefered using the definition of complements used in Mathlib so I will instead show that
  the statement still holds as long as either A = Set.univ or B = Set.univ.
-/

-- This lemma is needed as part of the proof of
-- (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B → A = Set.univ ∨ B = Set.univ
lemma disjoint_compl_left_prod : Disjoint (Aᶜ ×ˢ Yᶜ) (A ×ˢ Yᶜ) := by
  simp only [Set.disjoint_prod, disjoint_self, Set.bot_eq_empty, Set.compl_empty_iff]
  left
  exact disjoint_compl_left

-- This lemma is also needed as part of the proof of
-- (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B → A = Set.univ ∨ B = Set.univ
lemma compl_compl_subset : ∀ A : Set α, (Aᶜ)ᶜ ⊆ A := by
  intro A
  simp only [compl_compl]
  exact Eq.subset rfl

example (h0 : X ⊆ A) (h1 : Y ⊆ B) :
  A = Set.univ ∨ B = Set.univ ↔ (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B := by
    apply Iff.intro
    -- Now proving:
    -- A = Set.univ ∨ B = Set.univ → (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B
    {
      intro h2
      -- Expand out (X ×ˢ Y)ᶜ into Set.univ ×ˢ Yᶜ ∪ Xᶜ ×ˢ Set.univ
      rw [Set.compl_prod_eq_union, Set.union_comm]
      -- Set.univ can be (A ∪ Aᶜ) or (B ∪ Bᶜ)
      nth_rewrite 1 [← Set.union_compl_self A]
      rw [← Set.union_compl_self B]
      -- Rewriting things out to see that
      -- A ×ˢ Yᶜ ∪ Aᶜ ×ˢ Yᶜ ∪ Xᶜ ×ˢ B ∪ Xᶜ ×ˢ Bᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B
      rw [Set.union_prod, Set.prod_union, ← Set.union_assoc]
      -- We prove this regardless of whether (A = Set.univ) or (B = Set.univ)
      rcases h2 with h2.l | h2.r
      -- Suppose A = Set.univ
      {
        -- Rewrite and simplify to only need to prove
        -- Xᶜ ×ˢ Bᶜ ⊆ Set.univ ×ˢ Yᶜ ∪ Xᶜ ×ˢ B
        rw [h2.l]
        simp only [Set.compl_univ, Set.empty_prod, Set.union_empty, Set.union_eq_left]
        -- It's sufficient to show Xᶜ ×ˢ Bᶜ ⊆ Set.univ ×ˢ Yᶜ
        apply Set.subset_union_of_subset_left
        -- Since Xᶜ ⊆ Set.univ and Bᶜ ⊆ Yᶜ, this is true
        apply Set.prod_mono
        · simp only [Set.subset_univ] -- Xᶜ ⊆ Set.univ
        · simp only [Set.compl_subset_compl]; apply h1 -- Bᶜ ⊆ Yᶜ
      }
      -- Suppose B = Set.univ
      {
        -- Rewrite and simplify to only need to prove
        -- Aᶜ ×ˢ Yᶜ ⊆ A ×ˢ Yᶜ ∪ Xᶜ ×ˢ Set.univ
        rw [h2.r]
        simp only [Set.compl_univ, Set.prod_empty, Set.union_empty]
        rw [Set.union_assoc, Set.union_left_comm]
        simp only [Set.union_eq_right]
        -- It's sufficient to show Aᶜ ×ˢ Yᶜ ⊆ Xᶜ ×ˢ Set.univ
        apply Set.subset_union_of_subset_right
        -- Since Aᶜ ⊆ Xᶜ and Yᶜ ⊆ Set.univ, this is true
        apply Set.prod_mono
        · simp only [Set.compl_subset_compl]; apply h0 -- Aᶜ ⊆ Yᶜ
        · simp only [Set.subset_univ] -- Yᶜ ⊆ Set.univ
      }
    }
    -- Now proving:
    -- (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B → Set.univ ∨ B = Set.univ
    {
      -- Rewrite and simplify assumption from:
      --   (X ×ˢ Y)ᶜ = A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B
      -- into two assumptions:
      --   Aᶜ ×ˢ Yᶜ ⊆ A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B
      --   Xᶜ ×ˢ Bᶜ ⊆ A ×ˢ Yᶜ ∪ Xᶜ ×ˢ B
      rw [Set.compl_prod_eq_union, Set.union_comm]
      nth_rewrite 1 [← Set.union_compl_self A]
      nth_rewrite 1 [← Set.union_compl_self B]
      rw [Set.union_prod, Set.prod_union, ← Set.union_assoc,
        Set.union_right_comm (A ×ˢ Yᶜ) (Aᶜ ×ˢ Yᶜ) (Xᶜ ×ˢ B),
        Set.union_assoc]
      simp only [Set.union_eq_left, Set.union_subset_iff, and_imp]
      intro h2 h3
      -- Since (Aᶜ ×ˢ Yᶜ) (A ×ˢ Yᶜ) are disjoint sets,
      -- h2 implies that (Aᶜ ×ˢ Yᶜ) ⊆ (Xᶜ ×ˢ B)
      -- Subsets of product spaces have three possibilities. We will show that in
      -- all of these possibilities, we can prove A = Set.univ or B = Set.univ
      have h5 : (Aᶜ ⊆ Xᶜ ∧ Yᶜ ⊆ B) ∨ Aᶜ = ∅ ∨ Yᶜ = ∅ := by
        apply Set.prod_subset_prod_iff.mp
        apply Disjoint.subset_right_of_subset_union h2 disjoint_compl_left_prod
      -- Simplifying h5 because it was easier to prove above but easier to use after
      simp only [Set.disjoint_prod, disjoint_self, Set.bot_eq_empty,
        Set.compl_empty_iff, Set.compl_subset_compl, true_and, h0] at h5
      -- h5 implies A = Set.univ or B = Set.univ for all its cases
      rcases h5 with h5.a | h5.b | h5.c
      -- Yᶜ ⊆ B → B = Set.univ
      · right
        apply Set.univ_subset_iff.mp
        rw [← Set.compl_subset_iff_union.mp (compl_compl_subset Y)]
        apply Set.union_subset
        · exact h5.a
        · exact h1
      -- A = Set.univ → A = Set.univ
      · left; exact h5.b
      -- Y = Set.univ → B = Set.univ
      · right; rw [h5.c] at h1; exact Set.eq_univ_of_univ_subset h1
    }

/- Question 2) -/
example (h0 : Finset.card A = m) (h1 : Finset.card B = n) :
  Finset.card (A ×ˢ B) = n * m := by
    simp only [Finset.card_product]
    rw [h0, h1]
    apply mul_comm

/- Question 3) -/
--idk how to express this
/-
example (A B X Y : Set T) (h0 : Set.Nontrivial A) (h1 : Set.Nontrivial B)
  (h2 : X ⊆ A) (h3 : Y ⊆ B) : ∃ W : Set (T × T), W ⊆ A ×ˢ B ∧ ¬ W ⊆ X ×ˢ Y := by
  sorry
-/
