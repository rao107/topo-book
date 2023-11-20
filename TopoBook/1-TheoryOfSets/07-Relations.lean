import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter One: Theory of Sets
### Section 7: Relations
-/

/- Question 1) -/

/- Question 2) -/

/- Question 3) -/
example (f : X → X) (h : Function.Injective f) : ∀ n : ℕ, Function.Injective (f^[n]) := by
  exact fun n ↦ Function.Injective.iterate h n

--example (f : X → X) (h0 : Function.Injective f) (h1 : ∀ a b, (∃ k, b = f^[k] a) ∨ (∃ j, a = f^[j] b) → (a, b) ∈ R) : True := by
--  sorry

/- Question 4) -/

/- Question 5) -/
