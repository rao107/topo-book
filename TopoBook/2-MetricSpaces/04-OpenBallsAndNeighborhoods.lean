import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 4: Open Balls and Neighborhoods
-/

/- Question 1 -/
def d (x y : X) : ℝ := if x = y then 0 else 1

/- Question 2 -/
noncomputable def f (a : ℝ) : ℝ → ℝ := fun x ↦ if x ≤ a then 0 else 1

example : ¬ContinuousAt (f a) a := by
  sorry

example : a ≠ b → ContinuousAt (f a) b := by
  intro h
  sorry

/- Question 3 -/

/- Question 4 -/

/- Question 5 -/

/- Question 6 -/
example (a b : T) (X : MetricSpace T) (h : a ≠ b) :
  ∃ Na ∈ nhds a, ∃ Nb ∈ nhds b, Na ∩ Nb = ∅ := by
    exists {a}
    constructor
    · sorry
    · exists {b}
      constructor
      · sorry
      · simp_all only [Set.inter_singleton_eq_empty, Set.mem_singleton_iff]
        apply Not.intro
        intro h1
        rw [h1] at h
        simp at h

/- Question 7 -/

/- Question 8 -/
example (a : ℝ) (f : ℝ → ℝ) (h0 : Continuous f) (h1 : f a > 0) :
  ∃ k > 0, ∃ δ > 0, ∀ x ∈ Set.Icc (a - δ) (a + δ), f x ≥ k := by
    sorry
