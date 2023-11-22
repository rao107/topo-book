import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 3: Continuity
-/

/- Question 1 -/

/- Question 2 -/

/- Question 3 -/
def f (x₁ x₂ : ℝ) : ℝ := x₁ + x₂

example : Continuous f := by
  unfold f
  
  sorry

/- Question 4 -/
def g (x y : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) := ((x, y), (x, y))
def h (a : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ := (a.fst.fst + a.fst.snd, a.snd.fst - a.snd.snd)
noncomputable def k (u : ℝ × ℝ) : ℝ × ℝ := (u.fst ^ 2, u.snd ^ 2)
noncomputable def m (x : ℝ × ℝ) : ℝ := (x.fst - x.snd) / 4

example : Continuous g := by  
  sorry

example : Continuous h := by
  sorry

example : Continuous k := by
  sorry

example : Continuous m := by
  sorry

example : x * y = m ( k ( h ( g x y ) ) ) := by
  unfold g h k m
  simp only [Real.rpow_two]
  ring_nf
