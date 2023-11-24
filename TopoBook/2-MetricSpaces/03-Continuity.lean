import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 3: Continuity
-/

/- Question 1 -/
--def dw (f g : Set.Icc → ℝ) : ℝ := ∫ t, |(f t) - (g t)| ∂μ

/- Question 2 -/

/- Question 3 -/
def f (x : ℝ × ℝ) : ℝ := x.fst + x.snd
noncomputable def d₁ (a b : ℝ × ℝ) : ℝ := max |a.fst - b.fst| |a.snd - b.snd|
noncomputable def d₂ (a b : ℝ × ℝ) : ℝ := Real.sqrt ((a.fst - b.fst) ^ 2 + (a.snd - b.snd) ^ 2)

example : ∀ ε > 0, ∃ δ > 0, ∀ x a, d₁ x a < δ → |f x - f a| < ε := by
  intro ε hε
  exists ε / 2
  constructor
  · linarith
  · intro x a
    unfold d₁ f
    simp only [max_lt_iff, and_imp]
    intro h0 h1
    rw [← sub_sub, add_sub_right_comm]
    have h2 : |x.fst - a.fst| + |x.snd - a.snd| < ε := by
      linarith
    have h3 : |x.fst - a.fst + (x.snd - a.snd)| ≤ |x.fst - a.fst| + |x.snd - a.snd| := by
      apply abs_add (x.fst - a.fst) (x.snd - a.snd)
    rw [add_sub_assoc]
    linarith

example : ∀ ε > 0, ∃ δ > 0, ∀ x a, d₂ x a < δ → |f x - f a| < ε := by
  intro ε hε
  exists ε / Real.sqrt 2
  constructor
  · ring_nf
    simp only [inv_pos, Real.sqrt_pos, zero_lt_two, zero_lt_mul_right]
    exact hε
  · intro x a
    unfold d₂ f
    intro h0
    sorry

example : Continuous f := by
  unfold f
  continuity

/- Question 4 -/
def g (x y : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) := ((x, y), (x, y))
def h (a : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ := (a.fst.fst + a.fst.snd, a.snd.fst - a.snd.snd)
noncomputable def k (u : ℝ × ℝ) : ℝ × ℝ := (u.fst ^ 2, u.snd ^ 2)
noncomputable def m (x : ℝ × ℝ) : ℝ := (x.fst - x.snd) / 4

example : Continuous g := by  
  continuity

example : Continuous h := by
  unfold h
  simp
  constructor
  · sorry
  · sorry

example : Continuous k := by
  unfold k
  continuity

example : Continuous m := by
  unfold m
  continuity

example : x * y = m ( k ( h ( g x y ) ) ) := by
  unfold g h k m
  simp only [Real.rpow_two]
  ring_nf
