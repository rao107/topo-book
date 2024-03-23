import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 3: Continuity
-/

/- Question 1 -/
--def dw (f g : Set.Icc → ℝ) : ℝ := ∫ t, |(f t) - (g t)| ∂μ

/- Question 2 -/

/- Question 3 -/
def f (x : ℝ × ℝ) : ℝ := x.1 + x.2

example : Continuous f := by
  unfold f
  apply continuous_add

/- Question 4 -/
def g (x y : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) := ((x, y), (x, y))
def h (a : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ := (a.1.1 + a.1.2, a.2.1 - a.2.2)
noncomputable def k (u : ℝ × ℝ) : ℝ × ℝ := (u.1 ^ 2, u.2 ^ 2)
noncomputable def m (x : ℝ × ℝ) : ℝ := (x.1 - x.2) / 4

example : Continuous g := by
  apply continuous_pi
  intro i
  simp_all only [continuous_prod_mk]
  apply And.intro
  · apply And.intro
    · apply continuous_id'
    · apply continuous_const
  · apply And.intro
    · apply continuous_id'
    · apply continuous_const

example : Continuous h := by
  unfold h
  simp only [continuous_prod_mk]
  constructor
  · apply Continuous.add
    · apply continuous_fst.comp continuous_fst
    · apply continuous_snd.comp continuous_fst
  · apply Continuous.add
    · apply continuous_fst.comp continuous_snd
    · apply Continuous.comp'
      · apply ContinuousNeg.continuous_neg
      · apply continuous_snd.comp continuous_snd

example : Continuous k := by
  unfold k
  simp only [continuous_prod_mk]
  apply And.intro
  · apply Continuous.pow
    apply continuous_fst
  · apply Continuous.pow
    apply continuous_snd

example : Continuous m := by
  unfold m
  apply Continuous.div_const
  apply Continuous.add
  · apply continuous_fst
  · apply Continuous.comp'
    · apply ContinuousNeg.continuous_neg
    · apply continuous_snd

example : x * y = m ( k ( h ( g x y ) ) ) := by
  unfold g h k m
  simp only [Real.rpow_two]
  ring_nf
