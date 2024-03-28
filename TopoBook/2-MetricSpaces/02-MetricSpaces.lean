import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 2: Metric Spaces
-/

/- Question 1 -/
def dₖ (k : { x : ℝ // x > 0}) (X : MetricSpace T) (x y : T) : ℝ := k * X.dist x y
example : dₖ k X x y ≥ 0 := by
    unfold dₖ
    obtain ⟨k, hk⟩ := k
    simp_all only [zero_le_mul_left]
    exact dist_nonneg

example : dₖ k X x y = 0 ↔ x = y := by
    unfold dₖ
    obtain ⟨k, hk⟩ := k
    apply Iff.intro
    · intro h2; simp_all only [mul_eq_zero, dist_eq_zero];
        rcases h2 with ha | hb
      · simp_all only [lt_self_iff_false]
      · exact hb
    · intro h2; simp_all only [dist_self, mul_zero]

example : dₖ k X x y = dₖ k X y x := by
    unfold dₖ; simp only [mul_eq_mul_left_iff]; left; apply dist_comm

example : dₖ k X x z ≤ dₖ k X x y + dₖ k X y z := by
    unfold dₖ
    obtain ⟨k, hk⟩ := k
    rw [← mul_add]
    apply (mul_le_mul_left hk).mpr
    exact dist_triangle x y z

/- Question 2 -/

/-
  This problem does not require a formal proof. The set of points x such that
  d''(x, a) ≤ 1 for a ∈ ℝ² looks like a square rotated 45° centered at a
-/

/- Question 3 -/

/- Question 4 -/

/- Question 5 -/

/- Question 6 -/

/-
  This problem does not require a formal proof. The distance function d represents the
  area between f and g while the distance function d' represents the maximum
  difference between f and g at any point between a and b.
-/

/- Question 7 -/
def d (x y : X) : ℝ := if x = y then 0 else 1
example : d x y ≥ 0 := by
    rfl

example : d x y = 0 ↔ x = y := by
    unfold d
    simp only [ite_true]

example : d x y = d y x := by
  rfl

example : d x z ≤ d x y + d y z := by
  unfold d
  simp only [ite_true, add_zero, le_refl]

/- Question 8 -/
