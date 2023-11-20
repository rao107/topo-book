import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 2: Metric Spaces
-/

/- Question 1 -/
example (k : ℝ) (X : MetricSpace T) (dₖ : T → T → ℝ)
  (h0 : ∀ x y, dₖ x y = k * X.dist x y) (h1 : k > 0) : dₖ x y ≥ 0 := by
  rw [h0]
  simp_all
  exact dist_nonneg

example (k : ℝ) (X : MetricSpace T) (dₖ : T → T → ℝ)
  (h0 : ∀ x y, dₖ x y = k * X.dist x y) (h1 : k > 0) : dₖ x y = 0 ↔ x = y := by
  rw [h0]
  apply Iff.intro
  · intro h2; simp_all; rcases h2 with ha | hb
    · simp_all
    · exact hb
  · intro h2; simp_all

example (k : ℝ) (X : MetricSpace T) (dₖ : T → T → ℝ)
  (h0 : ∀ x y, dₖ x y = k * X.dist x y) (h1 : k > 0) : dₖ x y = dₖ y x := by
  rw [h0, h0]; simp; left; apply dist_comm

example (k : ℝ) (X : MetricSpace T) (dₖ : T → T → ℝ)
  (h0 : ∀ x y, dₖ x y = k * X.dist x y) (h1 : k > 0) : dₖ x z ≤ dₖ x y + dₖ y z := by
  rw [h0, h0, h0, ← mul_add]
  apply (mul_le_mul_left h1).mpr
  exact dist_triangle x y z

/- Question 2 -/

/-
  This problem does not require a proof. The set of points x such that
  d''(x, a) ≤ 1 for a ∈ ℝ² looks like a square rotated 45° centered at a
-/

/- Question 3 -/

/- Question 4 -/

/- Question 5 -/

/- Question 6 -/

/-
  This problem does not require a proof. The distance function d represents the
  area between f and g while the distance function d' represents the maximum
  difference between f and g at any point between a and b.
-/

/- Question 7 -/
example (d : X → X → ℝ) (h0 : ∀ x, d x x = 0)
  (h1 : ∀ x y, x ≠ y → d x y = 1) : d x y ≥ 0 := by
    by_cases h : x = y
    · rw [h, h0]
    · rw [h1]
      · simp
      · exact h

example (d : X → X → ℝ) (h0 : ∀ x, d x x = 0)
  (h1 : ∀ x y, x ≠ y → d x y = 1) : d x y = 0 ↔ x = y := by
    apply Iff.intro
    · by_contra h2; simp_all
    · intro _; apply h0

example (d : X → X → ℝ) (h0 : ∀ x, d x x = 0)
  (h1 : ∀ x y, x ≠ y → d x y = 1) : d x y = d y x := by
  by_cases h : x = y
  · rw [h]
  · rw [h1, h1]
    · apply Not.intro; intro h2; rw [h2] at h; simp at h
    · apply Not.intro; intro h2; rw [h2] at h; simp at h

example (d : X → X → ℝ) (h0 : ∀ x, d x x = 0)
  (h1 : ∀ x y, x ≠ y → d x y = 1) : d x z ≤ d x y + d y z := by
  by_cases h2 : x = z
  · rw [h2, h0]; by_cases h3 : y = z
    · rw [h3, h0]; simp
    · rw [h1]
      · rw [h1]
        · simp
        · exact h3
      · apply Not.intro; intro h4; rw [h4] at h3; simp at h3
  · rw [h1]
    · by_cases h3 : x = y
      · rw [h3, h0, ← h3, h1]
        · simp
        · exact h2
      · rw [h1]
        · simp; by_cases h4 : y = z
          · rw [h4, h0]
          · rw [h1]
            · simp
            · exact h4
        · exact h3
    · exact h2
  
/- Question 8 -/
