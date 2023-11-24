import Mathlib

/-!
# Introduction to Topology Third Edition by Bert Mendelson
## Chapter Two: Metric Spaces
### Section 6: Open and Closed Sets
-/

/- Question 1 -/

/- Question 2 -/
def T := Type
def X := MetricSpace T
--noncomputable def X.dist (x y : T) := if x = y then 0 else 1

/- Question 3 -/

/- Question 4 -/
example (A : Set ℝ) (h0 : IsClosed A) (h1 : Nonempty A) (h2 : Nonempty (lowerBounds A)) (h3 : IsGLB A α) : α ∈ A := by
  simp_all
  sorry

/- Question 5 -/

/- Question 6 -/
