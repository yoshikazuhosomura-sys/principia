import Mathlib

/-!
# One-parameter class plus one-step residual: the telescoping bookkeeping

Elementary bookkeeping behind the decomposition
"a class closed under the step up to a change of its parameter" × "a one-step residual".
`x k` is an observable after `k` steps, `f k` the value of the class function at the parameter
read off after `k` steps, and `r k` bounds the one-step residual.  Nothing here concerns any
specific measure: the analytic content is entirely in the hypothesis on `r`.
-/

namespace LatticeGaugeClassResidualTelescoping

open Finset

/-- The deviation from the class function after `K` steps is at most the sum of the one-step
residuals (telescoping). -/
theorem telescoping_residual (x f r : ℕ → ℝ)
    (h : ∀ k, |x (k + 1) - x k - (f (k + 1) - f k)| ≤ r k) (K : ℕ) :
    |x K - x 0 - (f K - f 0)| ≤ ∑ k ∈ range K, r k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    calc |x (K + 1) - x 0 - (f (K + 1) - f 0)|
        = |(x K - x 0 - (f K - f 0)) + (x (K + 1) - x K - (f (K + 1) - f K))| := by
          congr 1; ring
      _ ≤ |x K - x 0 - (f K - f 0)| + |x (K + 1) - x K - (f (K + 1) - f K)| := abs_add_le _ _
      _ ≤ (∑ k ∈ range K, r k) + r K := add_le_add ih (h K)

/-- The same statement when the class has `n` parameters: only the values of the class
function along the parameter sequence enter. -/
theorem telescoping_residual_multi {n : ℕ} (F : (Fin n → ℝ) → ℝ) (p : ℕ → Fin n → ℝ)
    (x r : ℕ → ℝ) (h : ∀ k, |x (k + 1) - x k - (F (p (k + 1)) - F (p k))| ≤ r k) (K : ℕ) :
    |x K - x 0 - (F (p K) - F (p 0))| ≤ ∑ k ∈ range K, r k :=
  telescoping_residual x (fun k => F (p k)) r h K

/-- A geometrically contracting (irrelevant) part of the residual sums to a bound uniform in
the number of steps. -/
theorem geometric_part_le (D q : ℝ) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    ∑ k ∈ range K, D * q ^ k ≤ D / (1 - q) := by
  rw [← mul_sum]
  have h1 : ∑ k ∈ range K, q ^ k ≤ q ^ 0 / (1 - q) := by
    rw [range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hq0 hq1
  rw [pow_zero] at h1
  calc D * ∑ k ∈ range K, q ^ k ≤ D * (1 / (1 - q)) := mul_le_mul_of_nonneg_left h1 hD
    _ = D / (1 - q) := by ring

/-- One step of the inverse-square comparison: `1/(u+c)^2 ≤ 1/(c u) - 1/(c (u+c))`. -/
theorem inv_sq_step (u c : ℝ) (hu : 0 < u) (hc : 0 < c) :
    1 / (u + c) ^ 2 ≤ 1 / (c * u) - 1 / (c * (u + c)) := by
  have hrhs : 1 / (c * u) - 1 / (c * (u + c)) = 1 / (u * (u + c)) := by
    field_simp; ring
  rw [hrhs]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

/-- Inverse squares of a linearly growing parameter `a + c k` sum to a bound uniform in `K`
(the arithmetic of 13-11 (8) with δ = 2, for a step that moves the parameter by at least `c`). -/
theorem inv_sq_sum_le (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (K : ℕ) :
    ∑ k ∈ range K, 1 / (a + c * k) ^ 2 ≤ 1 / a ^ 2 + 1 / (c * a) := by
  have key : ∀ K : ℕ, ∑ k ∈ range (K + 1), 1 / (a + c * k) ^ 2
      ≤ 1 / a ^ 2 + 1 / (c * a) - 1 / (c * (a + c * K)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ]
      have hu : 0 < a + c * (K : ℝ) := by positivity
      have hs := inv_sq_step (a + c * (K : ℝ)) c hu hc
      have e1 : a + c * ((K + 1 : ℕ) : ℝ) = a + c * (K : ℝ) + c := by push_cast; ring
      rw [e1]
      linarith
  rcases K with _ | K
  · simp; positivity
  · have hpos : 0 ≤ 1 / (c * (a + c * (K : ℝ))) := by positivity
    linarith [key K]

/-- Assembly: if the one-step residual is at most `C/(a+ck)^2 + D q^k`, the total deviation
from the class function is bounded uniformly in the number of steps. -/
theorem uniform_deviation (x f : ℕ → ℝ) (a c C D q : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ k, |x (k + 1) - x k - (f (k + 1) - f k)| ≤ C * (1 / (a + c * k) ^ 2) + D * q ^ k)
    (K : ℕ) :
    |x K - x 0 - (f K - f 0)| ≤ C * (1 / a ^ 2 + 1 / (c * a)) + D / (1 - q) := by
  have h1 := telescoping_residual x f _ h K
  rw [sum_add_distrib, ← mul_sum] at h1
  have h2 := inv_sq_sum_le a c ha hc K
  have h3 := geometric_part_le D q hD hq0 hq1 K
  calc |x K - x 0 - (f K - f 0)| ≤ C * ∑ k ∈ range K, 1 / (a + c * k) ^ 2
        + ∑ k ∈ range K, D * q ^ k := h1
    _ ≤ C * (1 / a ^ 2 + 1 / (c * a)) + D / (1 - q) := by
        have := mul_le_mul_of_nonneg_left h2 hC
        linarith

end LatticeGaugeClassResidualTelescoping

#print axioms LatticeGaugeClassResidualTelescoping.telescoping_residual
#print axioms LatticeGaugeClassResidualTelescoping.telescoping_residual_multi
#print axioms LatticeGaugeClassResidualTelescoping.geometric_part_le
#print axioms LatticeGaugeClassResidualTelescoping.inv_sq_step
#print axioms LatticeGaugeClassResidualTelescoping.inv_sq_sum_le
#print axioms LatticeGaugeClassResidualTelescoping.uniform_deviation
