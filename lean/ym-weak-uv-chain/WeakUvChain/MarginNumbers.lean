/-
Numerical check of the margin inequality (with the window numbers). Single file; checks with `import Mathlib` only.

  Chain margin C_s/u⋆ + D Z ≤ b/2, b = 2 b₀ ln 4, b₀ = 22/(48π²) (SU(2) one loop).
  Small-field constant C_s = ‖ψ‖ c₀ (1 + a c₀/((1−λ)² u⋆)), λ = τ + a r, r = (1−τ)/(4a) (window radius), so λ = (3τ+1)/4.
  With the window numbers τ = 0.6953, a = 4.3348, c₀ = 0.04 (floating-point computation), the margin holds
  for β = 28 (u⋆ = 7) if ‖ψ‖ ≤ 7 and DZ ≤ 0.004, and for β = 54 (u⋆ = 13.5) if ‖ψ‖ ≤ 16 and DZ ≤ 0.002.
  b/2 is bounded below using π < 3.1416 and log 2 > 0.6931471803 (Mathlib).
-/
import Mathlib

namespace MarginNumbers

/-- Lower bound for `b/2 = b₀ ln 4`. -/
theorem half_b_lower : (0.0643 : ℝ) ≤ 22 / (48 * Real.pi ^ 2) * Real.log 4 := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4]
  have hpi2 : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
  have hden : 0 < 48 * Real.pi ^ 2 := by positivity
  have h1 : 22 / (48 * 3.1416 ^ 2) ≤ 22 / (48 * Real.pi ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) hden; nlinarith
  have h2 : (0.0643 : ℝ) ≤ 22 / (48 * 3.1416 ^ 2) * (2 * 0.6931471803) := by norm_num
  have h3 : 22 / (48 * 3.1416 ^ 2) * (2 * 0.6931471803) ≤ 22 / (48 * Real.pi ^ 2) * (2 * Real.log 2) := by
    apply mul_le_mul h1 (by linarith) (by norm_num) (by positivity)
  linarith

/-- Margin for β = 28 (u⋆ = 7). -/
theorem margin_beta28 (ψ DZ : ℝ) (hψ : ψ ≤ 7) (hDZ : DZ ≤ 0.004) :
    ψ * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7)) / 7 + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 4 := by
  have hb := half_b_lower
  have hF : (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) : ℝ) ≤ 1.475 := by norm_num
  have hF0 : (0 : ℝ) ≤ 1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) := by norm_num
  have : ψ * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7)) / 7 ≤
      7 * 0.04 * 1.475 / 7 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (mul_le_mul_of_nonneg_right hψ (by norm_num)) hF hF0 (by norm_num)
  norm_num at this ⊢
  linarith

/-- Margin for β = 54 (u⋆ = 13.5). -/
theorem margin_beta54 (ψ DZ : ℝ) (hψ : ψ ≤ 16) (hDZ : DZ ≤ 0.002) :
    ψ * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5)) / 13.5 + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 4 := by
  have hb := half_b_lower
  have hF : (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) : ℝ) ≤ 1.246 := by norm_num
  have hF0 : (0 : ℝ) ≤ 1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) := by norm_num
  have : ψ * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5)) / 13.5 ≤
      16 * 0.04 * 1.246 / 13.5 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (mul_le_mul_of_nonneg_right hψ (by norm_num)) hF hF0 (by norm_num)
  norm_num at this ⊢
  linarith

/-- λ at the window radius: `τ + a · (1−τ)/(4a) = (3τ+1)/4` (a > 0). -/
theorem lambda_window (τ a : ℝ) (ha : 0 < a) : τ + a * ((1 - τ) / (4 * a)) = (3 * τ + 1) / 4 := by
  field_simp; ring

#print axioms half_b_lower
#print axioms margin_beta28
#print axioms margin_beta54
#print axioms lambda_window

end MarginNumbers
