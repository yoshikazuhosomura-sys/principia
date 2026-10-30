/-
Restates the margin inequality for one step at scale factor 2. Single file; checks with `import Mathlib` only.
MarginNumbers (factor 4: b = 2b₀ ln 4, b/2 = b₀ ln 4 ≥ 0.0643) is left unchanged.

  The numbers (τ = 0.6953, a = 4.3348, c₀) are those of one factor-2 step. At factor 2, b = 2b₀ ln 2 and
  b/2 = b₀ ln 2 ∈ [0.03218, 0.0322).
  λ = (3τ+1)/4, window radius r = (1−τ)/(4a), closed-ball condition c₀/u ≤ (1−λ) r = 3(1−τ)²/(16a) ∈ [0.004015, 0.004016].
  §1 Bounds for b/2  §2 Closed-ball condition: c₀ = 0.022 needs u ≥ 5.48 (β ≥ 21.92); c₀ = 0.04 fails at u = 7 and
     holds for u ≥ 9.97 (β ≥ 39.88)
  §3 The form ‖ψ‖ = u⋆: for c₀ = 0.022, β = 28 fits up to DZ ≤ 0.0044; c₀ = 0.04 fits for no u⋆
  §4 The ker φ form (|δλ| + C₂/u, C₂ = a c₀²/(1−λ)², |δλ| ≤ 0.022): for c₀ = 0.022, β = 28 gives DZ ≤ 0.0044;
     for c₀ = 0.04, β = 54 gives DZ ≤ 0.0003, and β = 40 (u⋆ = 10) fails even with DZ = 0
  All numbers are arithmetic on (floating-point computation) inputs; the input values themselves are not checked here.
-/
import Mathlib

namespace MarginRatioTwo

/-! ## 1. Upper and lower bounds for b/2 = b₀ ln 2 -/

theorem half_b2_lower : (0.03218 : ℝ) ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hden : 0 < 48 * Real.pi ^ 2 := by positivity
  have h1 : 22 / (48 * 3.1416 ^ 2) ≤ 22 / (48 * Real.pi ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) hden; nlinarith
  have h2 : (0.03218 : ℝ) ≤ 22 / (48 * 3.1416 ^ 2) * 0.6931471803 := by norm_num
  have h3 : 22 / (48 * 3.1416 ^ 2) * 0.6931471803 ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
    mul_le_mul h1 hlog2.le (by norm_num) (by positivity)
  linarith

theorem half_b2_upper : 22 / (48 * Real.pi ^ 2) * Real.log 2 < (0.0322 : ℝ) := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hlog2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 22 / (48 * Real.pi ^ 2) ≤ 22 / (48 * 3.1415 ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
  have h2 : 22 / (48 * 3.1415 ^ 2) * (0.6931471808 : ℝ) < 0.0322 := by norm_num
  have h3 : 22 / (48 * Real.pi ^ 2) * Real.log 2 ≤ 22 / (48 * 3.1415 ^ 2) * 0.6931471808 :=
    mul_le_mul h1 hlog2.le hlog0.le (by norm_num)
  linarith

/-! ## 2. Closed-ball condition -/

/-- The value of `(1−λ) r = 3(1−τ)²/(16a)` at the window numbers. -/
theorem ball_bound_value :
    (0.004015 : ℝ) ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) ∧
    (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) ≤ (0.004016 : ℝ) := by
  constructor <;> norm_num

/-- c₀ = 0.022: the closed-ball condition holds if `u ≥ 5.48` (β = 4u ≥ 21.92). -/
theorem ball_c022 (u : ℝ) (hu : 5.48 ≤ u) :
    0.022 / u ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) := by
  have hb := ball_bound_value.1
  have hu0 : 0 < u := by linarith
  rw [div_le_iff₀ hu0]; nlinarith

/-- c₀ = 0.04: the closed-ball condition fails at β = 28 (u = 7). -/
theorem ball_c04_fails_beta28 :
    (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) < (0.04 : ℝ) / 7 := by
  norm_num

/-- c₀ = 0.04: the closed-ball condition holds if `u ≥ 9.97` (β ≥ 39.88). -/
theorem ball_c04 (u : ℝ) (hu : 9.97 ≤ u) :
    0.04 / u ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) := by
  have hb := ball_bound_value.1
  have hu0 : 0 < u := by linarith
  rw [div_le_iff₀ hu0]; nlinarith

/-! ## 3. The form ‖ψ‖ = u⋆ -/

/-- β = 28, c₀ = 0.022, ‖ψ‖ ≤ 7: the margin at factor 2 holds up to DZ ≤ 0.0044. -/
theorem margin2_beta28_c022 (ψ DZ : ℝ) (hψ : ψ ≤ 7) (hDZ : DZ ≤ 0.0044) :
    ψ * 0.022 * (1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7)) / 7 + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hb := half_b2_lower
  have hF : (1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) : ℝ) ≤ 1.261 := by norm_num
  have hF0 : (0 : ℝ) ≤ 1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) := by norm_num
  have : ψ * 0.022 * (1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7)) / 7 ≤
      7 * 0.022 * 1.261 / 7 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (mul_le_mul_of_nonneg_right hψ (by norm_num)) hF hF0 (by norm_num)
  norm_num at this ⊢
  linarith

/-- With ‖ψ‖ = u⋆, c₀ = 0.04 never fits the factor-2 margin for any u⋆ > 0:
`u⋆ · c₀ · F / u⋆ = c₀ F ≥ c₀ = 0.04 > b₀ ln 2`. -/
theorem margin2_c04_fform_fails (ustar DZ : ℝ) (hus : 0 < ustar) (hDZ : 0 ≤ DZ) :
    22 / (48 * Real.pi ^ 2) * Real.log 2 <
      ustar * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar)) / ustar + DZ := by
  have hb := half_b2_upper
  have hF : (1 : ℝ) ≤ 1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar) := by
    have : (0 : ℝ) ≤ 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar) := by positivity
    linarith
  have e : ustar * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar)) / ustar =
      0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar)) := by
    field_simp
  rw [e]; nlinarith

/-! ## 4. The ker φ form: |δλ| + C₂/u -/

/-- β = 28 (u⋆ = 7), c₀ = 0.022, |δλ| ≤ 0.022: holds up to DZ ≤ 0.0044. -/
theorem margin2_ker_beta28_c022 (δ DZ : ℝ) (hδ : |δ| ≤ 0.022) (hDZ : DZ ≤ 0.0044) :
    |δ| + 4.3348 * 0.022 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hb := half_b2_lower
  have hC : (4.3348 * 0.022 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) : ℝ) ≤ 0.00574 := by norm_num
  linarith

/-- β = 54 (u⋆ = 13.5), c₀ = 0.04, |δλ| ≤ 0.022: holds up to DZ ≤ 0.0003. -/
theorem margin2_ker_beta54_c04 (δ DZ : ℝ) (hδ : |δ| ≤ 0.022) (hDZ : DZ ≤ 0.0003) :
    |δ| + 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hb := half_b2_lower
  have hC : (4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) : ℝ) ≤ 0.00984 := by
    norm_num
  linarith

/-- β = 40 (u⋆ = 10), c₀ = 0.04, at the edge δλ = 0.022: fails even with DZ = 0. -/
theorem margin2_ker_beta40_c04_fails (DZ : ℝ) (hDZ : 0 ≤ DZ) :
    22 / (48 * Real.pi ^ 2) * Real.log 2 <
      0.022 + 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 10) + DZ := by
  have hb := half_b2_upper
  have hC : (0.0132 : ℝ) ≤ 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 10) := by
    norm_num
  linarith

#print axioms half_b2_lower
#print axioms half_b2_upper
#print axioms ball_bound_value
#print axioms ball_c022
#print axioms ball_c04_fails_beta28
#print axioms ball_c04
#print axioms margin2_beta28_c022
#print axioms margin2_c04_fform_fails
#print axioms margin2_ker_beta28_c022
#print axioms margin2_ker_beta54_c04
#print axioms margin2_ker_beta40_c04_fails

end MarginRatioTwo
