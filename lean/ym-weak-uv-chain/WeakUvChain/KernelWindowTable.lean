/-
Checks the points of the table of window lower ends and DZ not covered by KernelMarginStages (β = 30, 43, 54).
Single file; checks with `import Mathlib` only. Starts with a copy of KernelMarginStages (which contains a copy of
MarginRatioTwo; unchanged up to comments).

  β = 30 (u = 7.5): τ₁, ℓ = 0 is outside the window; τ₃, ℓ = 0 is inside (DZ ≤ 0.0053).
  β = 43 (u = 10.75), 54 (u = 13.5): inside the window even for the hardest case ℓ = 0.36, τ₁ (DZ ≤ 0.0054, 0.0066).
  For each ℓ, the smallest β (among the table points) where the window holds for all τ rows: 33 for ℓ = 0,
  38 for 0.16, 43 for 0.36.
-/
import Mathlib

/-! Copy of MarginRatioTwo (unchanged up to comments) -/
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

/-! Copy of KernelMarginStages (unchanged up to comments) -/
namespace KernelMarginStages

/-! ## 1. Window condition -/

/-- Window condition (type of window_from_loc_A): `L = ℓ/u + 2ar`, `τ + L < 1`, `c₀/u + (τ + L) r ≤ r`. -/
def WindowCond (τ ℓ a c₀ u r : ℝ) : Prop :=
  τ + (ℓ / u + 2 * a * r) < 1 ∧ c₀ / u + (τ + (ℓ / u + 2 * a * r)) * r ≤ r

/-- Necessary: if the window condition holds then `c₀/u ≤ κ²/(8a)`, `κ = 1 − τ − ℓ/u`. -/
theorem window_necessary (τ ℓ a c₀ u r : ℝ) (ha : 0 < a)
    (h : WindowCond τ ℓ a c₀ u r) : c₀ / u ≤ (1 - τ - ℓ / u) ^ 2 / (8 * a) := by
  obtain ⟨_, h2⟩ := h
  rw [le_div_iff₀ (by positivity)]
  have hsq : 0 ≤ ((1 - τ - ℓ / u) - 4 * a * r) ^ 2 := sq_nonneg _
  nlinarith

/-- Sufficient: if `κ > 0` and `c₀/u ≤ κ²/(8a)`, the window condition holds with `r = κ/(4a)`. -/
theorem window_sufficient (τ ℓ a c₀ u : ℝ) (ha : 0 < a) (hκ : 0 < 1 - τ - ℓ / u)
    (h : c₀ / u ≤ (1 - τ - ℓ / u) ^ 2 / (8 * a)) :
    WindowCond τ ℓ a c₀ u ((1 - τ - ℓ / u) / (4 * a)) := by
  set κ := 1 - τ - ℓ / u with hk
  have e : 2 * a * (κ / (4 * a)) = κ / 2 := by field_simp; ring
  refine ⟨by rw [e]; linarith, ?_⟩
  rw [e]
  have e2 : (τ + (ℓ / u + κ / 2)) * (κ / (4 * a)) = κ / (4 * a) - κ ^ 2 / (8 * a) := by
    rw [hk]; field_simp; ring
  rw [e2]; linarith

/-! ## 2. β = 28 lies outside the window -/

theorem window_beta28_fails_tau1 (r : ℝ) : ¬ WindowCond 0.6953 0 4.3348 0.022 7 r := by
  intro h
  have := window_necessary 0.6953 0 4.3348 0.022 7 r (by norm_num) h
  norm_num at this

theorem window_beta28_fails_tau3 (r : ℝ) : ¬ WindowCond 0.6804 0 4.3348 0.022 7 r := by
  intro h
  have := window_necessary 0.6804 0 4.3348 0.022 7 r (by norm_num) h
  norm_num at this

/-! ## 3. Cases β = 33, 36, 38 -/

theorem window_33_tau1_l0 : WindowCond 0.6953 0 4.3348 0.022 8.25 0.01757 := by
  unfold WindowCond; norm_num

theorem window_33_tau3_l0 : WindowCond 0.6804 0 4.3348 0.022 8.25 0.01843 := by
  unfold WindowCond; norm_num

theorem window_33_tau3_l16_fails (r : ℝ) :
    ¬ WindowCond 0.6804 0.16 4.3348 0.022 8.25 r := by
  intro h
  have := window_necessary 0.6804 0.16 4.3348 0.022 8.25 r (by norm_num) h
  norm_num at this

theorem window_36_tau1_l16_fails (r : ℝ) :
    ¬ WindowCond 0.6953 0.16 4.3348 0.022 9 r := by
  intro h
  have := window_necessary 0.6953 0.16 4.3348 0.022 9 r (by norm_num) h
  norm_num at this

theorem window_36_tau3_l16 : WindowCond 0.6804 0.16 4.3348 0.022 9 0.0174 := by
  unfold WindowCond; norm_num

theorem window_38_tau1_l16 : WindowCond 0.6953 0.16 4.3348 0.022 9.5 0.0166 := by
  unfold WindowCond; norm_num

theorem window_38_tau3_l36_fails (r : ℝ) :
    ¬ WindowCond 0.6804 0.36 4.3348 0.022 9.5 r := by
  intro h
  have := window_necessary 0.6804 0.36 4.3348 0.022 9.5 r (by norm_num) h
  norm_num at this

/-! ## 4. Margin for the cases where the window holds -/

/-- Quadratic term on the small closed ball: `C₂/u = a c₀²/(((3/4)κ)² u)` (λ = τ + ℓ/u + a r; with r = κ/(4a),
1 − λ = (3/4)κ). -/
noncomputable def C2u (τ ℓ u : ℝ) : ℝ := 4.3348 * 0.022 ^ 2 / ((3 / 4 * (1 - τ - ℓ / u)) ^ 2 * u)

/-- Check of `1 − λ = (3/4)κ`. -/
theorem one_sub_lambda (τ ℓ u a : ℝ) (ha : 0 < a) :
    1 - (τ + ℓ / u + a * ((1 - τ - ℓ / u) / (4 * a))) = 3 / 4 * (1 - τ - ℓ / u) := by
  field_simp; ring

theorem margin_of (X Y Cu DZ : ℝ) (hC : Cu ≤ X) (hDZ : DZ ≤ Y) (hsum : 0.022 + X + Y ≤ 0.03218) :
    0.022 + Cu + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have := MarginRatioTwo.half_b2_lower; linarith

theorem margin_33_tau1_l0 (DZ : ℝ) (h : DZ ≤ 0.0053) :
    0.022 + C2u 0.6953 0 8.25 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00487 0.0053 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_33_tau3_l0 (DZ : ℝ) (h : DZ ≤ 0.0057) :
    0.022 + C2u 0.6804 0 8.25 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00444 0.0057 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_36_tau1_l0 (DZ : ℝ) (h : DZ ≤ 0.0057) :
    0.022 + C2u 0.6953 0 9 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00447 0.0057 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_36_tau3_l0 (DZ : ℝ) (h : DZ ≤ 0.0061) :
    0.022 + C2u 0.6804 0 9 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00407 0.0061 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_36_tau3_l16 (DZ : ℝ) (h : DZ ≤ 0.0056) :
    0.022 + C2u 0.6804 0.16 9 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00456 0.0056 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_38_tau1_l0 (DZ : ℝ) (h : DZ ≤ 0.0059) :
    0.022 + C2u 0.6953 0 9.5 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00424 0.0059 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_38_tau1_l16 (DZ : ℝ) (h : DZ ≤ 0.0054) :
    0.022 + C2u 0.6953 0.16 9.5 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00475 0.0054 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_38_tau3_l0 (DZ : ℝ) (h : DZ ≤ 0.0063) :
    0.022 + C2u 0.6804 0 9.5 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00385 0.0063 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_38_tau3_l16 (DZ : ℝ) (h : DZ ≤ 0.0058) :
    0.022 + C2u 0.6804 0.16 9.5 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00429 0.0058 _ DZ (by unfold C2u; norm_num) h (by norm_num)

#print axioms window_necessary
#print axioms window_sufficient
#print axioms window_beta28_fails_tau1
#print axioms window_beta28_fails_tau3
#print axioms window_33_tau1_l0
#print axioms window_33_tau3_l0
#print axioms window_33_tau3_l16_fails
#print axioms window_36_tau1_l16_fails
#print axioms window_36_tau3_l16
#print axioms window_38_tau1_l16
#print axioms window_38_tau3_l36_fails
#print axioms one_sub_lambda
#print axioms margin_of
#print axioms margin_33_tau1_l0
#print axioms margin_33_tau3_l0
#print axioms margin_36_tau1_l0
#print axioms margin_36_tau3_l0
#print axioms margin_36_tau3_l16
#print axioms margin_38_tau1_l0
#print axioms margin_38_tau1_l16
#print axioms margin_38_tau3_l0
#print axioms margin_38_tau3_l16

end KernelMarginStages

namespace KernelWindowTable

open KernelMarginStages

theorem window_30_tau1_l0_fails (r : ℝ) : ¬ WindowCond 0.6953 0 4.3348 0.022 7.5 r := by
  intro h
  have := window_necessary 0.6953 0 4.3348 0.022 7.5 r (by norm_num) h
  norm_num at this

theorem window_30_tau3_l0 :
    WindowCond 0.6804 0 4.3348 0.022 7.5 ((1 - 0.6804 - 0 / 7.5) / (4 * 4.3348)) :=
  window_sufficient 0.6804 0 4.3348 0.022 7.5 (by norm_num) (by norm_num) (by norm_num)

theorem window_43_tau1_l36 :
    WindowCond 0.6953 0.36 4.3348 0.022 10.75 ((1 - 0.6953 - 0.36 / 10.75) / (4 * 4.3348)) :=
  window_sufficient 0.6953 0.36 4.3348 0.022 10.75 (by norm_num) (by norm_num) (by norm_num)

theorem window_54_tau1_l36 :
    WindowCond 0.6953 0.36 4.3348 0.022 13.5 ((1 - 0.6953 - 0.36 / 13.5) / (4 * 4.3348)) :=
  window_sufficient 0.6953 0.36 4.3348 0.022 13.5 (by norm_num) (by norm_num) (by norm_num)

theorem window_38_tau1_l36_fails (r : ℝ) : ¬ WindowCond 0.6953 0.36 4.3348 0.022 9.5 r := by
  intro h
  have := window_necessary 0.6953 0.36 4.3348 0.022 9.5 r (by norm_num) h
  norm_num at this

theorem window_36_tau1_l16_fails' (r : ℝ) : ¬ WindowCond 0.6953 0.16 4.3348 0.022 9 r :=
  window_36_tau1_l16_fails r

theorem margin_30_tau3_l0 (DZ : ℝ) (h : DZ ≤ 0.0053) :
    0.022 + C2u 0.6804 0 7.5 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00487 0.0053 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_43_tau1_l36 (DZ : ℝ) (h : DZ ≤ 0.0054) :
    0.022 + C2u 0.6953 0.36 10.75 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00472 0.0054 _ DZ (by unfold C2u; norm_num) h (by norm_num)

theorem margin_54_tau1_l36 (DZ : ℝ) (h : DZ ≤ 0.0066) :
    0.022 + C2u 0.6953 0.36 13.5 + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
  margin_of 0.00358 0.0066 _ DZ (by unfold C2u; norm_num) h (by norm_num)

/-- The measured DZ ≈ 2e−3 (β = 28, (floating-point computation); 4e−3 even with Z = 2z) is within the bound
(≥ 0.0053) of every case in the table where the window holds. -/
theorem measured_inside (DZ : ℝ) (h : DZ ≤ 0.004) : DZ ≤ 0.0053 := by linarith

#print axioms window_30_tau1_l0_fails
#print axioms window_30_tau3_l0
#print axioms window_43_tau1_l36
#print axioms window_54_tau1_l36
#print axioms window_38_tau1_l36_fails
#print axioms window_36_tau1_l16_fails'
#print axioms margin_30_tau3_l0
#print axioms margin_43_tau1_l36
#print axioms margin_54_tau1_l36
#print axioms measured_inside

end KernelWindowTable
