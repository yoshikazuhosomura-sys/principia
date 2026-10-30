/-
Definitions of the background constants to be measured (τ_bg, ℓ_bg, a_bg, K₀), in the form used by the chain fields.
Single file; checks with `import Mathlib` only. Includes a copy of CThetaReadings (unchanged up to comments).

  Background B(V): minimiser of the Wilson action with the coarse variable V fixed (block average QU = V; Bałaban's form).
  From the smallest eigenvalue λ_min of the constrained Hessian H_c(B) and the operator norm c_Q of the constraint,
      λ_min ‖δB‖ ≤ c_Q ‖δV‖  ⇒  ‖δB‖ ≤ c_Q ‖δV‖ / λ_min
  Inserting (H-gap) λ_min ≥ λ₀(1 − f₁/0.679) (HessianGap) and λ₀ = 0.500 (flux, cov, 8⁴ (floating-point computation))
  gives ‖δB‖ ≤ 4.88 c_Q ‖δV‖ for f₁ ≤ 0.4.
  The values of c_Q, τ_bg, a_bg are (assumed).
-/
import Mathlib

/-! Copy of CThetaReadings (unchanged up to comments) -/
namespace CThetaReadings

/-- (A): C_θ = 1/θ_c ≥ 1.19 > 0.0725 when θ_c ≤ 0.84. -/
theorem hessian_reading_fails (θc : ℝ) (h0 : 0 < θc) (h : θc ≤ 0.84) :
    (0.0725 : ℝ) < 1 / θc := by
  rw [lt_div_iff₀ h0]; nlinarith

/-- (A): r = θ/θ_c ≤ 0.029 requires θ ≤ 0.029 θ_c ≤ 0.0244, below the clover median 0.138. -/
theorem hessian_reading_theta_max (θ θc : ℝ) (h0 : 0 < θc) (h : θc ≤ 0.84)
    (hr : θ / θc ≤ 0.029) : θ ≤ 0.0244 ∧ θ < 0.138 := by
  have : θ ≤ 0.029 * θc := by rwa [div_le_iff₀ h0] at hr
  constructor <;> nlinarith

/-- (B): at θ = 0.4, N₆ ≤ 2.17 gives N₆ θ²/12 ≤ 0.029. -/
theorem coefficient_reading_04 (N6 : ℝ) (h : N6 ≤ 2.17) :
    N6 * 0.4 ^ 2 / 12 ≤ (0.029 : ℝ) := by
  have : N6 * 0.4 ^ 2 / 12 ≤ 2.17 * 0.4 ^ 2 / 12 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right h (by norm_num)
  linarith [show (2.17 : ℝ) * 0.4 ^ 2 / 12 ≤ 0.029 by norm_num]

/-- (B): at θ = 0.68 (edge of analyticity), N₆ ≥ 1 gives N₆ θ²/12 > 0.029. -/
theorem coefficient_reading_068 (N6 : ℝ) (h : 1 ≤ N6) : (0.029 : ℝ) < N6 * 0.68 ^ 2 / 12 := by
  have : (1 : ℝ) * 0.68 ^ 2 / 12 ≤ N6 * 0.68 ^ 2 / 12 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right h (by norm_num)
  linarith [show (0.029 : ℝ) < 1 * 0.68 ^ 2 / 12 by norm_num]

/-- (A′): from the Hessian lower bound `λ_min(θ) ≥ λ₀(1 − θ/θ_c)` and `λ_min ‖x‖ ≤ ‖b‖`, get `‖x‖ ≤ ‖b‖/(λ₀(1 − θ/θ_c))`. -/
theorem minimizer_lipschitz (lam lam0 θ θc x b : ℝ) (hl0 : 0 < lam0) (hθc : 0 < θc) (hθ : θ < θc)
    (hlam : lam0 * (1 - θ / θc) ≤ lam) (hx : 0 ≤ x) (h : lam * x ≤ b) :
    x ≤ b / (lam0 * (1 - θ / θc)) := by
  have h1 : 0 < 1 - θ / θc := by rw [sub_pos, div_lt_one hθc]; exact hθ
  have h2 : 0 < lam0 * (1 - θ / θc) := mul_pos hl0 h1
  rw [le_div_iff₀ h2]
  nlinarith

/-- (A′): K_bg(θ) = K₀/(1 − θ/θ_c) is monotone for θ ≤ θ′ < θ_c. -/
theorem K_bg_mono (K0 θ θ' θc : ℝ) (hK : 0 ≤ K0) (hθc : 0 < θc) (h : θ ≤ θ') (h' : θ' < θc) :
    K0 / (1 - θ / θc) ≤ K0 / (1 - θ' / θc) := by
  have h1 : 0 < 1 - θ' / θc := by rw [sub_pos, div_lt_one hθc]; exact h'
  apply div_le_div_of_nonneg_left hK h1
  have : θ / θc ≤ θ' / θc := div_le_div_of_nonneg_right h hθc.le
  linarith

/-- (A′): K_bg ≤ 2.43 K₀ at θ = 0.4, θ_c = 0.68. -/
theorem K_bg_value (K0 : ℝ) (hK : 0 ≤ K0) : K0 / (1 - 0.4 / 0.68) ≤ 2.43 * K0 := by
  have e : K0 / (1 - 0.4 / 0.68) = (0.68 / 0.28) * K0 := by field_simp; ring
  rw [e]
  have : (0.68 / 0.28 : ℝ) ≤ 2.43 := by norm_num
  nlinarith

#print axioms hessian_reading_fails
#print axioms hessian_reading_theta_max
#print axioms coefficient_reading_04
#print axioms coefficient_reading_068
#print axioms minimizer_lipschitz
#print axioms K_bg_mono
#print axioms K_bg_value

end CThetaReadings

namespace BackgroundConstants

/-- Background constants to be measured (a bundle of Props). `dB` is the norm of the background difference, `dV` the norm of the coarse-variable difference, `f1` the background invariant. -/
structure BackgroundBounds (lam0 cQ θc f1 lam dB dV : ℝ) : Prop where
  lam0_pos : 0 < lam0
  θc_pos : 0 < θc
  f1_lt : f1 < θc
  gap : lam0 * (1 - f1 / θc) ≤ lam
  dB_nonneg : 0 ≤ dB
  constrained : lam * dB ≤ cQ * dV

/-- Background Lipschitz bound: `‖δB‖ ≤ c_Q ‖δV‖ / (λ₀(1 − f₁/θ_c))`. -/
theorem background_lipschitz (lam0 cQ θc f1 lam dB dV : ℝ)
    (H : BackgroundBounds lam0 cQ θc f1 lam dB dV) :
    dB ≤ cQ * dV / (lam0 * (1 - f1 / θc)) :=
  CThetaReadings.minimizer_lipschitz lam lam0 f1 θc dB (cQ * dV) H.lam0_pos H.θc_pos H.f1_lt
    H.gap H.dB_nonneg H.constrained

/-- Numerical values: if λ₀ = 0.5, θ_c = 0.679, f₁ ≤ 0.4 and c_Q‖δV‖ ≥ 0, then `‖δB‖ ≤ 4.88 c_Q ‖δV‖`. -/
theorem background_lipschitz_numbers (cQ f1 lam dB dV : ℝ) (hf4 : f1 ≤ 0.4)
    (hcv : 0 ≤ cQ * dV)
    (H : BackgroundBounds 0.5 cQ 0.679 f1 lam dB dV) : dB ≤ 4.88 * (cQ * dV) := by
  have h := background_lipschitz 0.5 cQ 0.679 f1 lam dB dV H
  have h1 : (0.205 : ℝ) ≤ 0.5 * (1 - f1 / 0.679) := by
    have : f1 / 0.679 ≤ 0.4 / 0.679 := div_le_div_of_nonneg_right hf4 (by norm_num)
    have h2 : (0.41 : ℝ) ≤ 1 - 0.4 / 0.679 := by norm_num
    nlinarith
  have h3 : cQ * dV / (0.5 * (1 - f1 / 0.679)) ≤ cQ * dV / 0.205 :=
    div_le_div_of_nonneg_left hcv (by norm_num) h1
  have h4 : cQ * dV / 0.205 ≤ 4.88 * (cQ * dV) := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

#print axioms background_lipschitz
#print axioms background_lipschitz_numbers

end BackgroundConstants
