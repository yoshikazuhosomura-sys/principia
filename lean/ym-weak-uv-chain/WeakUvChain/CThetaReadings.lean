/-
Arithmetic of two readings of C_θ in (P-geom). Single file; checks with `import Mathlib` only.

  (A) Hessian reading: the background field strength θ enters the fluctuation Hessian at linear order (the spin term 2[F, ·] in
      Lie-algebra coordinates), and positivity of the constrained Hessian is lost at θ_c ∈ [0.68, 0.84]. The relative operator-norm
      perturbation is δ(θ) ≈ θ/θ_c, i.e. C_θ ≈ 1/θ_c ∈ [1.19, 1.47]. C_θ ≤ 0.0725 fails. r ≤ 0.029 requires θ ≤ 0.029 θ_c ≤ 0.0244,
      below the clover median 0.138 at β = 28.
  (B) Action-coefficient reading: the relative size φ²/12 of the quartic term in the Wilson action 1 − cos φ = φ²/2 − φ⁴/24 + …,
      read with the normalisation factor N₆ of ‖·‖₆ as r ≈ N₆ θ²/12. At θ = 0.4, N₆ ≤ 2.17 gives r ≤ 0.029. At θ = 0.68 it fails even for N₆ = 1.
  (A′) Replacement under reading (A): the Lipschitz constant of the background minimiser has the form 1/λ_min(θ) ≥ …, giving
      K_bg(θ) = K₀/(1 − θ/θ_c). It is finite and monotone for θ < θ_c, and K_bg ≤ 2.43 K₀ at θ = 0.4, θ_c = 0.68.
-/
import Mathlib

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
