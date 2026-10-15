import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The one-step map of the Van Vleck prefactor exponent (algebraic layer)

Class functions on SU(2) of the form `f = exp(-B ψ²/2 + h(ψ))`, `h = O(1)`, and the one-step
kernel `f'² = (f∗f)∗f²`. With `P = ψ / sin ψ` and `log P = Σ p_k ψ^{2k}`, the saddle-point
(Laplace) computation gives, coefficient by coefficient, for the exponent `γ_k := h_k / p_k`
read at `ψ^{2k}`:
`γ'_k = L_k (γ_k - 1) + I_k`, `L_k = (4^k+1)/25^k`, `I_k = (1 + 25^{-k})/2`.

* `step_k2` : at `ψ⁴`, `γ' = (17γ + 296)/625`.
* `step_k2_heat` : the heat-kernel exponent `γ = 1` goes to `313/625`.
* `step_k2_fixed_iff` : the unique fixed point at `ψ⁴` is `37/76`.
* `step_k2_contract` : `|γ' - 37/76| = (17/625) |γ - 37/76|`.
* `fixed_point_general` : with `x = 25^k`, `y = 4^k` (as reals, `x ≠ 0`, `x - y - 1 ≠ 0`),
  `γ* = (x - 2y - 1)/(2(x - y - 1))` is a fixed point of `γ ↦ ((y+1)/x)(γ-1) + (1+1/x)/2`.
* `half_sub_gamma_star` : `1/2 - γ* = y/(2(x - y - 1))`.
* `transverse_hessian` : `(k/a)·a cot a + (k/b)·b cot b = k sin(a+b)/(sin a sin b)`
  (transverse Hessian of `B₁d₁²/2 + B₂d₂²/2` on the unit three-sphere at a collinear saddle,
  `k = B₁a = B₂b`).
* `convolution_prefactor` : `P(a) P(b) · sin a sin b / sin(a+b) = (ab/(a+b)) · P(a+b)`.
* `rem_shape_geometric` : `r(n+1) ≤ λ r(n) + C 5ⁿ/B₀` with `0 ≤ λ < 5`, `B₀ > 0`, `C ≥ 0` gives
  `r(n) ≤ λⁿ r(0) + C/((5-λ)B₀) · 5ⁿ` (with `B_n = B₀/5ⁿ` the last term is `C/((5-λ)B_n)`).
* `ratio_coefficient` : `(2/5)/(3/5) = 2/3`.

Only the algebra is formalised: the convolution, the Laplace (saddle-point) reduction on the
group and the one-loop formula for `D` are not.
-/

namespace LatticeGaugePrefactorFlowFixedPoint

/-- The affine one-step map of the prefactor exponent read at one Taylor order. -/
def stepMap (L I γ : ℝ) : ℝ := L * (γ - 1) + I

theorem step_k2 (γ : ℝ) : stepMap (17 / 625) ((1 + 1 / 625) / 2) γ = (17 * γ + 296) / 625 := by
  unfold stepMap; ring

theorem step_k2_heat : stepMap (17 / 625) ((1 + 1 / 625) / 2) 1 = 313 / 625 := by
  unfold stepMap; norm_num

theorem step_k2_fixed_iff (γ : ℝ) :
    stepMap (17 / 625) ((1 + 1 / 625) / 2) γ = γ ↔ γ = 37 / 76 := by
  unfold stepMap
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

theorem step_k2_contract (γ : ℝ) :
    |stepMap (17 / 625) ((1 + 1 / 625) / 2) γ - 37 / 76| = (17 / 625) * |γ - 37 / 76| := by
  have e : stepMap (17 / 625) ((1 + 1 / 625) / 2) γ - 37 / 76 = (17 / 625) * (γ - 37 / 76) := by
    unfold stepMap; ring
  rw [e, abs_mul]; norm_num

theorem fixed_point_general (x y : ℝ) (hx : x ≠ 0) (hd : x - y - 1 ≠ 0) :
    stepMap ((y + 1) / x) ((1 + 1 / x) / 2) ((x - 2 * y - 1) / (2 * (x - y - 1)))
      = (x - 2 * y - 1) / (2 * (x - y - 1)) := by
  unfold stepMap
  field_simp
  ring

theorem fixed_point_k3 :
    stepMap ((64 + 1) / 15625) ((1 + 1 / 15625) / 2) (1937 / 3890) = 1937 / 3890 := by
  unfold stepMap; norm_num

theorem fixed_point_k4 :
    stepMap ((256 + 1) / 390625) ((1 + 1 / 390625) / 2) (12191 / 24398) = 12191 / 24398 := by
  unfold stepMap; norm_num

theorem half_sub_gamma_star (x y : ℝ) (hd : x - y - 1 ≠ 0) :
    1 / 2 - (x - 2 * y - 1) / (2 * (x - y - 1)) = y / (2 * (x - y - 1)) := by
  field_simp
  ring

theorem transverse_hessian (k a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsa : Real.sin a ≠ 0) (hsb : Real.sin b ≠ 0) :
    (k / a) * (a * Real.cos a / Real.sin a) + (k / b) * (b * Real.cos b / Real.sin b)
      = k * Real.sin (a + b) / (Real.sin a * Real.sin b) := by
  rw [Real.sin_add]
  field_simp
  ring

theorem convolution_prefactor (a b : ℝ) (hsa : Real.sin a ≠ 0) (hsb : Real.sin b ≠ 0)
    (hs : Real.sin (a + b) ≠ 0) (hab : a + b ≠ 0) :
    (a / Real.sin a) * (b / Real.sin b) * (Real.sin a * Real.sin b / Real.sin (a + b))
      = (a * b / (a + b)) * ((a + b) / Real.sin (a + b)) := by
  field_simp

theorem rem_shape_geometric (r : ℕ → ℝ) (lam C B0 : ℝ) (hl0 : 0 ≤ lam) (hl : lam < 5)
    (hB : 0 < B0) (hC : 0 ≤ C) (h : ∀ n : ℕ, r (n + 1) ≤ lam * r n + C * 5 ^ n / B0) :
    ∀ n : ℕ, r n ≤ lam ^ n * r 0 + C / ((5 - lam) * B0) * 5 ^ n := by
  have h5 : (5 - lam) ≠ 0 := by linarith
  have hB' : B0 ≠ 0 := ne_of_gt hB
  intro n
  induction n with
  | zero =>
    have h5p : 0 < 5 - lam := by linarith
    have : 0 ≤ C / ((5 - lam) * B0) := by positivity
    simp [this]
  | succ n ih =>
    have key : lam * (C / ((5 - lam) * B0) * 5 ^ n) + C * 5 ^ n / B0
        = C / ((5 - lam) * B0) * 5 ^ (n + 1) := by
      field_simp
      ring
    calc r (n + 1) ≤ lam * r n + C * 5 ^ n / B0 := h n
      _ ≤ lam * (lam ^ n * r 0 + C / ((5 - lam) * B0) * 5 ^ n) + C * 5 ^ n / B0 := by
          gcongr
      _ = lam ^ (n + 1) * r 0 + C / ((5 - lam) * B0) * 5 ^ (n + 1) := by
          rw [← key]; ring

theorem ratio_coefficient : (2 / 5 : ℝ) / (3 / 5) = 2 / 3 := by norm_num

end LatticeGaugePrefactorFlowFixedPoint

#print axioms LatticeGaugePrefactorFlowFixedPoint.step_k2
#print axioms LatticeGaugePrefactorFlowFixedPoint.step_k2_heat
#print axioms LatticeGaugePrefactorFlowFixedPoint.step_k2_fixed_iff
#print axioms LatticeGaugePrefactorFlowFixedPoint.step_k2_contract
#print axioms LatticeGaugePrefactorFlowFixedPoint.fixed_point_general
#print axioms LatticeGaugePrefactorFlowFixedPoint.fixed_point_k3
#print axioms LatticeGaugePrefactorFlowFixedPoint.fixed_point_k4
#print axioms LatticeGaugePrefactorFlowFixedPoint.half_sub_gamma_star
#print axioms LatticeGaugePrefactorFlowFixedPoint.transverse_hessian
#print axioms LatticeGaugePrefactorFlowFixedPoint.convolution_prefactor
#print axioms LatticeGaugePrefactorFlowFixedPoint.rem_shape_geometric
#print axioms LatticeGaugePrefactorFlowFixedPoint.ratio_coefficient
