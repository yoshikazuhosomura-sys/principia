import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

/-!
# Uniform geometric control of the shape remainder (one-row four-plaquette model, algebraic layer)

Projected one-step map of the SU(2) one-row four-plaquette model `f' = [(f∗f)∗f²]^{1/2}`
(diagonal definition), class functions `f = exp(-B ψ²/2 + h₂ψ⁴ + h₃ψ⁶ + h₄ψ⁸)`.
Distance to the attracting class: `r = max_k ρ^{2k} |h_k - h*_k|` (`k = 2,3,4`).
The analytic part (Laplace remainder via the ℝ³ lift and Cauchy estimates) is on paper;
here only the assembly and the finite algebra are formalised.

* `uv_uniform` : if `B (n+1) ≤ B n / 5` and `r (n+1) ≤ λ r n + C / B n` for `n < N`
  (`0 ≤ λ < 5`, `C ≥ 0`, `B n > 0`), then `r n ≤ λⁿ r 0 + C / ((5-λ) B n)` for `n ≤ N`.
  The scale `B n` is the actual scale after `n` steps (it decreases), so the residual is
  controlled at the final scale, uniformly in the number of steps taken from the ultraviolet.
* `stays_in_box` : `r ≤ r₀`, `λ r₀ + C/B ≤ r₀` and the one-step inequality give `r' ≤ r₀`.
* `pow_sub_pow_norm_le` : `‖s‖ ≤ A`, `‖d‖ ≤ D` give `‖(s+d)^k - s^k‖ ≤ (A+D)^k - A^k` in `ℂ`
  (the majorant step for `G(s + Δ) - G(s)`).
* `saddle_ratio_le`, `saddle_ratio_three`, `keff_half_le` : the stiffness-shifted saddle ratios
  `c₁ = (2B+1/3)/(5B+1) ≤ 2/5`, `0 ≤ c₃ - 1/5 ≤ 2/(75B)`, and
  `k_eff/2 = (B+1/3)(2B+1/3)/(2(5B+1)) ≤ B/5 + 3/50`.
* `cov_eigen` : the fluctuation covariance `κ = [[3,-2,-1],[-2,3,-1],[-1,-1,2]]/5` has
  `κ(1,1,1) = 0`, `κ(1,-1,0) = (1,-1,0)`, `κ(1,1,-2) = (3/5)(1,1,-2)`.
* `first_order_at_fixed_point` : substitution giving `(γ'₂ - 37/76) B → -591986/69290625`.
* `quadratic_shape_coefficient` : `22·464/15625 + 40·24/15625 = 11168/15625`.
-/

namespace LatticeGaugeShapeRemainderUniform

theorem uv_uniform (r B : ℕ → ℝ) (lam C : ℝ) (N : ℕ) (hl0 : 0 ≤ lam) (hl : lam < 5)
    (hC : 0 ≤ C) (hBpos : ∀ n, 0 < B n)
    (hBstep : ∀ n, n < N → 5 * B (n + 1) ≤ B n)
    (hstep : ∀ n, n < N → r (n + 1) ≤ lam * r n + C / B n) :
    ∀ n, n ≤ N → r n ≤ lam ^ n * r 0 + C / ((5 - lam) * B n) := by
  have h5 : 0 < 5 - lam := by linarith
  intro n
  induction n with
  | zero =>
    intro _
    have hB := hBpos 0
    have : 0 ≤ C / ((5 - lam) * B 0) := by positivity
    simp only [pow_zero, one_mul]
    linarith
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    have ih' := ih (by omega)
    have hB0 := hBpos n
    have hB1 := hBpos (n + 1)
    have key1 : lam * (C / ((5 - lam) * B n)) + C / B n = 5 * C / ((5 - lam) * B n) := by
      field_simp
      ring
    have key2 : 5 * C / ((5 - lam) * B n) ≤ C / ((5 - lam) * B (n + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hs := hBstep n hn'
      nlinarith [mul_nonneg (mul_nonneg hC h5.le) (sub_nonneg.mpr hs)]
    calc r (n + 1) ≤ lam * r n + C / B n := hstep n hn'
      _ ≤ lam * (lam ^ n * r 0 + C / ((5 - lam) * B n)) + C / B n := by
          have := mul_le_mul_of_nonneg_left ih' hl0
          linarith
      _ = lam ^ (n + 1) * r 0 + (lam * (C / ((5 - lam) * B n)) + C / B n) := by ring
      _ = lam ^ (n + 1) * r 0 + 5 * C / ((5 - lam) * B n) := by rw [key1]
      _ ≤ lam ^ (n + 1) * r 0 + C / ((5 - lam) * B (n + 1)) := by linarith

theorem stays_in_box (r r' r0 lam C B : ℝ) (hl0 : 0 ≤ lam) (hr : r ≤ r0)
    (hbox : lam * r0 + C / B ≤ r0) (hstep : r' ≤ lam * r + C / B) : r' ≤ r0 := by
  have := mul_le_mul_of_nonneg_left hr hl0
  linarith

theorem pow_sub_pow_norm_le (s d : ℂ) (A D : ℝ) (hs : ‖s‖ ≤ A) (hd : ‖d‖ ≤ D) :
    ∀ k : ℕ, ‖(s + d) ^ k - s ^ k‖ ≤ (A + D) ^ k - A ^ k := by
  have hA : 0 ≤ A := le_trans (norm_nonneg _) hs
  have hD : 0 ≤ D := le_trans (norm_nonneg _) hd
  have hsd : ‖s + d‖ ≤ A + D := le_trans (norm_add_le _ _) (by linarith)
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (s + d) ^ (k + 1) - s ^ (k + 1) = (s + d) * ((s + d) ^ k - s ^ k) + d * s ^ k := by
      ring
    have hsk : ‖s ^ k‖ ≤ A ^ k := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hs k
    have hmono : A ^ k ≤ (A + D) ^ k := pow_le_pow_left₀ hA (by linarith) k
    have t1 : ‖s + d‖ * ‖(s + d) ^ k - s ^ k‖ ≤ (A + D) * ((A + D) ^ k - A ^ k) :=
      mul_le_mul hsd ih (norm_nonneg _) (by linarith)
    have t2 : ‖d‖ * ‖s ^ k‖ ≤ D * A ^ k := mul_le_mul hd hsk (norm_nonneg _) hD
    rw [e]
    calc ‖(s + d) * ((s + d) ^ k - s ^ k) + d * s ^ k‖
        ≤ ‖(s + d) * ((s + d) ^ k - s ^ k)‖ + ‖d * s ^ k‖ := norm_add_le _ _
      _ = ‖s + d‖ * ‖(s + d) ^ k - s ^ k‖ + ‖d‖ * ‖s ^ k‖ := by rw [norm_mul, norm_mul]
      _ ≤ (A + D) * ((A + D) ^ k - A ^ k) + D * A ^ k := by linarith
      _ = (A + D) ^ (k + 1) - A ^ (k + 1) := by ring

theorem saddle_ratio_le (B : ℝ) (hB : 0 < B) : (2 * B + 1 / 3) / (5 * B + 1) ≤ 2 / 5 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem saddle_ratio_three (B : ℝ) (hB : 0 < B) :
    0 ≤ (B + 1 / 3) / (5 * B + 1) - 1 / 5 ∧
      (B + 1 / 3) / (5 * B + 1) - 1 / 5 ≤ 2 / (75 * B) := by
  have h1 : (B + 1 / 3) / (5 * B + 1) - 1 / 5 = (2 / 3) / (5 * (5 * B + 1)) := by
    field_simp
    ring
  rw [h1]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem keff_half_le (B : ℝ) (hB : 0 < B) :
    (B + 1 / 3) * (2 * B + 1 / 3) / (2 * (5 * B + 1)) ≤ B / 5 + 3 / 50 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem cov_eigen :
    ((3 / 5 : ℝ) * 1 + (-2 / 5) * 1 + (-1 / 5) * 1 = 0 ∧
      (-2 / 5 : ℝ) * 1 + (3 / 5) * 1 + (-1 / 5) * 1 = 0 ∧
      (-1 / 5 : ℝ) * 1 + (-1 / 5) * 1 + (2 / 5) * 1 = 0) ∧
    ((3 / 5 : ℝ) * 1 + (-2 / 5) * (-1) + (-1 / 5) * 0 = 1 ∧
      (-2 / 5 : ℝ) * 1 + (3 / 5) * (-1) + (-1 / 5) * 0 = -1 ∧
      (-1 / 5 : ℝ) * 1 + (-1 / 5) * (-1) + (2 / 5) * 0 = 0) ∧
    ((3 / 5 : ℝ) * 1 + (-2 / 5) * 1 + (-1 / 5) * (-2) = 3 / 5 * 1 ∧
      (-2 / 5 : ℝ) * 1 + (3 / 5) * 1 + (-1 / 5) * (-2) = 3 / 5 * 1 ∧
      (-1 / 5 : ℝ) * 1 + (-1 / 5) * 1 + (2 / 5) * (-2) = 3 / 5 * (-2)) := by
  norm_num

/-- First-order coefficient of `h'₂` (in `1/B`): `-(8/3125) h₂ + (42/125) h₃ - 14/140625`,
evaluated at `h₂ = (37/76)/180`, `h₃ = (1937/3890)/2835` and divided by `p₂ = 1/180`. -/
theorem first_order_at_fixed_point :
    (-(8 / 3125 : ℚ) * (37 / 76 / 180) + 42 / 125 * (1937 / 3890 / 2835) - 14 / 140625) * 180
      = -591986 / 69290625 := by
  norm_num

/-- The quadratic shape coefficient: `(1/8)·176·Σκ²vv + (1/2)·80·Σκ u t` with
`Σκ²vv = 464/15625`, `Σκ u t = 24/15625` (`v = (4,4,2)/25`, `u = g c³`, `t = κ_jj g_j c_j`). -/
theorem quadratic_shape_coefficient :
    ((3 / 5 : ℚ) ^ 2 * (4 / 25) ^ 2 * 2 + 2 * (2 / 5) ^ 2 * (4 / 25) ^ 2
        + 4 * (1 / 5) ^ 2 * (4 / 25) * (2 / 25) + (2 / 5) ^ 2 * (2 / 25) ^ 2 = 464 / 15625) ∧
    ((8 / 125 : ℚ) * (16 / 1000) * 2 + (16 / 1000) * (-32 / 1000) = 24 / 15625) ∧
    ((1 / 8 : ℚ) * 176 * (464 / 15625) + (1 / 2) * 80 * (24 / 15625) = 11168 / 15625) := by
  norm_num

end LatticeGaugeShapeRemainderUniform

#print axioms LatticeGaugeShapeRemainderUniform.uv_uniform
#print axioms LatticeGaugeShapeRemainderUniform.stays_in_box
#print axioms LatticeGaugeShapeRemainderUniform.pow_sub_pow_norm_le
#print axioms LatticeGaugeShapeRemainderUniform.saddle_ratio_le
#print axioms LatticeGaugeShapeRemainderUniform.saddle_ratio_three
#print axioms LatticeGaugeShapeRemainderUniform.keff_half_le
#print axioms LatticeGaugeShapeRemainderUniform.cov_eigen
#print axioms LatticeGaugeShapeRemainderUniform.first_order_at_fixed_point
#print axioms LatticeGaugeShapeRemainderUniform.quadratic_shape_coefficient
