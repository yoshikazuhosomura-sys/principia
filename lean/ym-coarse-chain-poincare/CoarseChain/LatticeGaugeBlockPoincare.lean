/-
  Block Poincaré constant of the one-dimensional double-well path measure:
  the algebraic and one-dimensional steps of the separator argument.

  Setting (paper): block of length L ≤ 15, separator site j with both sides of length ≤ 7,
  where the z-Hessian is ≥ κ₀ = 15/4 - 4 cos(π/8) > 0.

  * `kappa_seven_gt`         : 1/20 < 15/4 - 4 cos(π/8)                     (no hypotheses)
  * `free_energy_quasiconvex`: a convex function of σ = s² is quasi-convex in s on s ≤ 0
  * `quasiconvex_add_osc`    : quasi-convex + perturbation of oscillation ≤ D has barrier ≤ D
  * `ratio_exp_bound`        : the pointwise kernel bound p(x)p(y)/p(s) ≤ e^{Δ/ħ}(p(x)+p(y))
  * `cross_term_sq`          : Cauchy–Schwarz step for the covariance term
  * `deriv_sq_split`         : (u+v)² ≤ 2u² + 2v²
  * `two_scale_assembly`     : the variance decomposition algebra of Lemma 2
  * `telescope`, `path_cs`   : g x - g y as a sum of increments, and its Cauchy–Schwarz bound
  * `hardy_discrete`         : discrete one-dimensional Hardy-type inequality
                               Σ_{y<x} p_x p_y (g_x - g_y)² ≤ Σ_e c_e (Δ_e g)² K_e
-/
import Mathlib

namespace LatticeGauge.BlockPoincare

open Real Finset

/-- The worst-case convexity of a block of length 7 is positive: 15/4 - 4 cos(π/8) > 1/20. -/
theorem kappa_seven_gt : (1:ℝ)/20 < 15/4 - 4 * Real.cos (π/8) := by
  rw [Real.cos_pi_div_eight]
  have h2 : Real.sqrt 2 < 1.4225 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 : 0 ≤ 2 + Real.sqrt 2 := by positivity
  have h3 : Real.sqrt (2 + Real.sqrt 2) < 1.85 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  nlinarith

/-- If `F` is convex on `[0, C]` (as a function of σ = s²), then `s ↦ F (s^2)` is quasi-convex
on the nonpositive half-line: for `y ≤ s ≤ x ≤ 0` with `y^2 ≤ C`, `F (s^2) ≤ max (F (x^2)) (F (y^2))`. -/
theorem free_energy_quasiconvex (F : ℝ → ℝ) (C : ℝ) (hF : ConvexOn ℝ (Set.Icc 0 C) F)
    {x y s : ℝ} (hys : y ≤ s) (hsx : s ≤ x) (hx : x ≤ 0) (hyC : y ^ 2 ≤ C) :
    F (s ^ 2) ≤ max (F (x ^ 2)) (F (y ^ 2)) := by
  have hxs : x ^ 2 ≤ s ^ 2 := by nlinarith
  have hsy : s ^ 2 ≤ y ^ 2 := by nlinarith
  have hxmem : x ^ 2 ∈ Set.Icc (0:ℝ) C := ⟨by positivity, le_trans hxs (le_trans hsy hyC)⟩
  have hymem : y ^ 2 ∈ Set.Icc (0:ℝ) C := ⟨by positivity, hyC⟩
  have hseg : s ^ 2 ∈ segment ℝ (x ^ 2) (y ^ 2) := by
    rw [segment_eq_uIcc]
    exact Set.mem_uIcc.mpr (Or.inl ⟨hxs, hsy⟩)
  exact hF.le_on_segment hxmem hymem hseg

/-- A quasi-convex function plus a perturbation whose oscillation is at most `D`
has barrier at most `D`. -/
theorem quasiconvex_add_osc (F0 R : ℝ → ℝ) (D : ℝ) {x y s : ℝ}
    (hq : F0 s ≤ max (F0 x) (F0 y)) (hR : ∀ u v, R u - R v ≤ D) :
    F0 s + R s ≤ max (F0 x + R x) (F0 y + R y) + D := by
  have h1 := hR s x
  have h2 := hR s y
  rcases le_total (F0 x) (F0 y) with h | h
  · rw [max_eq_right h] at hq
    have : F0 y + R y ≤ max (F0 x + R x) (F0 y + R y) := le_max_right _ _
    linarith
  · rw [max_eq_left h] at hq
    have : F0 x + R x ≤ max (F0 x + R x) (F0 y + R y) := le_max_left _ _
    linarith

/-- Pointwise kernel bound of the one-dimensional Hardy-type lemma:
if `Fs ≤ max Fx Fy + Δ` then `exp(-(Fx+Fy-Fs)/ħ) ≤ exp(Δ/ħ) (exp(-Fx/ħ) + exp(-Fy/ħ))`. -/
theorem ratio_exp_bound {ħ Fx Fy Fs Δ : ℝ} (hħ : 0 < ħ) (hΔ : Fs ≤ max Fx Fy + Δ) :
    Real.exp (-(Fx + Fy - Fs) / ħ) ≤
      Real.exp (Δ / ħ) * (Real.exp (-Fx / ħ) + Real.exp (-Fy / ħ)) := by
  have hpos1 := Real.exp_pos (-Fx / ħ)
  have hpos2 := Real.exp_pos (-Fy / ħ)
  have hE := Real.exp_pos (Δ / ħ)
  rcases le_total Fx Fy with h | h
  · rw [max_eq_right h] at hΔ
    have hle : -(Fx + Fy - Fs) / ħ ≤ Δ / ħ + -Fx / ħ := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hħ.le
    calc Real.exp (-(Fx + Fy - Fs) / ħ) ≤ Real.exp (Δ / ħ + -Fx / ħ) := Real.exp_le_exp.mpr hle
      _ = Real.exp (Δ / ħ) * Real.exp (-Fx / ħ) := Real.exp_add _ _
      _ ≤ Real.exp (Δ / ħ) * (Real.exp (-Fx / ħ) + Real.exp (-Fy / ħ)) := by nlinarith
  · rw [max_eq_left h] at hΔ
    have hle : -(Fx + Fy - Fs) / ħ ≤ Δ / ħ + -Fy / ħ := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hħ.le
    calc Real.exp (-(Fx + Fy - Fs) / ħ) ≤ Real.exp (Δ / ħ + -Fy / ħ) := Real.exp_le_exp.mpr hle
      _ = Real.exp (Δ / ħ) * Real.exp (-Fy / ħ) := Real.exp_add _ _
      _ ≤ Real.exp (Δ / ħ) * (Real.exp (-Fx / ħ) + Real.exp (-Fy / ħ)) := by nlinarith

/-- Cauchy–Schwarz step for the covariance term: `c² ≤ Vf·Vh`, `Vf ≤ hk·A`, `Vh ≤ 2 hk`
(hk = ħ/κ ≥ 0) give `c² ≤ 2 hk² A`. -/
theorem cross_term_sq {c Vf Vh hk A : ℝ} (hc : c ^ 2 ≤ Vf * Vh) (hVh0 : 0 ≤ Vh)
    (hhk : 0 ≤ hk) (hA : 0 ≤ A) (hVf : Vf ≤ hk * A) (hVh : Vh ≤ 2 * hk) :
    c ^ 2 ≤ 2 * hk ^ 2 * A := by
  have h1 : Vf * Vh ≤ (hk * A) * (2 * hk) :=
    mul_le_mul hVf hVh hVh0 (mul_nonneg hhk hA)
  nlinarith

/-- `(u+v)² ≤ 2u² + 2v²`. -/
theorem deriv_sq_split (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- Variance decomposition algebra (Lemma 2): `V = E1 + V2`, `E1 ≤ hk·A`, `V2 ≤ Cm·G2`,
`G2 ≤ 2B + c·A`, `2 ≤ c`, `A, B, hk, Cm ≥ 0` give `V ≤ (hk + Cm·c)(A + B)`. -/
theorem two_scale_assembly {V E1 V2 G2 A B hk Cm c : ℝ} (hV : V = E1 + V2) (hE1 : E1 ≤ hk * A)
    (hV2 : V2 ≤ Cm * G2) (hG2 : G2 ≤ 2 * B + c * A) (hB : 0 ≤ B)
    (hhk : 0 ≤ hk) (hCm : 0 ≤ Cm) (hc : 2 ≤ c) :
    V ≤ (hk + Cm * c) * (A + B) := by
  have h1 : Cm * G2 ≤ Cm * (2 * B + c * A) := mul_le_mul_of_nonneg_left hG2 hCm
  have h2 : Cm * (2 * B) ≤ Cm * (c * B) := mul_le_mul_of_nonneg_left (by nlinarith) hCm
  have h3 : 0 ≤ hk * B := mul_nonneg hhk hB
  nlinarith

/-- Telescoping: `g x - g y = Σ_{e ∈ [y, x)} (g (e+1) - g e)` for `y ≤ x`. -/
theorem telescope (g : ℕ → ℝ) {y x : ℕ} (hyx : y ≤ x) :
    g x - g y = ∑ e ∈ Ico y x, (g (e + 1) - g e) := by
  induction x, hyx using Nat.le_induction with
  | base => simp
  | succ x hyx ih =>
    rw [Finset.sum_Ico_succ_top hyx, ← ih]; ring

/-- Cauchy–Schwarz along the path from `y` to `x` with positive conductances `c`. -/
theorem path_cs (c g : ℕ → ℝ) (hc : ∀ k, 0 < c k) {y x : ℕ} (hyx : y ≤ x) :
    (g x - g y) ^ 2 ≤ (∑ e ∈ Ico y x, c e * (g (e + 1) - g e) ^ 2) * ∑ e ∈ Ico y x, 1 / c e := by
  rw [telescope g hyx]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact mul_nonneg (hc i).le (sq_nonneg _)
  · intro i _; exact div_nonneg zero_le_one (hc i).le
  · intro i _
    have h := hc i
    rw [show c i * (g (i + 1) - g i) ^ 2 * (1 / c i) = (g (i + 1) - g i) ^ 2 by field_simp]

theorem ico_as_filter (N y x : ℕ) (hx : x ≤ N) :
    (range N).filter (fun e => y ≤ e ∧ e < x) = Ico y x := by
  ext e; simp only [mem_filter, mem_range, mem_Ico]; omega

/-- Discrete one-dimensional Hardy-type inequality (the discrete form of Lemma 3):
with nonnegative masses `p` on the nodes `0, …, N` and positive conductances `c` on the edges,
`Σ_{y<x} p_x p_y (g_x - g_y)² ≤ Σ_e c_e (g_{e+1} - g_e)² · K_e`,
`K_e = Σ_{y ≤ e < x} p_x p_y Σ_{e' ∈ [y,x)} 1/c_{e'}`. -/
theorem hardy_discrete (N : ℕ) (p c g : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hc : ∀ k, 0 < c k) :
    ∑ x ∈ range (N + 1), ∑ y ∈ range x, p x * p y * (g x - g y) ^ 2 ≤
      ∑ e ∈ range N, c e * (g (e + 1) - g e) ^ 2 *
        (∑ x ∈ range (N + 1), ∑ y ∈ range x,
          if (y ≤ e ∧ e < x) then p x * p y * ∑ e' ∈ Ico y x, 1 / c e' else 0) := by
  have key : ∀ x ∈ range (N + 1), ∀ y ∈ range x,
      p x * p y * (g x - g y) ^ 2 ≤
        ∑ e ∈ range N, (if (y ≤ e ∧ e < x) then
          c e * (g (e + 1) - g e) ^ 2 * (p x * p y * ∑ e' ∈ Ico y x, 1 / c e') else 0) := by
    intro x hx y hy
    have hxN : x ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hx)
    have hyx : y ≤ x := (mem_range.mp hy).le
    rw [← Finset.sum_filter, ico_as_filter N y x hxN, ← Finset.sum_mul]
    have hpp : 0 ≤ p x * p y := mul_nonneg (hp x) (hp y)
    calc p x * p y * (g x - g y) ^ 2
        ≤ p x * p y * ((∑ e ∈ Ico y x, c e * (g (e + 1) - g e) ^ 2) * ∑ e ∈ Ico y x, 1 / c e) :=
          mul_le_mul_of_nonneg_left (path_cs c g hc hyx) hpp
      _ = (∑ e ∈ Ico y x, c e * (g (e + 1) - g e) ^ 2) * (p x * p y * ∑ e' ∈ Ico y x, 1 / c e') := by
          ring
  calc ∑ x ∈ range (N + 1), ∑ y ∈ range x, p x * p y * (g x - g y) ^ 2
      ≤ ∑ x ∈ range (N + 1), ∑ y ∈ range x, ∑ e ∈ range N, (if (y ≤ e ∧ e < x) then
          c e * (g (e + 1) - g e) ^ 2 * (p x * p y * ∑ e' ∈ Ico y x, 1 / c e') else 0) := by
        apply Finset.sum_le_sum; intro x hx
        apply Finset.sum_le_sum; intro y hy
        exact key x hx y hy
    _ = ∑ e ∈ range N, ∑ x ∈ range (N + 1), ∑ y ∈ range x, (if (y ≤ e ∧ e < x) then
          c e * (g (e + 1) - g e) ^ 2 * (p x * p y * ∑ e' ∈ Ico y x, 1 / c e') else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl; intro e _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
        split_ifs <;> ring

end LatticeGauge.BlockPoincare

#print axioms LatticeGauge.BlockPoincare.kappa_seven_gt
#print axioms LatticeGauge.BlockPoincare.free_energy_quasiconvex
#print axioms LatticeGauge.BlockPoincare.quasiconvex_add_osc
#print axioms LatticeGauge.BlockPoincare.ratio_exp_bound
#print axioms LatticeGauge.BlockPoincare.cross_term_sq
#print axioms LatticeGauge.BlockPoincare.deriv_sq_split
#print axioms LatticeGauge.BlockPoincare.two_scale_assembly
#print axioms LatticeGauge.BlockPoincare.telescope
#print axioms LatticeGauge.BlockPoincare.path_cs
#print axioms LatticeGauge.BlockPoincare.ico_as_filter
#print axioms LatticeGauge.BlockPoincare.hardy_discrete
