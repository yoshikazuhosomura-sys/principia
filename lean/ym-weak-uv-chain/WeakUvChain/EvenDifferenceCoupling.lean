/-
Extracting the large-field coupling difference r^ℓ = (F_θ − F_0)/(c(θ)·V), c(θ) = 12(1 − cos θ):
  §1 The coefficient 2/c in the triangle-inequality bound |r^ℓ| ≤ (2/c)ζ blows up as θ → 0, at least 1/(3θ²) (≥ 33 at θ = 1/10).
  §2 If F is even in θ and the coefficients of its power series in θ² satisfy a Cauchy-type bound |a_n| ≤ M (1/R²)^{n+1}
     (M = 2Vζ, R the radius of analyticity), then |F_θ − F_0| ≤ M q/(1−q) (q = θ²/R²).
  §3 Hence for 0 < θ ≤ 1/10, R ≥ 7/10: |r^ℓ| ≤ (7/10)ζ, uniformly in θ (finite as θ → 0).
  §4 Rescaling the norm on the β coordinates: ‖φ‖·a·c₀² and the window condition c₀/u ≤ κ²/(8a) are invariant under scaling the norm by s.
Single file; checks with `import Mathlib` only.
-/
import Mathlib

namespace EvenDifferenceCoupling

open Real

/-! ## 1. Bounds on c(θ) = 12(1 − cos θ) -/

theorem c_upper (θ : ℝ) : 12 * (1 - Real.cos θ) ≤ 6 * θ ^ 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

theorem c_lower (θ : ℝ) (h : |θ| ≤ 1) : 6 * θ ^ 2 - 5 / 8 * θ ^ 4 ≤ 12 * (1 - Real.cos θ) := by
  have hb := Real.cos_bound h
  have h4 : |θ| ^ 4 = θ ^ 4 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [h4] at hb
  have := (abs_le.mp hb).2
  linarith

/-- The triangle-inequality coefficient blows up as θ → 0: `1/(3θ²) ≤ 2/c(θ)` (0 < θ ≤ 1). -/
theorem triangle_coefficient_blows_up (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) :
    1 / (3 * θ ^ 2) ≤ 2 / (12 * (1 - Real.cos θ)) := by
  have hl := c_lower θ (by rw [abs_of_pos h0]; exact h1)
  have hu := c_upper θ
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have hcpos : 0 < 12 * (1 - Real.cos θ) := by nlinarith [sq_nonneg θ, pow_pos h0 2]
  rw [div_le_div_iff₀ (by positivity) hcpos]
  linarith

/-- At θ = 1/10 the triangle-inequality coefficient exceeds 33. -/
theorem triangle_coefficient_at_tenth : (33 : ℝ) ≤ 2 / (12 * (1 - Real.cos (1 / 10))) := by
  have h := triangle_coefficient_blows_up (1 / 10) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-! ## 2. Differences of even series -/

theorem even_series_bound (a : ℕ → ℝ) (M R θ : ℝ) (hR : 0 < R) (hθ : θ ^ 2 < R ^ 2) (_hM : 0 ≤ M)
    (ha : ∀ n, |a n| ≤ M * (1 / R ^ 2) ^ (n + 1)) :
    |∑' n, a n * (θ ^ 2) ^ (n + 1)| ≤ M * (θ ^ 2 / R ^ 2) / (1 - θ ^ 2 / R ^ 2) := by
  set q := θ ^ 2 / R ^ 2 with hq
  have hR2 : 0 < R ^ 2 := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hR2]; exact hθ
  have hs : HasSum (fun n : ℕ => M * q * q ^ n) (M * q * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q)
  have hb : ∀ n, ‖a n * (θ ^ 2) ^ (n + 1)‖ ≤ M * q * q ^ n := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (θ ^ 2) ^ (n + 1))]
    have e : M * q * q ^ n = M * (1 / R ^ 2) ^ (n + 1) * (θ ^ 2) ^ (n + 1) := by
      rw [mul_assoc, ← pow_succ', mul_assoc, ← mul_pow, hq]
      congr 2; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (ha n) (by positivity)
  have := tsum_of_norm_bounded hs hb
  rw [Real.norm_eq_abs] at this
  rw [div_eq_mul_inv]
  exact this

/-! ## 3. Coupling difference uniform in θ -/

theorem coupling_uniform (a : ℕ → ℝ) (Fθ F0 V ζ R θ : ℝ) (hV : 0 < V) (hζ : 0 ≤ ζ)
    (hR : 7 / 10 ≤ R) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 10)
    (hser : Fθ - F0 = ∑' n, a n * (θ ^ 2) ^ (n + 1))
    (ha : ∀ n, |a n| ≤ 2 * V * ζ * (1 / R ^ 2) ^ (n + 1)) :
    |(Fθ - F0) / (12 * (1 - Real.cos θ) * V)| ≤ 7 / 10 * ζ := by
  have hR0 : 0 < R := by linarith
  have hθ2 : θ ^ 2 ≤ 1 / 100 := by nlinarith
  have hR2 : 49 / 100 ≤ R ^ 2 := by nlinarith
  have hθR : θ ^ 2 < R ^ 2 := by linarith
  have hb := even_series_bound a (2 * V * ζ) R θ hR0 hθR (by positivity) ha
  rw [← hser] at hb
  have hc := c_lower θ (by rw [abs_of_pos hθ0]; linarith)
  have ht2 : 0 < θ ^ 2 := by positivity
  have hc' : θ ^ 2 * (599 / 100) ≤ 12 * (1 - Real.cos θ) := by
    have : θ ^ 4 = θ ^ 2 * θ ^ 2 := by ring
    nlinarith
  have hcpos : 0 < 12 * (1 - Real.cos θ) := by nlinarith
  have e : 2 * V * ζ * (θ ^ 2 / R ^ 2) / (1 - θ ^ 2 / R ^ 2) = 2 * V * ζ * θ ^ 2 / (R ^ 2 - θ ^ 2) := by
    have : R ^ 2 - θ ^ 2 ≠ 0 := by linarith
    have : R ^ 2 ≠ 0 := by positivity
    field_simp
  rw [e] at hb
  have hden : 48 / 100 ≤ R ^ 2 - θ ^ 2 := by linarith
  have hb2 : 2 * V * ζ * θ ^ 2 / (R ^ 2 - θ ^ 2) ≤ 2 * V * ζ * θ ^ 2 / (48 / 100) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
  rw [abs_div, abs_of_pos (mul_pos hcpos hV), div_le_iff₀ (mul_pos hcpos hV)]
  have hVζ : 0 ≤ V * ζ := by positivity
  have : 2 * V * ζ * θ ^ 2 / (48 / 100) ≤ 7 / 10 * ζ * (θ ^ 2 * (599 / 100) * V) := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have h3 : 7 / 10 * ζ * (θ ^ 2 * (599 / 100) * V) ≤ 7 / 10 * ζ * (12 * (1 - Real.cos θ) * V) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hc' hV.le
  linarith

/-! ## 4. Rescaling the norm on the β coordinates -/

/-- Scaling the norm by `s`: `‖φ‖ → ‖φ‖/s`, `a → a/s`, `c₀ → s c₀`. `‖φ‖ a c₀²` is unchanged. -/
theorem kernel_constant_scale (φn a c₀ s : ℝ) (hs : 0 < s) :
    (φn / s) * (a / s) * (s * c₀) ^ 2 = φn * a * c₀ ^ 2 := by
  field_simp

/-- The window condition `c₀/u ≤ κ²/(8a)` is also unchanged under the same rescaling. -/
theorem window_scale (c₀ a u κ s : ℝ) (hs : 0 < s) (ha : 0 < a) (_hu : 0 < u) :
    (s * c₀) / u ≤ κ ^ 2 / (8 * (a / s)) ↔ c₀ / u ≤ κ ^ 2 / (8 * a) := by
  have e1 : (s * c₀) / u = s * (c₀ / u) := by ring
  have e2 : κ ^ 2 / (8 * (a / s)) = s * (κ ^ 2 / (8 * a)) := by field_simp
  rw [e1, e2]
  exact mul_le_mul_iff_of_pos_left hs

end EvenDifferenceCoupling

#print axioms EvenDifferenceCoupling.c_upper
#print axioms EvenDifferenceCoupling.c_lower
#print axioms EvenDifferenceCoupling.triangle_coefficient_blows_up
#print axioms EvenDifferenceCoupling.triangle_coefficient_at_tenth
#print axioms EvenDifferenceCoupling.even_series_bound
#print axioms EvenDifferenceCoupling.coupling_uniform
#print axioms EvenDifferenceCoupling.kernel_constant_scale
#print axioms EvenDifferenceCoupling.window_scale
