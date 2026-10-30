import Mathlib

/-!
# Stiffness of a coarse face angle: exact decomposition and a lower bound

For a coarse face angle `ψ` with `y = β (1 - cos ψ)`, the Schwinger–Dyson identity summed over all
fine links gives
`1 + Γ = [ (F - b)/a + (ln a)' + 2 cot ψ ] / (β sin ψ)`.
Writing `b = 2 a B cot ψ`, this splits into a force ratio `R = F/(a β sin ψ)`, a diffusion defect
`(B - 1) h` with `h = 2 cos ψ / (β sin² ψ)`, and the slope of `ln a`.  In terms of `y`,
`h = 2 (1 - y/β) / (y (2 - y/β))`, and `0 ≤ h ≤ 1/y` for `0 < y ≤ β`.

The lower bound `Γ ≥ r₀ - 1 - η / y₀ - λ` follows from `R ≥ r₀`, `B - 1 ≤ η`, a slope bound and
`y ≥ y₀`.  In the Gaussian (free) theory, `dᵀ P = dᵀ` for the projection `P` onto `im d` makes
the force ratio equal to `1 / P_pp` for every linear averaging rule `K`; in four dimensions this
is `2`.  The tree value of the diffusion coefficient for the flux rule is the exact rational
`3173/7200`.
-/

namespace CoarseStiffness

open Matrix

/-- The defect weight as a function of `y`. -/
noncomputable def hfun (y β : ℝ) : ℝ := 2 * (1 - y / β) / (y * (2 - y / β))

theorem h_from_angle (y β : ℝ) (hβ : 0 < β) (hy : 0 < y) (hyb : y < 2 * β) :
    2 * (1 - y / β) / (β * ((y / β) * (2 - y / β))) = hfun y β := by
  unfold hfun
  have h2 : 0 < 2 - y / β := by
    rw [sub_pos, div_lt_iff₀ hβ]; linarith
  field_simp

theorem h_nonneg (y β : ℝ) (hβ : 0 < β) (hy : 0 < y) (hyb : y ≤ β) : 0 ≤ hfun y β := by
  unfold hfun
  have hu : y / β ≤ 1 := by rw [div_le_one hβ]; exact hyb
  have h2 : 0 < 2 - y / β := by linarith
  apply div_nonneg
  · linarith
  · positivity

theorem h_le_inv (y β : ℝ) (hβ : 0 < β) (hy : 0 < y) (hyb : y ≤ β) : hfun y β ≤ 1 / y := by
  unfold hfun
  have hu0 : 0 ≤ y / β := by positivity
  have hu : y / β ≤ 1 := by rw [div_le_one hβ]; exact hyb
  have h2 : 0 < 2 - y / β := by linarith
  rw [div_le_div_iff₀ (by positivity) hy]
  nlinarith

/-- Exact split of the stiffness: force ratio, diffusion defect, slope of `ln a`. -/
theorem decomposition (a s c β F B l : ℝ) (ha : 0 < a) (hs : 0 < s) (hβ : 0 < β) :
    ((F - 2 * a * B * c / s) / a + l + 2 * c / s) / (β * s)
      = F / (a * β * s) - (B - 1) * (2 * c / (β * s ^ 2)) + l / (β * s) := by
  field_simp
  ring

/-- Lower bound on `Γ = R - (B - 1) h + λ' - 1`. -/
theorem gamma_lower (R B h dl r₀ η lam y y₀ : ℝ) (hR : r₀ ≤ R) (hB : B - 1 ≤ η) (hη : 0 ≤ η)
    (hh0 : 0 ≤ h) (hh : h ≤ 1 / y) (hy₀ : 0 < y₀) (hy : y₀ ≤ y) (hdl : -lam ≤ dl) :
    r₀ - 1 - η / y₀ - lam ≤ R - (B - 1) * h + dl - 1 := by
  have hyy : 1 / y ≤ 1 / y₀ := one_div_le_one_div_of_le hy₀ hy
  have h1 : (B - 1) * h ≤ η * h := mul_le_mul_of_nonneg_right hB hh0
  have h2 : η * h ≤ η * (1 / y₀) := mul_le_mul_of_nonneg_left (le_trans hh hyy) hη
  have h3 : η * (1 / y₀) = η / y₀ := by ring
  linarith

/-- The force ratio from a force floor and a ceiling of the diffusion coefficient. -/
theorem ratio_lower (φ φ₀ a amax : ℝ) (ha : 0 < a) (hamax : a ≤ amax) (hφ₀ : 0 ≤ φ₀)
    (hφ : φ₀ ≤ φ) : φ₀ / amax ≤ φ / a := by
  have hm : 0 < amax := lt_of_lt_of_le ha hamax
  calc φ₀ / amax ≤ φ₀ / a := div_le_div_of_nonneg_left hφ₀ ha hamax
    _ ≤ φ / a := div_le_div_of_nonneg_right hφ ha.le

/-- A symmetric `P` fixing the columns of `d` satisfies `dᵀ P = dᵀ`. -/
theorem transpose_fix {p n : Type*} [Fintype p] (d : Matrix p n ℝ) (P : Matrix p p ℝ)
    (hsym : Pᵀ = P) (hfix : P * d = d) : dᵀ * P = dᵀ := by
  have := congrArg Matrix.transpose hfix
  rw [Matrix.transpose_mul, hsym] at this
  exact this

/-- Free theory: the coarse force pairing equals the coarse diffusion matrix. -/
theorem free_force_pairing {m p n : Type*} [Fintype p] [Fintype n]
    (K : Matrix m p ℝ) (d : Matrix p n ℝ) (P : Matrix p p ℝ) (h : dᵀ * P = dᵀ) :
    K * d * dᵀ * P * Kᵀ = K * d * dᵀ * Kᵀ := by
  rw [Matrix.mul_assoc (K * d) dᵀ P, h]

/-- Free theory: with `F = a θ / V` and `β_k V = P_pp`, the force ratio is `1 / P_pp`. -/
theorem free_ratio (a θ V βk Ppp F : ℝ) (ha : 0 < a) (hθ : θ ≠ 0) (hV : 0 < V) (hβ : 0 < βk)
    (hF : F = a * θ / V) (hk : βk * V = Ppp) : F / (a * βk * θ) = 1 / Ppp := by
  subst hF; subst hk
  field_simp

theorem four_dim_ratio : 1 / (2 / (4 : ℝ)) - 1 = 1 := by norm_num

/-- Exact tree value of the coarse diffusion coefficient of the flux rule (coefficient list
grouped by absolute value, both signs). -/
theorem flux_tree_value :
    (2 * (2 * ((49/120 : ℝ)^2 + (23/80)^2 + (17/120)^2 + (23/240)^2 + (19/240)^2 + (13/240)^2)
      + 12 * (1/8)^2 + 24 * (1/16)^2 + 10 * (1/30)^2 + 16 * (1/40)^2 + 48 * (1/120)^2)) / 4
      = 3173 / 7200 := by norm_num

theorem flux_link_count :
    2 * (2 * 6 + 12 + 24 + 10 + 16 + 48) = 244 := by norm_num

theorem cs_four (x₁ x₂ x₃ x₄ : ℝ) :
    (x₁ + x₂ + x₃ + x₄) ^ 2 ≤ 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₁ - x₄), sq_nonneg (x₂ - x₃),
    sq_nonneg (x₂ - x₄), sq_nonneg (x₃ - x₄)]

/-- Lower bound with a direct bound `D ≤ δ` on the defect product `D = (B - 1) h`. -/
theorem gamma_lower_direct (R D dl r₀ δ lam : ℝ) (hR : r₀ ≤ R) (hD : D ≤ δ) (hdl : -lam ≤ dl) :
    r₀ - 1 - δ - lam ≤ R - D + dl - 1 := by linarith

/-- Ledger instances (the inputs are the measured band extremes; only the arithmetic is checked):
level 1 of `16⁴ → 8⁴` and level 2 of `8⁴ → 4⁴` at `β = 28`, level 1 of `8⁴ → 4⁴` at `β = 54`. -/
theorem gamma_min_level1_b28 : (1.985 : ℝ) - 1 - 0.0221 - 0.0446 = 0.9183 := by norm_num
theorem gamma_min_level2_b28 : (1.9824 : ℝ) - 1 - 0.0261 - 0.0432 = 0.9131 := by norm_num
theorem gamma_min_level1_b54 : (2.0015 : ℝ) - 1 - 0.0199 - 0.0469 = 0.9347 := by norm_num

/-- With `Γ_min ≥ 0.913` the tail rate `1 + Γ_min` stays within `4.4%` of the Gamma rate `2`. -/
theorem rate_gap : (2 : ℝ) - (1 + 0.9131) ≤ 0.044 * 2 := by norm_num

end CoarseStiffness

#print axioms CoarseStiffness.h_from_angle
#print axioms CoarseStiffness.h_nonneg
#print axioms CoarseStiffness.h_le_inv
#print axioms CoarseStiffness.decomposition
#print axioms CoarseStiffness.gamma_lower
#print axioms CoarseStiffness.ratio_lower
#print axioms CoarseStiffness.transpose_fix
#print axioms CoarseStiffness.free_force_pairing
#print axioms CoarseStiffness.free_ratio
#print axioms CoarseStiffness.four_dim_ratio
#print axioms CoarseStiffness.flux_tree_value
#print axioms CoarseStiffness.flux_link_count
#print axioms CoarseStiffness.cs_four
#print axioms CoarseStiffness.gamma_lower_direct
#print axioms CoarseStiffness.gamma_min_level1_b28
#print axioms CoarseStiffness.gamma_min_level2_b28
#print axioms CoarseStiffness.gamma_min_level1_b54
#print axioms CoarseStiffness.rate_gap
