import Mathlib

/-!
# First-order stiffness of a face from the first two moments of `y`

At first order in `1/β` the density of `y` is
`Gamma(3/2, 1/2) · (1 + ((c₀ - 1/4) y - c₁ y² / 2)/β)` up to normalisation (the `-1/4` is the
Haar factor `√(2 - y/β)`), i.e. `Γ(y) = 1 - (c₀ - c₁ y)/β`.  With the Gamma moments
`E y = 3/4`, `E y² = 15/16`, `E y³ = 105/64`, `E y⁴ = 945/256`, the first-order shifts
`⟨y⟩ = 3/4 + w₂/β`, `⟨y²⟩ = 15/16 + v₂/β` are linear in `(c₀, c₁)`; inverting gives
`c₁ = 32 w₂/3 - 64 v₂/15` and `c₀ = 1/4 + 8 w₂/3 + 5 c₁/4`.  A pure rescaling of the variance
(`δv₂ = 5 δw₂ / 2`) leaves `c₁` unchanged, the expansion of the cosine alone gives `c₁ = 2/3`,
and the excess kurtosis is `β K = -(5/12) c₁`.
-/

namespace FaceMoment

theorem gamma_moments :
    (3/2 : ℝ) * (1/2) = 3/4 ∧ (3/2 : ℝ) * (5/2) * (1/2)^2 = 15/16 ∧
    (3/2 : ℝ) * (5/2) * (7/2) * (1/2)^3 = 105/64 ∧
    (3/2 : ℝ) * (5/2) * (7/2) * (9/2) * (1/2)^4 = 945/256 := by norm_num

theorem gamma_covariances :
    (3/8 : ℝ) = 15/16 - (3/4)^2 ∧ (15/16 : ℝ) = 105/64 - (3/4) * (15/16) ∧
    (45/16 : ℝ) = 945/256 - (15/16)^2 := by norm_num

/-- The forward map `(c₀, c₁) ↦ (w₂, v₂)` (covariances with `(c₀ - 1/4) y - c₁ y²/2`). -/
theorem forward (c₀ c₁ : ℝ) :
    (c₀ - 1/4) * (3/8) - c₁ / 2 * (15/16) = (3/8) * (c₀ - 1/4) - (15/32) * c₁ ∧
    (c₀ - 1/4) * (15/16) - c₁ / 2 * (45/16) = (15/16) * (c₀ - 1/4) - (45/32) * c₁ := by
  constructor <;> ring

theorem inverse (c₀ c₁ w₂ v₂ : ℝ) (hw : w₂ = (3/8) * (c₀ - 1/4) - (15/32) * c₁)
    (hv : v₂ = (15/16) * (c₀ - 1/4) - (45/32) * c₁) :
    c₁ = 32 * w₂ / 3 - 64 * v₂ / 15 ∧ c₀ = 1/4 + 8 * w₂ / 3 + 5 * c₁ / 4 := by
  constructor
  · rw [hw, hv]; ring
  · rw [hw]; ring

/-- Excess kurtosis at first order: `β K = (16/9)(v₂ - 5 w₂/2) = -(5/12) c₁`. -/
theorem kurtosis (w₂ v₂ c₁ : ℝ) (h : c₁ = 32 * w₂ / 3 - 64 * v₂ / 15) :
    (16/9 : ℝ) * (v₂ - 5 * w₂ / 2) = -(5/12) * c₁ := by rw [h]; ring

/-- A pure variance rescaling does not move the slope. -/
theorem rescaling_keeps_slope (dw : ℝ) : 32 * dw / 3 - 64 * (5 * dw / 2) / 15 = 0 := by ring

/-- Expanding the cosine alone (`y = u - u²/(6β)` with `u` exactly Gamma): `c₁ = 2/3`. -/
theorem cosine_only :
    32 * (-(15/16) / 6 : ℝ) / 3 - 64 * (-(105/64) / 3) / 15 = 2/3 := by norm_num

/-- With the slope `1/3`: `c₀ = 2/3 + 8 w₂/3`, so `c₀ = 1` exactly when `w₂ = 1/8`. -/
theorem fine_intercept (w₂ : ℝ) : 1/4 + 8 * w₂ / 3 + 5 * (1/3 : ℝ) / 4 = 2/3 + 8 * w₂ / 3 := by ring

theorem fine_intercept_one (w₂ : ℝ) : 2/3 + 8 * w₂ / 3 = 1 ↔ w₂ = 1/8 := by
  constructor <;> intro h <;> linarith

/-- Coarse level: `w₂ᵏ = r w₂` (the coarse coupling is defined by matching `⟨y⟩`). With
`w₂ = 0.155`, `r = 1.1`, `c₁ᵏ = 1.15`: `c₀ᵏ ≤ 2.15`, and `c₀ᵏ - c₁ᵏ/2 ≤ 1.57`. -/
theorem coarse_values :
    1/4 + 8 * (1.1 * 0.155 : ℝ) / 3 + 5 * 1.15 / 4 ≤ 2.15 ∧
    1/4 + 8 * (1.1 * 0.155 : ℝ) / 3 + 5 * 1.15 / 4 - 1.15 / 2 ≤ 1.57 := by norm_num

theorem threshold (βk C : ℝ) (hβ : 0 < βk) (h : 10 * C ≤ βk) : 0.9 ≤ 1 - C / βk := by
  have : C / βk ≤ 1 / 10 := by rw [div_le_iff₀ hβ]; linarith
  linarith

/-- `Γ_k ≥ 1 - (c₀ - c₁ y)/β_k ≥ 1 - (c₀ - c₁ y₀)/β_k` for `y ≥ y₀` when `c₁ ≥ 0`. -/
theorem band_lower (c₀ c₁ y y₀ βk : ℝ) (hβ : 0 < βk) (hc : 0 ≤ c₁) (hy : y₀ ≤ y) :
    1 - (c₀ - c₁ * y₀) / βk ≤ 1 - (c₀ - c₁ * y) / βk := by
  have : c₀ - c₁ * y ≤ c₀ - c₁ * y₀ := by nlinarith
  have := div_le_div_of_nonneg_right this hβ.le
  linarith

end FaceMoment

#print axioms FaceMoment.gamma_moments
#print axioms FaceMoment.gamma_covariances
#print axioms FaceMoment.forward
#print axioms FaceMoment.inverse
#print axioms FaceMoment.kurtosis
#print axioms FaceMoment.rescaling_keeps_slope
#print axioms FaceMoment.cosine_only
#print axioms FaceMoment.fine_intercept
#print axioms FaceMoment.fine_intercept_one
#print axioms FaceMoment.coarse_values
#print axioms FaceMoment.threshold
#print axioms FaceMoment.band_lower
