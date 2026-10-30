import Mathlib

/-!
# The first-order stiffness constants of fine and coarse faces

* Two-loop plaquette constant for SU(2) (`⟨y⟩ = 3/4 + w₂/β`): with the lattice integrals
  `P₁, Q₁, Q₂`, `w₂ = 48 (1/384 + P₁/24 - P₁²/12 - Q₁/24 - Q₂/288) - 3/32`,
  i.e. `w₂ = 1/8 + (2P₁ - 4P₁² - 2Q₁ - Q₂/6) - 3/32`.
* Coarse slope: if the face angle is `ξ = Φ + γ Φ³` in terms of the Gaussian flux `Φ`, then with
  `u = β Φ²/8` one has `y = u - (1/6 - 16 γ) u²/β`, and the slope is `c₁ = 4 (1/6 - 16γ) = 2/3 - 64γ`.
* The constants `c₀ = 1/4 + 8 r w₂/3 + 5 c₁/4` and the thresholds `β_k ≥ 10 C`.
-/

namespace LevelConstants

theorem w2_split (P Q₁ Q₂ : ℝ) :
    48 * (1/384 + P/24 - P^2/12 - Q₁/24 - Q₂/288) - 3/32
      = 1/8 + (2*P - 4*P^2 - 2*Q₁ - Q₂/6) - 3/32 := by ring

theorem w2_value (P Q₁ Q₂ : ℝ) (hP1 : 0.1549333902 ≤ P) (hP2 : P ≤ 0.1549333903)
    (hQ1 : Q₁ = 0.0423063684) (hQ2 : Q₂ = 0.054623978180) :
    0.15138 ≤ 48 * (1/384 + P/24 - P^2/12 - Q₁/24 - Q₂/288) - 3/32 ∧
      48 * (1/384 + P/24 - P^2/12 - Q₁/24 - Q₂/288) - 3/32 ≤ 0.15139 := by
  subst hQ1; subst hQ2
  constructor <;> nlinarith

/-- The gap to `1/8`. -/
theorem w2_gap (P Q₁ Q₂ : ℝ) (hP1 : 0.1549333902 ≤ P) (hP2 : P ≤ 0.1549333903)
    (hQ1 : Q₁ = 0.0423063684) (hQ2 : Q₂ = 0.054623978180) :
    0.0263 ≤ (2*P - 4*P^2 - 2*Q₁ - Q₂/6) - 3/32 ∧ (2*P - 4*P^2 - 2*Q₁ - Q₂/6) - 3/32 ≤ 0.0264 := by
  subst hQ1; subst hQ2
  constructor <;> nlinarith

/-- `y = β (ξ²/8 - ξ⁴/384)` with `ξ² = Φ² + 2γΦ⁴` and `u = βΦ²/8`. -/
theorem cubic_to_y (β Φ γ : ℝ) (hβ : 0 < β) :
    β * ((Φ^2 + 2*γ*Φ^4)/8 - Φ^4/384)
      = β*Φ^2/8 - (1/6 - 16*γ) * (β*Φ^2/8)^2 / β := by
  field_simp; ring

/-- For `y = u - κ u²/β` with `u` Gamma: `w₂ = -(15/16) κ`, `v₂ = -(105/32) κ`, slope `4κ`. -/
theorem slope_of_kappa (κ : ℝ) :
    32 * (-(15/16) * κ) / 3 - 64 * (-(105/32) * κ) / 15 = 4 * κ := by ring

theorem slope_of_gamma (γ : ℝ) : 4 * (1/6 - 16*γ) = 2/3 - 64*γ := by ring

/-- Equal path holonomies give no cubic term of the averaged angle. -/
theorem equal_paths (u : ℝ) : -u^3/24 + u * u^2/8 - u^3/12 = 0 := by ring

theorem fine_constants (w₂ : ℝ) (h2 : w₂ ≤ 0.15139) :
    2/3 + 8*w₂/3 ≤ 1.0704 ∧ 2/3 + 8*w₂/3 - 1/6 ≤ 0.9038 := by constructor <;> linarith

/-- Level 1 (`r = 1.1237`, `c₁ = 1.1733`) and level 2 (`r = 1.2327`, `c₁ = 1.2084`). -/
theorem coarse_constants (w₂ : ℝ) (h2 : w₂ ≤ 0.15139) :
    1/4 + 8*(1.1237*w₂)/3 + 5*1.1733/4 ≤ 2.171 ∧
    1/4 + 8*(1.1237*w₂)/3 + 5*1.1733/4 - 1.1733/2 ≤ 1.584 ∧
    1/4 + 8*(1.2327*w₂)/3 + 5*1.2084/4 ≤ 2.259 ∧
    1/4 + 8*(1.2327*w₂)/3 + 5*1.2084/4 - 1.2084/2 ≤ 1.654 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem threshold (βk C : ℝ) (hβ : 0 < βk) (h : 10 * C ≤ βk) : 0.9 ≤ 1 - C / βk := by
  have : C / βk ≤ 1 / 10 := by rw [div_le_iff₀ hβ]; linarith
  linarith

theorem thresholds :
    (0.9 : ℝ) ≤ 1 - 2.171 / 21.71 ∧ (0.9 : ℝ) ≤ 1 - 2.259 / 22.59 ∧
    (0.9 : ℝ) ≤ 1 - 1.584 / 15.84 ∧ (0.9 : ℝ) ≤ 1 - 1.654 / 16.54 := by norm_num

end LevelConstants

#print axioms LevelConstants.w2_split
#print axioms LevelConstants.w2_value
#print axioms LevelConstants.w2_gap
#print axioms LevelConstants.cubic_to_y
#print axioms LevelConstants.slope_of_kappa
#print axioms LevelConstants.slope_of_gamma
#print axioms LevelConstants.equal_paths
#print axioms LevelConstants.fine_constants
#print axioms LevelConstants.coarse_constants
#print axioms LevelConstants.threshold
#print axioms LevelConstants.thresholds
