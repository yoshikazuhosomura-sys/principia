import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Real.Basic

/-!
# Refitting a one-step kernel to the fundamental + adjoint family (algebraic layer)

The family `F = β cos ψ + ρ β cos² ψ` has Taylor coefficients `F = const - B ψ²/2 + q ψ⁴ + …`
with `B = β(1+2ρ)`, `q = β(1/24 + ρ/3)`. Given measured coefficients `(B', q')` of the next
outer kernel, the two conditions are linear in `(β, βρ)`.

* `refit_solution` : `β = 4B/3 - 8q ≠ 0`, `ρ = (B - β)/(2β)` solve both conditions.
* `refit_unique` : any solution has `β = 4B/3 - 8q`.
* `rho_of_ratio` : for `β ≠ 0`, `1/3 - 2x ≠ 0`:
  `β(1/24 + ρ/3) = x · β(1+2ρ) ↔ ρ = (x - 1/24)/(1/3 - 2x)`.
* `tree_quadratic_split` : `B u²/8 + B (w-u)²/2 = B w²/10 + (5B/8)(u - 4w/5)²`
  (flat tree saddle `u = 4w/5` of the outer convolution, inner kernel `2F(u/2)`).
* `tree_value_at_saddle` : with `F x = -B x²/2 + q x⁴`, `F(2w/5) + F(w/5) = -(B/10) w² + (17q/625) w⁴`.
* `image_rho`, `image_gap` : `x = (17/125)(-1/12)` gives `ρ = -53/356`, and
  `-53/356 - (-1/4) = 9/89`.
* `image_one_loop_D` : `2/5 + (24/5)(17/125)(-1/12) = 216/625`.

Only the algebra is formalised: the convolution, the saddle-point (tree) reduction, the
envelope argument for the quartic term and the one-loop formula for `D` are not.
-/

namespace LatticeGaugeFundAdjointRefit

theorem refit_solution (B q β ρ : ℝ) (hβdef : β = 4 * B / 3 - 8 * q) (hβ : β ≠ 0)
    (hρ : ρ = (B - β) / (2 * β)) :
    β * (1 + 2 * ρ) = B ∧ β * (1 / 24 + ρ / 3) = q := by
  have e : β * ρ = (B - β) / 2 := by
    rw [hρ]; field_simp
  constructor
  · linear_combination 2 * e
  · linear_combination (1 / 3) * e - (1 / 8) * hβdef

theorem refit_unique (β ρ B q : ℝ) (h1 : β * (1 + 2 * ρ) = B) (h2 : β * (1 / 24 + ρ / 3) = q) :
    β = 4 * B / 3 - 8 * q := by
  subst h1; subst h2; ring

theorem rho_of_ratio (β ρ x : ℝ) (hβ : β ≠ 0) (hx : 1 / 3 - 2 * x ≠ 0) :
    β * (1 / 24 + ρ / 3) = x * (β * (1 + 2 * ρ)) ↔ ρ = (x - 1 / 24) / (1 / 3 - 2 * x) := by
  rw [eq_div_iff hx]
  constructor
  · intro h
    have h' : β * (ρ * (1 / 3 - 2 * x) - (x - 1 / 24)) = 0 := by linear_combination h
    have := (mul_eq_zero.mp h').resolve_left hβ
    linear_combination this
  · intro hr
    linear_combination β * hr

theorem tree_quadratic_split (B u w : ℝ) :
    B * u ^ 2 / 8 + B * (w - u) ^ 2 / 2 = B * w ^ 2 / 10 + (5 * B / 8) * (u - 4 * w / 5) ^ 2 := by
  ring

theorem tree_value_at_saddle (B q w : ℝ) :
    let F : ℝ → ℝ := fun x => -B * x ^ 2 / 2 + q * x ^ 4
    F (2 * w / 5) + F (w / 5) = -(B / 10) * w ^ 2 + (17 * q / 625) * w ^ 4 := by
  intro F
  simp only [F]
  ring

theorem image_rho :
    ((17 / 125 : ℝ) * (-1 / 12) - 1 / 24) / (1 / 3 - 2 * ((17 / 125 : ℝ) * (-1 / 12))) = -53 / 356 := by
  norm_num

theorem image_gap : (-53 / 356 : ℝ) - (-1 / 4) = 9 / 89 := by norm_num

theorem image_one_loop_D : (2 / 5 : ℝ) + (24 / 5) * ((17 / 125) * (-1 / 12)) = 216 / 625 := by
  norm_num

end LatticeGaugeFundAdjointRefit

#print axioms LatticeGaugeFundAdjointRefit.refit_solution
#print axioms LatticeGaugeFundAdjointRefit.refit_unique
#print axioms LatticeGaugeFundAdjointRefit.rho_of_ratio
#print axioms LatticeGaugeFundAdjointRefit.tree_quadratic_split
#print axioms LatticeGaugeFundAdjointRefit.tree_value_at_saddle
#print axioms LatticeGaugeFundAdjointRefit.image_rho
#print axioms LatticeGaugeFundAdjointRefit.image_gap
#print axioms LatticeGaugeFundAdjointRefit.image_one_loop_D
