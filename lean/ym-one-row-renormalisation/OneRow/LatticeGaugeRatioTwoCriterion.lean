import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# The ratio-two criterion for the second-order loop couplings (algebraic layer)

Four plaquettes in a row with the loops `W_a`, `W_b` fixed; outer kernel `e^F`, inner kernel
`G = f * f`, base measure `sin²ψ · G · e^{2F}`. Write `E2 = E[F'²]`, `E1 = E[F'(log G)']`,
`Eh = E[F'']`, `Ec = E[F' cot ψ]`. The moment form of the couplings is
`κ_ab = S/2`, `κ_a = -Dsd/2 - S` with `S = E2/12`, `Dsd = Eh/12 + Ec/6`, and integration by parts
(boundary terms zero) gives `Eh + 2 Ec = -E1 - 2 E2`.

* `kappa_a_of_ibp`, `kappa_ab_eq` : `κ_a = E1/24`, `κ_ab = E2/24` under that relation.
* `ratio_two_iff` : `κ_ab = 2 κ_a ↔ E2 - 2 E1 = 0`; `ratio_eq_two_add` : `E2/E1 = 2 + (E2 - 2E1)/E1`.
* `one_loop_D` : with the Gaussian moments `m2 = 6/(5B)`, `m4 = 12/(5B²)`, `t = 1/B`,
  `B (m2/3 - 3 q m4 + 10 q t m2) = 2/5 + 24 q/(5B)` (the one-loop value of `D = E2 - 2E1`).
* `one_loop_D_u1` : the abelian analogue `-B (3 q m4 - 6 q t m2) = 24 q/(25 B)`,
  `m2 = 2/(5B)`, `m4 = 12/(25B²)`.
* `gamma_family_one_loop_lower` : for `c < 3`,
  `8/25 < 2/5 + (24/5)(1/24 + c/180)/(1 - c/3)` (no zero along `γ = cβ` at one loop).
* `fund_adj_one_loop_root` : `2/5 + 24 q/(5B) = 0` with `B = β(1+2ρ)`, `q = β(1/24 + ρ/3)`
  iff `ρ = -1/4` (for `β ≠ 0`, `1 + 2ρ ≠ 0`).
* `no_pointwise_sqrt_one_loop` : the one-loop defect `-ψ/3 + 3 q ψ³ - 10 q t ψ` of the pointwise
  relation `(log G)' = F'/2` is not identically zero for any `q, t`.

Only the algebra is formalised: the Haar measure, the moments themselves, the integration by
parts and the saddle-point expansion are not.
-/

namespace LatticeGaugeRatioTwoCriterion

theorem kappa_a_of_ibp (E2 Eh Ec E1 : ℝ) (h : Eh + 2 * Ec = -E1 - 2 * E2) :
    -(Eh / 12 + Ec / 6) / 2 - E2 / 12 = E1 / 24 := by
  linarith

theorem kappa_ab_eq (E2 : ℝ) : (E2 / 12) / 2 = E2 / 24 := by ring

theorem ratio_two_iff (E2 E1 : ℝ) : E2 / 24 = 2 * (E1 / 24) ↔ E2 - 2 * E1 = 0 := by
  constructor <;> intro h <;> linarith

theorem ratio_eq_two_add (E2 E1 : ℝ) (h : E1 ≠ 0) : E2 / E1 = 2 + (E2 - 2 * E1) / E1 := by
  field_simp
  ring

theorem one_loop_D (B q : ℝ) (hB : B ≠ 0) :
    B * ((6 / (5 * B)) / 3 - 3 * q * (12 / (5 * B ^ 2)) + 10 * q * (1 / B) * (6 / (5 * B)))
      = 2 / 5 + 24 * q / (5 * B) := by
  field_simp
  ring

theorem one_loop_D_u1 (B q : ℝ) (hB : B ≠ 0) :
    -B * (3 * q * (12 / (25 * B ^ 2)) - 6 * q * (1 / B) * (2 / (5 * B))) = 24 * q / (25 * B) := by
  field_simp
  ring

theorem gamma_family_one_loop_lower (c : ℝ) (hc : c < 3) :
    8 / 25 < 2 / 5 + (24 / 5) * ((1 / 24 + c / 180) / (1 - c / 3)) := by
  have hpos : 0 < 1 - c / 3 := by linarith
  have key : -1 / 60 < (1 / 24 + c / 180) / (1 - c / 3) := by
    rw [lt_div_iff₀ hpos]
    linarith
  linarith

theorem fund_adj_one_loop_root (β ρ : ℝ) (hβ : β ≠ 0) (hρ : 1 + 2 * ρ ≠ 0) :
    2 / 5 + 24 * (β * (1 / 24 + ρ / 3)) / (5 * (β * (1 + 2 * ρ))) = 0 ↔ ρ = -1 / 4 := by
  have key : 2 / 5 + 24 * (β * (1 / 24 + ρ / 3)) / (5 * (β * (1 + 2 * ρ)))
      = (12 * ρ + 3) / (5 * (1 + 2 * ρ)) := by
    field_simp
    ring
  rw [key, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exfalso
      apply hρ
      linarith
  · intro h
    left
    rw [h]
    norm_num

theorem no_pointwise_sqrt_one_loop (q t : ℝ) :
    ¬ ∀ ψ : ℝ, -ψ / 3 + 3 * q * ψ ^ 3 - 10 * q * t * ψ = 0 := by
  intro h
  have h1 := h 1
  have h2 := h 2
  have hq : q = 0 := by
    ring_nf at h1 h2
    linarith
  rw [hq] at h1
  norm_num at h1

end LatticeGaugeRatioTwoCriterion

#print axioms LatticeGaugeRatioTwoCriterion.kappa_a_of_ibp
#print axioms LatticeGaugeRatioTwoCriterion.kappa_ab_eq
#print axioms LatticeGaugeRatioTwoCriterion.ratio_two_iff
#print axioms LatticeGaugeRatioTwoCriterion.ratio_eq_two_add
#print axioms LatticeGaugeRatioTwoCriterion.one_loop_D
#print axioms LatticeGaugeRatioTwoCriterion.one_loop_D_u1
#print axioms LatticeGaugeRatioTwoCriterion.gamma_family_one_loop_lower
#print axioms LatticeGaugeRatioTwoCriterion.fund_adj_one_loop_root
#print axioms LatticeGaugeRatioTwoCriterion.no_pointwise_sqrt_one_loop
