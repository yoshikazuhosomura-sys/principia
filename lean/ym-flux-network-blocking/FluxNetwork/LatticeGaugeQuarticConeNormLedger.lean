import Mathlib

/-!
# Two normalisations of the quartic cone: a finite ledger

For a direction `θ` (finite family) with image `φ = Fθ` (finite family) write
`N = ∑ φ⁴`, `D4 = ∑ θ⁴`, `Q = ∑ φ²`, `D2 = ∑ θ²`, so that
`μ = N / D4` (quartic ratio, long-wavelength normalisation), `β' = Q / D2`
(direction quadratic ratio) and `λ = μ / β'` (direction normalisation).
If `bmin * D2 ≤ Q ≤ bmax * D2` with `0 < bmin`, then
* `ledger`        : `bmin * λ ≤ μ ≤ bmax * λ`;
* `transfer`      : `N ≤ M * D4` gives `bmin * (N * D2) ≤ M * (D4 * Q)`, i.e. `λ ≤ M / bmin`;
* `cone_b_to_a`   : a cone in the direction normalisation, `|X| * D2 ≤ x * Q * D4`,
                    is a cone in the long-wavelength one with constant `x * bmax`;
* `stein_floor`   : if `A_i^2 ≤ F * v_i` (weights `v_i`) and `0 ≤ ν_i ≤ A_i`,
                    then `∑ ν_i^2 ≤ F * ∑ v_i` (the zero-momentum floor of a weighted interpolation bound).
Only finite real arithmetic is formalised; no lattice, no interpolation theorem, no limit.
-/

namespace LatticeGauge.QuarticConeNorm

open Finset

variable {ι κ : Type*}

theorem ratio_sandwich (μ b bmin bmax : ℝ) (hb : 0 < bmin) (hlo : bmin ≤ b) (hhi : b ≤ bmax)
    (hμ : 0 ≤ μ) : bmin * (μ / b) ≤ μ ∧ μ ≤ bmax * (μ / b) := by
  have hbp : 0 < b := lt_of_lt_of_le hb hlo
  have hq : 0 ≤ μ / b := div_nonneg hμ hbp.le
  have e : b * (μ / b) = μ := by field_simp
  constructor
  · calc bmin * (μ / b) ≤ b * (μ / b) := mul_le_mul_of_nonneg_right hlo hq
      _ = μ := e
  · calc μ = b * (μ / b) := e.symm
      _ ≤ bmax * (μ / b) := mul_le_mul_of_nonneg_right hhi hq

theorem ledger (s : Finset ι) (t : Finset κ) (θ : ι → ℝ) (φ : κ → ℝ) (bmin bmax : ℝ)
    (hb : 0 < bmin) (hD2 : 0 < ∑ i ∈ s, θ i ^ 2) (hD4 : 0 < ∑ i ∈ s, θ i ^ 4)
    (hlo : bmin * ∑ i ∈ s, θ i ^ 2 ≤ ∑ q ∈ t, φ q ^ 2)
    (hhi : ∑ q ∈ t, φ q ^ 2 ≤ bmax * ∑ i ∈ s, θ i ^ 2) :
    bmin * (((∑ q ∈ t, φ q ^ 4) / ∑ i ∈ s, θ i ^ 4) / ((∑ q ∈ t, φ q ^ 2) / ∑ i ∈ s, θ i ^ 2))
        ≤ (∑ q ∈ t, φ q ^ 4) / ∑ i ∈ s, θ i ^ 4 ∧
      (∑ q ∈ t, φ q ^ 4) / ∑ i ∈ s, θ i ^ 4
        ≤ bmax * (((∑ q ∈ t, φ q ^ 4) / ∑ i ∈ s, θ i ^ 4) / ((∑ q ∈ t, φ q ^ 2) / ∑ i ∈ s, θ i ^ 2)) := by
  apply ratio_sandwich _ _ _ _ hb
  · rw [le_div_iff₀ hD2]; linarith
  · rw [div_le_iff₀ hD2]; linarith
  · exact div_nonneg (sum_nonneg (fun q _ => by positivity)) hD4.le

theorem transfer (N D4 D2 Q M bmin : ℝ) (hb : 0 < bmin) (hD2 : 0 ≤ D2)
    (hM : 0 ≤ M * D4) (hμ : N ≤ M * D4) (hlo : bmin * D2 ≤ Q) :
    bmin * (N * D2) ≤ M * (D4 * Q) := by
  have h := mul_le_mul hμ hlo (by positivity) hM
  calc bmin * (N * D2) = N * (bmin * D2) := by ring
    _ ≤ M * D4 * Q := h
    _ = M * (D4 * Q) := by ring

theorem cone_b_to_a (X D4 D2 Q x bmax : ℝ) (hD2 : 0 < D2) (hx : 0 ≤ x) (hD4 : 0 ≤ D4)
    (hc : |X| * D2 ≤ x * Q * D4) (hhi : Q ≤ bmax * D2) :
    |X| ≤ x * bmax * D4 := by
  have h1 : x * Q * D4 ≤ x * (bmax * D2) * D4 := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hx) hD4
  have h2 : |X| * D2 ≤ (x * bmax * D4) * D2 := by
    calc |X| * D2 ≤ x * (bmax * D2) * D4 := le_trans hc h1
      _ = (x * bmax * D4) * D2 := by ring
  exact le_of_mul_le_mul_right h2 hD2

theorem stein_floor (s : Finset ι) (A v ν : ι → ℝ) (F : ℝ)
    (hF : ∀ i ∈ s, A i ^ 2 ≤ F * v i) (hν : ∀ i ∈ s, 0 ≤ ν i ∧ ν i ≤ A i) :
    ∑ i ∈ s, ν i ^ 2 ≤ F * ∑ i ∈ s, v i := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  obtain ⟨h0, h1⟩ := hν i hi
  have : ν i ^ 2 ≤ A i ^ 2 := pow_le_pow_left₀ h0 h1 2
  exact le_trans this (hF i hi)

end LatticeGauge.QuarticConeNorm

#print axioms LatticeGauge.QuarticConeNorm.ratio_sandwich
#print axioms LatticeGauge.QuarticConeNorm.ledger
#print axioms LatticeGauge.QuarticConeNorm.transfer
#print axioms LatticeGauge.QuarticConeNorm.cone_b_to_a
#print axioms LatticeGauge.QuarticConeNorm.stein_floor
