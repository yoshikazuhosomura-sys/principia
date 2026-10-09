/-
The Euler factor of the p-adic L-function at an anomalous prime.

For E/Q with good ordinary reduction at p >= 5 let alpha be the unit root of
X^2 - a_p X + p.  The interpolation factor of the Mazur-Tate-Teitelbaum p-adic
L-function is (1 - alpha^{-1})^2, and v_p(1 - alpha^{-1}) = v_p(alpha - 1).

This file formalises the two closed arithmetic steps of that computation:

* `ap_of_anomalous` : the Hasse bound plus the congruence a_p = 1 (mod p) leave
  only a_p = 1, or the single exception p = 5, a_p = -4.
* `unit_root_identity`, `sub_one_associated_p`, `sub_one_associated_p_of_pred` :
  the identity alpha*(alpha-1) = (a-1)*alpha - p, and the conclusion that in the
  two surviving cases alpha - 1 is p times a unit -- which in Z_p is exactly
  v_p(alpha - 1) = 1.
-/
import Mathlib

namespace AnomalousEuler

/-- If `a` is congruent to `1` modulo `p` and satisfies the Hasse bound
`a^2 ≤ 4p` for a rational prime `p ≥ 5`, then `a = 1`, or `p = 5` and `a = -4`. -/
theorem ap_of_anomalous {p : ℕ} (hp5 : 5 ≤ p) {a : ℤ}
    (hdvd : (p : ℤ) ∣ a - 1) (hasse : a ^ 2 ≤ 4 * p) :
    a = 1 ∨ (p = 5 ∧ a = -4) := by
  have hp : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
  obtain ⟨k, hk⟩ := hdvd
  have ha : a = 1 + (p : ℤ) * k := by linarith [hk]
  rcases lt_trichotomy k 0 with hneg | hzero | hpos
  · -- k ≤ -1
    have hk1 : k = -1 ∨ k ≤ -2 := by omega
    rcases hk1 with h | h
    · -- a = 1 - p : the Hasse bound gives p^2 - 6p + 1 ≤ 0, hence p = 5
      have ha' : a = 1 - (p : ℤ) := by rw [ha, h]; ring
      have hple : (p : ℤ) ≤ 5 := by nlinarith [hasse, ha', hp]
      have hp5' : (p : ℤ) = 5 := le_antisymm hple hp
      exact Or.inr ⟨by exact_mod_cast hp5', by rw [ha', hp5']; ring⟩
    · -- a ≤ 1 - 2p, so a^2 ≥ (2p-1)^2 > 4p
      exfalso
      have hpk : (p : ℤ) * k ≤ -2 * (p : ℤ) := by nlinarith
      have hale : a ≤ 1 - 2 * (p : ℤ) := by linarith
      nlinarith [hasse, hale, hp, sq_nonneg (a - 1 + 2 * (p : ℤ))]
  · left; rw [ha, hzero]; ring
  · -- k ≥ 1, so a ≥ 1 + p and a^2 ≥ (1+p)^2 > 4p
    exfalso
    have hk1 : (1 : ℤ) ≤ k := hpos
    have hpk : (p : ℤ) ≤ (p : ℤ) * k := by nlinarith
    have hage : 1 + (p : ℤ) ≤ a := by linarith
    nlinarith [hasse, hage, hp, sq_nonneg (a - 1 - (p : ℤ))]

/-- `alpha^2 = a*alpha - p` gives `alpha*(alpha-1) = (a-1)*alpha - p`. -/
theorem unit_root_identity {R : Type*} [CommRing R] (α a p : R) (h : α ^ 2 = a * α - p) :
    α * (α - 1) = (a - 1) * α - p := by linear_combination h

/-- The anomalous case `a = 1`: if `alpha` is a unit and `alpha^2 = alpha - p`,
then `alpha - 1` is `p` times a unit.  Over `Z_p` this says `v_p(alpha-1) = 1`. -/
theorem sub_one_associated_p {R : Type*} [CommRing R] {α p : R} (hu : IsUnit α)
    (h : α ^ 2 = α - p) : ∃ u : R, IsUnit u ∧ α - 1 = u * p := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨-(↑u⁻¹ : R), (Units.isUnit u⁻¹).neg, ?_⟩
  have h1 : (u : R) * ((u : R) - 1) = -p := by linear_combination h
  have hv : (u : R) * (↑u⁻¹ : R) = 1 := u.mul_inv
  calc (u : R) - 1 = ((u : R) * ((u : R) - 1)) * (↑u⁻¹ : R) := by
        rw [mul_comm (u : R) ((u : R) - 1), mul_assoc, hv, mul_one]
    _ = -p * (↑u⁻¹ : R) := by rw [h1]
    _ = -(↑u⁻¹ : R) * p := by ring

/-- The exceptional case `a = 1 - p` (by `ap_of_anomalous` only `p = 5`, `a = -4`):
if `alpha` and `alpha + 1` are units and `alpha^2 = (1-p)*alpha - p`, then again
`alpha - 1` is `p` times a unit. -/
theorem sub_one_associated_p_of_pred {R : Type*} [CommRing R] {α p : R} (hu : IsUnit α)
    (hu1 : IsUnit (α + 1)) (h : α ^ 2 = (1 - p) * α - p) :
    ∃ u : R, IsUnit u ∧ α - 1 = u * p := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨-((u : R) + 1) * (↑u⁻¹ : R), (hu1.neg).mul (Units.isUnit u⁻¹), ?_⟩
  have h1 : (u : R) * ((u : R) - 1) = -(p * ((u : R) + 1)) := by linear_combination h
  have hv : (u : R) * (↑u⁻¹ : R) = 1 := u.mul_inv
  calc (u : R) - 1 = ((u : R) * ((u : R) - 1)) * (↑u⁻¹ : R) := by
        rw [mul_comm (u : R) ((u : R) - 1), mul_assoc, hv, mul_one]
    _ = -(p * ((u : R) + 1)) * (↑u⁻¹ : R) := by rw [h1]
    _ = -((u : R) + 1) * (↑u⁻¹ : R) * p := by ring

end AnomalousEuler

#print axioms AnomalousEuler.ap_of_anomalous
#print axioms AnomalousEuler.unit_root_identity
#print axioms AnomalousEuler.sub_one_associated_p
#print axioms AnomalousEuler.sub_one_associated_p_of_pred
