/-
  Bernstein / Nikolskii type inequalities in the finite dimensional even
  (cosine) basis of degree `m`.

  Everything here is finite dimensional: a trigonometric polynomial
  `p(x) = ∑_{k ≤ m} a k * cos (k x)` is described by its coefficient
  vector, and the "energy" is the coefficient energy `∑_{k ≤ m} (a k)^2`.
  The three statements are

  * `sq_le_energy`        : `p x ^ 2 ≤ (m+1) * energy`      (Nikolskii: sup by L²)
  * `deriv_energy_le`     : `∑ (k * a k)^2 ≤ m^2 * energy`  (Bernstein in ℓ²)
  * `deriv_sq_le_energy`  : `p' x ^ 2 ≤ (m+1) * m^2 * energy`

  together with the fact that the stated derivative really is the derivative.
-/
import Mathlib

namespace TimeBand

open Finset

variable (m : ℕ) (a : ℕ → ℝ)

/-- The even (cosine) trigonometric polynomial of degree `m` with coefficients `a`. -/
noncomputable def cosPoly (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), a k * Real.cos (k * x)

/-- The termwise derivative of `cosPoly`. -/
noncomputable def cosPolyDeriv (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), a k * (-Real.sin (k * x) * k)

/-- The coefficient energy. -/
noncomputable def energy : ℝ :=
  ∑ k ∈ Finset.range (m + 1), a k ^ 2

theorem energy_nonneg : 0 ≤ energy m a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `cosPolyDeriv` is the derivative of `cosPoly`. -/
theorem hasDerivAt_cosPoly (x : ℝ) :
    HasDerivAt (cosPoly m a) (cosPolyDeriv m a x) x := by
  have h : cosPoly m a = ∑ k ∈ Finset.range (m + 1), fun x : ℝ => a k * Real.cos (k * x) := by
    funext y
    simp [cosPoly]
  rw [h, cosPolyDeriv]
  apply HasDerivAt.sum
  intro k _
  have h1 : HasDerivAt (fun x : ℝ => (k : ℝ) * x) (k : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (k : ℝ)
  exact (h1.cos).const_mul (a k)

/-- **Nikolskii**: the sup of a degree `m` cosine polynomial is controlled by its
coefficient energy, with the constant `m + 1` (the dimension). -/
theorem sq_le_energy (x : ℝ) :
    cosPoly m a x ^ 2 ≤ (m + 1 : ℝ) * energy m a := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m + 1))
      (fun k => a k) (fun k => Real.cos (k * x))
  have hcos : ∑ k ∈ Finset.range (m + 1), Real.cos ((k : ℝ) * x) ^ 2 ≤ (m + 1 : ℝ) := by
    calc ∑ k ∈ Finset.range (m + 1), Real.cos ((k : ℝ) * x) ^ 2
        ≤ ∑ _k ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          have := Real.neg_one_le_cos ((k : ℝ) * x)
          have h2 := Real.cos_le_one ((k : ℝ) * x)
          nlinarith [Real.cos_le_one ((k : ℝ) * x), Real.neg_one_le_cos ((k : ℝ) * x)]
      _ = (m + 1 : ℝ) := by simp
  calc cosPoly m a x ^ 2
      = (∑ k ∈ Finset.range (m + 1), a k * Real.cos ((k : ℝ) * x)) ^ 2 := by rfl
    _ ≤ (∑ k ∈ Finset.range (m + 1), a k ^ 2) *
          ∑ k ∈ Finset.range (m + 1), Real.cos ((k : ℝ) * x) ^ 2 := hCS
    _ ≤ (∑ k ∈ Finset.range (m + 1), a k ^ 2) * (m + 1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left hcos
          exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    _ = (m + 1 : ℝ) * energy m a := by rw [mul_comm]; rfl

theorem abs_le_sqrt_energy (x : ℝ) :
    |cosPoly m a x| ≤ Real.sqrt ((m + 1 : ℝ) * energy m a) := by
  have h := sq_le_energy m a x
  have h0 : 0 ≤ (m + 1 : ℝ) * energy m a :=
    mul_nonneg (by positivity) (energy_nonneg m a)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- **Bernstein in ℓ²**: differentiating multiplies each coefficient by `k ≤ m`. -/
theorem deriv_energy_le :
    ∑ k ∈ Finset.range (m + 1), ((k : ℝ) * a k) ^ 2 ≤ (m : ℝ) ^ 2 * energy m a := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkm : (k : ℝ) ≤ (m : ℝ) := by
    have : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have : ((k : ℝ) * a k) ^ 2 = (k : ℝ) ^ 2 * a k ^ 2 := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg (a k))
  nlinarith

/-- The derivative of a degree `m` cosine polynomial obeys the same sup bound with
an extra factor `m^2`. -/
theorem deriv_sq_le_energy (x : ℝ) :
    cosPolyDeriv m a x ^ 2 ≤ (m + 1 : ℝ) * ((m : ℝ) ^ 2 * energy m a) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m + 1))
      (fun k => (k : ℝ) * a k) (fun k => -Real.sin ((k : ℝ) * x))
  have hsin : ∑ k ∈ Finset.range (m + 1), (-Real.sin ((k : ℝ) * x)) ^ 2 ≤ (m + 1 : ℝ) := by
    calc ∑ k ∈ Finset.range (m + 1), (-Real.sin ((k : ℝ) * x)) ^ 2
        ≤ ∑ _k ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          nlinarith [Real.sin_le_one ((k : ℝ) * x), Real.neg_one_le_sin ((k : ℝ) * x)]
      _ = (m + 1 : ℝ) := by simp
  have hrw : cosPolyDeriv m a x
      = ∑ k ∈ Finset.range (m + 1), ((k : ℝ) * a k) * (-Real.sin ((k : ℝ) * x)) := by
    unfold cosPolyDeriv
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), ((k : ℝ) * a k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc cosPolyDeriv m a x ^ 2
      = (∑ k ∈ Finset.range (m + 1), ((k : ℝ) * a k) * (-Real.sin ((k : ℝ) * x))) ^ 2 := by
        rw [hrw]
    _ ≤ (∑ k ∈ Finset.range (m + 1), ((k : ℝ) * a k) ^ 2) *
          ∑ k ∈ Finset.range (m + 1), (-Real.sin ((k : ℝ) * x)) ^ 2 := hCS
    _ ≤ (∑ k ∈ Finset.range (m + 1), ((k : ℝ) * a k) ^ 2) * (m + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsin hnn
    _ ≤ ((m : ℝ) ^ 2 * energy m a) * (m + 1 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (deriv_energy_le m a)
        positivity
    _ = (m + 1 : ℝ) * ((m : ℝ) ^ 2 * energy m a) := by ring

end TimeBand

#print axioms TimeBand.hasDerivAt_cosPoly
#print axioms TimeBand.sq_le_energy
#print axioms TimeBand.abs_le_sqrt_energy
#print axioms TimeBand.deriv_energy_le
#print axioms TimeBand.deriv_sq_le_energy
