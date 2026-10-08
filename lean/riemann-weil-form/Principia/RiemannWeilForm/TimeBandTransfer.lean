/-
  Elementary ingredients of the "transfer" estimate for a time–band operator.

  The analytic statement being supported is:  for `F` of exponential type `L`
  with small tail outside a band `[-T,T]`, the tail of `F(· + iδ)` on the
  shifted horizontal line is bounded by `e^{2L|δ|}` times a power of that
  smallness.  The proof is a Phragmén–Lindelöf / harmonic-majorant argument
  applied to the entire function

      Θ(w) = (1/2π) ∫_{|x|>T} F(x+w) conj(F(x-w)) dx ,

  and the numerical exponent it produces is `(1+ω)/2` with the harmonic
  measure `ω = (2/π) arctan (σ/δ)` of the interval `[-σ,σ]` seen from `iδ`.

  Formalised here (all finite dimensional or one-variable real analysis):

  * `arctan_le_self`, `harmonic_measure_ge` : `(2/π) arctan (σ/δ) ≥ 1 - 2δ/(πσ)`,
      the lower bound for the harmonic measure that turns the majorant into a
      power of the smallness.
  * `rpow_exponent_loss` : `U ^ ω ≤ U / U ^ θ` when `1 - θ ≤ ω` and `0 < U ≤ 1`,
      the passage from the exponent to an explicit constant.
  * `min_one_exp_add_le`, `bandWeight_shift` : the band–edge weight
      `ρ(x) = min 1 (exp ((|x| - T)/R))` satisfies `ρ (x - s) ≤ e^{|s|/R} ρ x`,
      the translation bound used for the smoothed cut-off.
  * `weighted_cauchy_schwarz` : the weighted Cauchy–Schwarz step that bounds
      `Θ` on the real axis by the geometric mean of two tails.
  * `sum_geom_deficiency` : `∑_{k<K} λ^{k+1}(1-λ) = λ (1 - λ^K)`, i.e.
      `∑_{k≤K} tr(Q^k - Q^{k+1}) = tr Q - tr Q^{K+1}` eigenvalue by eigenvalue.
  * `abel_remainder_bound` : a bounded remainder contributes at most
      `(sup |η|) · (total variation)`, the step which makes the constant in the
      trace asymptotics independent of `K`.
  * `transfer_of_ratio` : the composition step from the ratio form of the
      transfer estimate to the subspace form.
-/
import Mathlib

namespace TimeBand

open Finset

/-! ### Harmonic measure of an interval seen from a point of the imaginary axis -/

/-- `arctan y ≤ y` for `0 ≤ y`. -/
theorem arctan_le_self {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  have h0 : 0 ≤ Real.arctan y := Real.arctan_nonneg.mpr hy
  have h1 : Real.arctan y < Real.pi / 2 := Real.arctan_lt_pi_div_two y
  have h2 := Real.le_tan h0 h1
  rwa [Real.tan_arctan] at h2

/-- The harmonic measure of `[-σ, σ]` at the point `i δ` of the upper half plane is
`(2/π) arctan (σ/δ)`, and it is at least `1 - 2δ/(π σ)`. -/
theorem harmonic_measure_ge {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    1 - 2 * d / (Real.pi * s) ≤ (2 / Real.pi) * Real.arctan (s / d) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hds : (0 : ℝ) < d / s := div_pos hd hs
  have hinv : (d / s)⁻¹ = s / d := by
    field_simp
  have h1 : Real.arctan (s / d) = Real.pi / 2 - Real.arctan (d / s) := by
    have h := Real.arctan_inv_of_pos hds
    rwa [hinv] at h
  have h2 : Real.arctan (d / s) ≤ d / s := arctan_le_self (le_of_lt hds)
  have h3 : (2 / Real.pi) * Real.arctan (d / s) ≤ (2 / Real.pi) * (d / s) := by
    apply mul_le_mul_of_nonneg_left h2
    positivity
  have h4 : (2 / Real.pi) * (Real.pi / 2 - Real.arctan (d / s))
      = 1 - (2 / Real.pi) * Real.arctan (d / s) := by
    field_simp
  have h5 : (2 / Real.pi) * (d / s) = 2 * d / (Real.pi * s) := by
    field_simp
  rw [h1, h4]
  linarith [h3, h5.symm ▸ h3]

/-- Turning the exponent produced by the harmonic majorant into a constant:
if `1 - θ ≤ ω` and `0 < U ≤ 1` then `U ^ ω ≤ U / U ^ θ`. -/
theorem rpow_exponent_loss {U om th : ℝ} (hU0 : 0 < U) (hU1 : U ≤ 1)
    (hth : 1 - th ≤ om) : U ^ om ≤ U / U ^ th := by
  have h1 : U ^ om ≤ U ^ (1 - th) :=
    Real.rpow_le_rpow_of_exponent_ge hU0 hU1 hth
  have h2 : U ^ (1 - th) = U / U ^ th := by
    rw [Real.rpow_sub hU0, Real.rpow_one]
  rwa [h2] at h1

/-! ### The band-edge weight and its translation bound -/

/-- `min 1 (exp (a + s)) ≤ exp s * min 1 (exp a)` for `0 ≤ s`. -/
theorem min_one_exp_add_le {a s : ℝ} (hs : 0 ≤ s) :
    min 1 (Real.exp (a + s)) ≤ Real.exp s * min 1 (Real.exp a) := by
  rcases le_total (Real.exp a) 1 with h | h
  · have hmin : min 1 (Real.exp a) = Real.exp a := min_eq_right h
    have hexp : Real.exp s * Real.exp a = Real.exp (a + s) := by
      rw [← Real.exp_add, add_comm]
    rw [hmin, hexp]
    exact min_le_right _ _
  · have hmin : min 1 (Real.exp a) = 1 := min_eq_left h
    rw [hmin, mul_one]
    exact le_trans (min_le_left _ _) (Real.one_le_exp hs)

/-- The band-edge weight: `1` outside the band `[-T,T]`, decaying like
`exp ((|x| - T)/R)` inside it. -/
noncomputable def bandWeight (T R x : ℝ) : ℝ := min 1 (Real.exp ((|x| - T) / R))

theorem bandWeight_pos (T R x : ℝ) : 0 < bandWeight T R x :=
  lt_min one_pos (Real.exp_pos _)

theorem bandWeight_le_one (T R x : ℝ) : bandWeight T R x ≤ 1 := min_le_left _ _

/-- Outside the band the weight is `1`, so it dominates the sharp cut-off. -/
theorem one_le_bandWeight_of_le_abs {T R x : ℝ} (hR : 0 < R) (hx : T ≤ |x|) :
    1 ≤ bandWeight T R x := by
  have h : (0 : ℝ) ≤ (|x| - T) / R := div_nonneg (by linarith) (le_of_lt hR)
  exact le_min le_rfl (Real.one_le_exp h)

/-- Translation bound for the band-edge weight. -/
theorem bandWeight_shift {T R : ℝ} (hR : 0 < R) (x s : ℝ) :
    bandWeight T R (x - s) ≤ Real.exp (|s| / R) * bandWeight T R x := by
  have habs : |x - s| ≤ |x| + |s| := by
    have h3 := le_abs_self x
    have h4 := neg_abs_le x
    have h5 := le_abs_self s
    have h6 := neg_abs_le s
    rcases abs_cases (x - s) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have hle : (|x - s| - T) / R ≤ (|x| - T) / R + |s| / R := by
    rw [← add_div]
    gcongr
    linarith
  have hmono : min 1 (Real.exp ((|x - s| - T) / R))
      ≤ min 1 (Real.exp ((|x| - T) / R + |s| / R)) :=
    min_le_min le_rfl (Real.exp_le_exp.mpr hle)
  refine hmono.trans ?_
  exact min_one_exp_add_le (div_nonneg (abs_nonneg s) (le_of_lt hR))

/-! ### The Cauchy–Schwarz step on the real axis -/

/-- Weighted Cauchy–Schwarz: this is the step bounding `Θ(σ)` by the geometric
mean of the two shifted tails. -/
theorem weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (a i * b i)) ^ 2
      ≤ (∑ i ∈ s, w i * a i ^ 2) * (∑ i ∈ s, w i * b i ^ 2) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (w i) * a i) (fun i => Real.sqrt (w i) * b i)
  have e1 : ∑ i ∈ s, (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)
      = ∑ i ∈ s, w i * (a i * b i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have h := Real.mul_self_sqrt (hw i hi)
    calc (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * (a i * b i) := by ring
      _ = w i * (a i * b i) := by rw [h]
  have e2 : ∑ i ∈ s, (Real.sqrt (w i) * a i) ^ 2 = ∑ i ∈ s, w i * a i ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have h := Real.sq_sqrt (hw i hi)
    calc (Real.sqrt (w i) * a i) ^ 2 = (Real.sqrt (w i)) ^ 2 * a i ^ 2 := by ring
      _ = w i * a i ^ 2 := by rw [h]
  have e3 : ∑ i ∈ s, (Real.sqrt (w i) * b i) ^ 2 = ∑ i ∈ s, w i * b i ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have h := Real.sq_sqrt (hw i hi)
    calc (Real.sqrt (w i) * b i) ^ 2 = (Real.sqrt (w i)) ^ 2 * b i ^ 2 := by ring
      _ = w i * b i ^ 2 := by rw [h]
  rwa [e1, e2, e3] at key

/-! ### The telescoping identity behind the trace asymptotics -/

/-- `∑_{k < K} λ^{k+1} (1 - λ) = λ (1 - λ^K)`.  Summed over the spectrum this is
`∑_{k ≤ K} tr (Q^k - Q^{k+1}) = tr Q - tr Q^{K+1}`. -/
theorem sum_geom_deficiency (lam : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, lam ^ (k + 1) * (1 - lam) = lam * (1 - lam ^ K) := by
  induction K with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A bounded remainder contributes at most `E` times the total variation.
This is why the constant in the trace asymptotics does not depend on `K`. -/
theorem abel_remainder_bound {n : ℕ} (eta phi : ℕ → ℝ) (E : ℝ)
    (hE : ∀ i, |eta i| ≤ E) :
    |∑ i ∈ Finset.range n, eta i * (phi (i + 1) - phi i)|
      ≤ E * ∑ i ∈ Finset.range n, |phi (i + 1) - phi i| := by
  calc |∑ i ∈ Finset.range n, eta i * (phi (i + 1) - phi i)|
      ≤ ∑ i ∈ Finset.range n, |eta i * (phi (i + 1) - phi i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, |eta i| * |phi (i + 1) - phi i| := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [abs_mul]
    _ ≤ ∑ i ∈ Finset.range n, E * |phi (i + 1) - phi i| := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact mul_le_mul_of_nonneg_right (hE i) (abs_nonneg _)
    _ = E * ∑ i ∈ Finset.range n, |phi (i + 1) - phi i| := by
        rw [Finset.mul_sum]

/-! ### From the ratio form to the subspace form -/

/-- If the transferred quadratic form is at most `c` times the original one on a
set `S`, and the original one is at most `u` times the norm on `S`, then the
transferred form is at most `c * u` times the norm on `S`. -/
theorem transfer_of_ratio {α : Type*} (S : Set α) (qN qNM nrm : α → ℝ) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc : ∀ f ∈ S, qNM f ≤ c * qN f) (hu : ∀ f ∈ S, qN f ≤ u * nrm f) :
    ∀ f ∈ S, qNM f ≤ c * u * nrm f := by
  intro f hf
  calc qNM f ≤ c * qN f := hc f hf
    _ ≤ c * (u * nrm f) := mul_le_mul_of_nonneg_left (hu f hf) hc0
    _ = c * u * nrm f := by ring

end TimeBand

#print axioms TimeBand.arctan_le_self
#print axioms TimeBand.harmonic_measure_ge
#print axioms TimeBand.rpow_exponent_loss
#print axioms TimeBand.min_one_exp_add_le
#print axioms TimeBand.one_le_bandWeight_of_le_abs
#print axioms TimeBand.bandWeight_shift
#print axioms TimeBand.weighted_cauchy_schwarz
#print axioms TimeBand.sum_geom_deficiency
#print axioms TimeBand.abel_remainder_bound
#print axioms TimeBand.transfer_of_ratio
