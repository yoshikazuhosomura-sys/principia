/-
premise 4 (supply w ≤ Φ(u), and the moment M of one block). Single file; checks with `import Mathlib` only.

  §1 Supply: the probability of the union of large-field events {Y_p ≥ y_h} over plaquettes p ∈ P of a block
     ≤ Σ_p M_p e^{−t y_h} ≤ n_p m e^{−t y_h} (Chernoff and the union bound)
  §2 Form of Φ: Φ(u) = n_p m e^{−t y_h(u)}. If the threshold y_h(u) is increasing in u, Φ is decreasing
     (supply_anti of the chain). The fixed plaquette-angle threshold y_h(u) = 4u(1 − cos θ_h) (β = 4u) is an example
  §3 Moment M (independent case): if plaquette energies are independent, the moment of the sum is the product,
     M ≤ m₁^{n_p} (Mathlib's iIndepFun.mgf_sum)
  §4 Moment M (dependent case, Hölder): ∫ e^{t Σ_i Y_i} ≤ max(∫ e^{n t Y_i}) (n = number of plaquettes, integrals in ℝ≥0∞)
  §5 #print axioms

The single-plaquette moment m₁ (expectation of e^{tY} under the Wilson action) is a premise
(the χ²₃-type reading is (reading)).
-/
import Mathlib

namespace LargeFieldSupply

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1. Supply (union bound and Chernoff) -/

theorem supply_union (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} (P : Finset ι)
    (Y : ι → Ω → ℝ) (t yh m : ℝ) (ht : 0 ≤ t)
    (hint : ∀ p ∈ P, Integrable (fun ω => Real.exp (t * Y p ω)) μ)
    (hm : ∀ p ∈ P, mgf (Y p) μ t ≤ m) :
    μ.real (⋃ p ∈ P, {ω | yh ≤ Y p ω}) ≤ P.card * m * Real.exp (-t * yh) := by
  calc μ.real (⋃ p ∈ P, {ω | yh ≤ Y p ω}) ≤ ∑ p ∈ P, μ.real {ω | yh ≤ Y p ω} :=
        measureReal_biUnion_finset_le P _
    _ ≤ ∑ _p ∈ P, m * Real.exp (-t * yh) := by
        apply sum_le_sum
        intro p hp
        have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := Y p) yh ht (hint p hp)
        calc μ.real {ω | yh ≤ Y p ω} ≤ Real.exp (-t * yh) * mgf (Y p) μ t := h
          _ ≤ Real.exp (-t * yh) * m := mul_le_mul_of_nonneg_left (hm p hp) (Real.exp_pos _).le
          _ = m * Real.exp (-t * yh) := mul_comm _ _
    _ = P.card * m * Real.exp (-t * yh) := by rw [sum_const, nsmul_eq_mul]; ring

/-! ## 2. Form and monotonicity of Φ -/

/-- `Φ(u) = n m e^{−t y_h(u)}` is decreasing if `y_h` is increasing and `t, n, m ≥ 0`. -/
theorem phi_antitone (n m t : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m) (ht : 0 ≤ t) (yh : ℝ → ℝ)
    (hy : Monotone yh) : Antitone fun u => n * m * Real.exp (-t * yh u) := by
  intro s u hsu
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hn hm)
  apply Real.exp_le_exp.mpr
  have := hy hsu
  nlinarith

/-- Fixed plaquette-angle threshold: `y_h(u) = 4u(1 − cos θ_h)` is increasing. -/
theorem fixed_angle_monotone (θh : ℝ) : Monotone fun u : ℝ => 4 * u * (1 - Real.cos θh) := by
  intro s u hsu
  have : 0 ≤ 1 - Real.cos θh := by linarith [Real.cos_le_one θh]
  nlinarith

/-- The supply_anti form of the chain (`ustar ≤ s ≤ t ⇒ Φ t ≤ Φ s`). -/
theorem supply_anti_form (n m t : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m) (ht : 0 ≤ t) (yh : ℝ → ℝ)
    (hy : Monotone yh) (ustar : ℝ) :
    ∀ s v : ℝ, ustar ≤ s → s ≤ v →
      n * m * Real.exp (-t * yh v) ≤ n * m * Real.exp (-t * yh s) :=
  fun s v _ hsv => phi_antitone n m t hn hm ht yh hy hsv

/-! ## 3. Moments (independent case) -/

theorem block_mgf_indep (μ : Measure Ω) {ι : Type*} (P : Finset ι) (Y : ι → Ω → ℝ) (t m₁ : ℝ)
    (hind : iIndepFun Y μ) (hmeas : ∀ p, Measurable (Y p)) (hm : ∀ p ∈ P, mgf (Y p) μ t ≤ m₁) :
    mgf (∑ p ∈ P, Y p) μ t ≤ m₁ ^ P.card := by
  rw [hind.mgf_sum hmeas P]
  calc ∏ p ∈ P, mgf (Y p) μ t ≤ ∏ _p ∈ P, m₁ :=
        prod_le_prod (fun p _ => mgf_nonneg) hm
    _ = m₁ ^ P.card := prod_const _

/-! ## 4. Moments (Hölder) -/

/-- Without independence: for `n = |P| ≥ 1` plaquettes, `∫⁻ e^{t Σ Y_p} ≤ m`, provided `∫⁻ e^{n t Y_p} ≤ m`
for each plaquette. -/
theorem block_mgf_holder (μ : Measure Ω) {ι : Type*} (P : Finset ι) (hP : 0 < P.card)
    (Y : ι → Ω → ℝ) (t : ℝ) (m : ℝ≥0∞) (hmeas : ∀ p, Measurable (Y p))
    (hm : ∀ p ∈ P, ∫⁻ ω, ENNReal.ofReal (Real.exp (P.card * t * Y p ω)) ∂μ ≤ m) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ∑ p ∈ P, Y p ω)) ∂μ ≤ m := by
  set n : ℝ := ((P.card : ℕ) : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hP
  have hsum : ∑ p ∈ P, (1 / n) = 1 := by rw [sum_const, nsmul_eq_mul, ← hn]; field_simp
  have hH := ENNReal.lintegral_prod_norm_pow_le (μ := μ) P
    (f := fun p ω => ENNReal.ofReal (Real.exp (n * t * Y p ω)))
    (fun p _ => (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (hmeas p)))).aemeasurable)
    (p := fun _ => 1 / n) hsum (fun _ _ => by positivity)
  have hpt : ∀ ω, ∏ p ∈ P, ENNReal.ofReal (Real.exp (n * t * Y p ω)) ^ (1 / n) =
      ENNReal.ofReal (Real.exp (t * ∑ p ∈ P, Y p ω)) := by
    intro ω
    have h1 : ∀ p ∈ P, ENNReal.ofReal (Real.exp (n * t * Y p ω)) ^ (1 / n) =
        ENNReal.ofReal (Real.exp (t * Y p ω)) := by
      intro p _
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
      congr 2; field_simp
    rw [prod_congr rfl h1, ← ENNReal.ofReal_prod_of_nonneg (fun p _ => (Real.exp_pos _).le),
      ← Real.exp_sum, mul_sum]
  simp_rw [hpt] at hH
  refine le_trans hH ?_
  calc ∏ p ∈ P, (∫⁻ ω, ENNReal.ofReal (Real.exp (n * t * Y p ω)) ∂μ) ^ (1 / n)
      ≤ ∏ _p ∈ P, m ^ (1 / n) :=
        prod_le_prod' fun p hp => ENNReal.rpow_le_rpow (hm p hp) (by positivity)
    _ = m := by
        rw [prod_const, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        have : 1 / n * (P.card : ℝ) = 1 := by rw [← hn]; field_simp
        rw [this, ENNReal.rpow_one]

#print axioms supply_union
#print axioms phi_antitone
#print axioms fixed_angle_monotone
#print axioms supply_anti_form
#print axioms block_mgf_indep
#print axioms block_mgf_holder

end LargeFieldSupply
