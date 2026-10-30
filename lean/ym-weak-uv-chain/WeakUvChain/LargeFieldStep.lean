/-
One large-field step: rarity bound (Chernoff type), healing (arithmetic of defects of convex combinations, and Markov),
and arithmetic of the KP threshold. Single file; checks with `import Mathlib` only.

  §1 Rarity: if the exponential moment E[e^{tY}] ≤ M then P(Y ≥ y_h) ≤ M e^{−t y_h}; form of the chain event
     {θ_h < I} (in ℝ≥0∞)
  §2 Healing (deterministic): if the coarse-block defect d′ is bounded by a convex combination of fine defects
     (arithmetic of defects of projected convex combinations), good parts have defect ≤ δ and bad parts ≤ 2,
     then d′ ≤ δ + 2 w(bad)
  §3 Healing (probabilistic): P(coarse block is large, d′ > θ) ≤ Σ wᵢ P(fine i is bad) / ((θ − δ)/2) (Markov)
  §4 KP threshold: M e^{−t y_h} ≤ 1/(2Δe²) holds for y_h ≥ log(2Δe² M)/t
  §5 #print axioms

The lattice measure, the moment values of the Wilson action, and convexity of the defect (projection of quaternion
averages) enter as premises.
-/
import Mathlib

namespace LargeFieldStep

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-! ## 1. Rarity (Chernoff type) -/

section Rarity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If the exponential moment is at most `M` then `P(Y ≥ y_h) ≤ M e^{−t y_h}` (`t ≥ 0`). -/
theorem rarity_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (t yh M : ℝ)
    (ht : 0 ≤ t) (hint : Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hM : mgf Y μ t ≤ M) :
    μ.real {ω | yh ≤ Y ω} ≤ M * Real.exp (-t * yh) := by
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := Y) yh ht hint
  have he : 0 ≤ Real.exp (-t * yh) := (Real.exp_pos _).le
  calc μ.real {ω | yh ≤ Y ω} ≤ Real.exp (-t * yh) * mgf Y μ t := h
    _ ≤ Real.exp (-t * yh) * M := mul_le_mul_of_nonneg_left hM he
    _ = M * Real.exp (-t * yh) := mul_comm _ _

/-- In the form of the chain event `{θ_h < I}`: the `ℝ≥0∞` bound `ofReal (M e^{−t θ_h})`. -/
theorem rarity_ennreal (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Ω → ℝ) (t θh M : ℝ)
    (ht : 0 ≤ t) (hint : Integrable (fun ω => Real.exp (t * I ω)) μ)
    (hM : mgf I μ t ≤ M) :
    μ {ω | θh < I ω} ≤ ENNReal.ofReal (M * Real.exp (-t * θh)) := by
  have hsub : {ω | θh < I ω} ⊆ {ω | θh ≤ I ω} := by
    intro ω h; exact le_of_lt (show θh < I ω from h)
  have h1 : μ {ω | θh < I ω} ≤ μ {ω | θh ≤ I ω} := measure_mono hsub
  have h2 := rarity_chernoff μ I t θh M ht hint hM
  refine le_trans h1 ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | θh ≤ I ω})]
  exact ENNReal.ofReal_le_ofReal (by rwa [measureReal_def] at h2)

end Rarity

/-! ## 2. Healing (deterministic) -/

/-- If the coarse-block defect satisfies `d′ ≤ Σ wᵢ dᵢ` (wᵢ ≥ 0, Σ wᵢ = 1), good parts (`i ∉ bad`) have defect `≤ δ`
and bad parts `≤ 2` (the real-part defect of a quaternion, 1 − cos θ ≤ 2), then `d′ ≤ δ + 2 Σ_{i ∈ bad} wᵢ`. -/
theorem healing_deterministic {ι : Type*} [DecidableEq ι] (s bad : Finset ι) (w d : ι → ℝ) (d' δ : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hδ : 0 ≤ δ)
    (hconv : d' ≤ ∑ i ∈ s, w i * d i)
    (hgood : ∀ i ∈ s, i ∉ bad → d i ≤ δ) (hbad : ∀ i ∈ s, i ∈ bad → d i ≤ 2) :
    d' ≤ δ + 2 * ∑ i ∈ s.filter (· ∈ bad), w i := by
  have hpt : ∀ i ∈ s, w i * d i ≤ w i * δ + 2 * (if i ∈ bad then w i else 0) := by
    intro i hi
    by_cases hb : i ∈ bad
    · simp only [hb, if_true]
      have := mul_le_mul_of_nonneg_left (hbad i hi hb) (hw i hi)
      have : 0 ≤ w i * δ := mul_nonneg (hw i hi) hδ
      linarith
    · simp only [hb, if_false, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood i hi hb) (hw i hi)
  have hsumle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, ← Finset.mul_sum,
    ← Finset.sum_filter] at hsumle
  linarith

/-! ## 3. Healing (probabilistic, Markov) -/

section HealingProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For the bad weight `W(ω) = Σ wᵢ 1_{badᵢ}(ω)`, `P(W ≥ s) ≤ (Σ wᵢ P(badᵢ))/s` (`s > 0`). -/
theorem healing_markov (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (Bad : ι → Set Ω) (hB : ∀ i, MeasurableSet (Bad i))
    (s : ℝ) (hs : 0 < s) :
    μ.real {ω | s ≤ ∑ i ∈ S, w i * (Bad i).indicator 1 ω} ≤
      (∑ i ∈ S, w i * μ.real (Bad i)) / s := by
  set W : Ω → ℝ := fun ω => ∑ i ∈ S, w i * (Bad i).indicator 1 ω with hW
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw i hi)
    by_cases h : ω ∈ Bad i <;> simp [h]
  have hint : Integrable W μ := by
    apply integrable_finsetSum
    intro i _
    exact ((integrable_const (1 : ℝ)).indicator (hB i)).const_mul (w i) |>.congr
      (Filter.Eventually.of_forall fun ω => by simp [Set.indicator])
  have hEW : ∫ ω, W ω ∂μ = ∑ i ∈ S, w i * μ.real (Bad i) := by
    rw [hW, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
      congr 1
      have : (fun ω => (Bad i).indicator (1 : Ω → ℝ) ω) = (Bad i).indicator (fun _ => (1 : ℝ)) := rfl
      rw [this, integral_indicator_const _ (hB i), smul_eq_mul, mul_one]
    · intro i _
      exact ((integrable_const (1 : ℝ)).indicator (hB i)).const_mul (w i) |>.congr
        (Filter.Eventually.of_forall fun ω => by simp [Set.indicator])
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hW0) hint s
  rw [hEW] at hm
  rw [le_div_iff₀ hs]
  linarith

end HealingProb

/-! ## 4. KP threshold -/

/-- `M e^{−t y_h} ≤ 1/(2Δe²)` (the ε of the KP condition) holds when `y_h ≥ log(2Δe² M)/t` (`t > 0`, `M, Δ > 0`). -/
theorem kp_threshold (M t Δ yh : ℝ) (hM : 0 < M) (ht : 0 < t) (hΔ : 0 < Δ)
    (hy : Real.log (2 * Δ * Real.exp 1 ^ 2 * M) / t ≤ yh) :
    M * Real.exp (-t * yh) ≤ 1 / (2 * Δ * Real.exp 1 ^ 2) := by
  have hK : 0 < 2 * Δ * Real.exp 1 ^ 2 := by positivity
  have h1 : Real.log (2 * Δ * Real.exp 1 ^ 2 * M) ≤ t * yh := by
    have := (div_le_iff₀ ht).mp hy
    linarith [mul_comm yh t]
  have h2 : 2 * Δ * Real.exp 1 ^ 2 * M ≤ Real.exp (t * yh) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < 2 * Δ * Real.exp 1 ^ 2 * M)]
    exact Real.exp_le_exp.mpr h1
  rw [le_div_iff₀ hK]
  have h3 : Real.exp (-t * yh) * Real.exp (t * yh) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-t * yh) := Real.exp_pos _
  nlinarith

/-! ## 5. Axiom check -/

#print axioms rarity_chernoff
#print axioms rarity_ennreal
#print axioms healing_deterministic
#print axioms healing_markov
#print axioms kp_threshold

end LargeFieldStep
