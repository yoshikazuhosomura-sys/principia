/-
One-step inequality for premise 7 (the splitting of (H-reg)). Single file; checks with `import Mathlib` only.

  §1 Difference of products: if |a_i|, |b_i| ≤ 1, then |Π a_i − Π b_i| ≤ Σ |a_i − b_i|.
  §2 Pointwise bound: for observables F_i (|F_i| ≤ 1, L_i-Lipschitz), if the distance d_i between block variables
     before and after the shift satisfies d_i ≤ K|δ| on the small-field event G, then
     |Π F_i(V_i) − Π F_i(V_i′)| ≤ Σ_i L_i K |δ| + 2|I| 1_{Gᶜ}.
  §3 Expectation: |E Π F_i(V_i) − E Π F_i(V_i′)| ≤ (Σ L_i) K |δ| + 2|I| μ(Gᶜ).
  §4 Equicontinuity: if for every η > 0 there is a small-field event with μ(Gᶜ) ≤ η uniformly in the lattice, and a
     Lipschitz constant K(η) on it, then equicontinuity in the shift follows (the equicontinuous form of Theorem W).
  The geometric decay in ω of the free field (the part decorrelating at the lattice spacing) is on the
  floating-point computation side.
-/
import Mathlib

namespace RegularityStep

open MeasureTheory Finset Filter Topology

/-! ## 1. Difference of products -/

theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have ha' : ∀ i ∈ s, |a i| ≤ 1 := fun i hi => ha i (mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ 1 := fun i hi => hb i (mem_insert_of_mem hi)
    have hPa : |∏ i ∈ s, a i| ≤ 1 := by
      rw [abs_prod]; exact prod_le_one (fun i _ => abs_nonneg _) ha'
    have hbj : |b j| ≤ 1 := hb j (mem_insert_self j s)
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        (a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    calc |(a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)|
        ≤ |(a j - b j) * ∏ i ∈ s, a i| + |b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := abs_add_le _ _
      _ = |a j - b j| * |∏ i ∈ s, a i| + |b j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          rw [abs_mul, abs_mul]
      _ ≤ |a j - b j| * 1 + 1 * ∑ i ∈ s, |a i - b i| := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hPa (abs_nonneg _)
          · exact mul_le_mul hbj (ih ha' hb') (abs_nonneg _) zero_le_one
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

/-! ## 2. Pointwise estimate -/

/-- Pointwise: `|F_i| ≤ 1`, `F_i` is `L_i`-Lipschitz, and `d_i(ω) ≤ K r` for `ω ∈ G` (`K, r ≥ 0`). -/
theorem pointwise_bound {Ω E ι : Type*} [PseudoMetricSpace E] [DecidableEq ι] (I : Finset ι)
    (F : ι → E → ℝ) (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i) (hF : ∀ i e, |F i e| ≤ 1)
    (hLip : ∀ i e e', |F i e - F i e'| ≤ L i * dist e e')
    (V V' : ι → Ω → E) (G : Set Ω) (K r : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hG : ∀ ω ∈ G, ∀ i ∈ I, dist (V i ω) (V' i ω) ≤ K * r) (ω : Ω) :
    |∏ i ∈ I, F i (V i ω) - ∏ i ∈ I, F i (V' i ω)| ≤
      (∑ i ∈ I, L i) * (K * r) + 2 * I.card * Gᶜ.indicator 1 ω := by
  have h1 := abs_prod_sub_prod_le I (fun i => F i (V i ω)) (fun i => F i (V' i ω))
    (fun i _ => hF i _) (fun i _ => hF i _)
  refine le_trans h1 ?_
  have hS : 0 ≤ (∑ i ∈ I, L i) * (K * r) :=
    mul_nonneg (sum_nonneg fun i _ => hL i) (mul_nonneg hK hr)
  by_cases hω : ω ∈ G
  · have : Gᶜ.indicator (1 : Ω → ℝ) ω = 0 := Set.indicator_of_notMem (by simpa using hω) _
    rw [this, mul_zero, add_zero, sum_mul]
    exact sum_le_sum fun i hi => le_trans (hLip i _ _)
      (mul_le_mul_of_nonneg_left (hG ω hω i hi) (hL i))
  · have : Gᶜ.indicator (1 : Ω → ℝ) ω = 1 := Set.indicator_of_mem (by simpa using hω) _
    rw [this, mul_one]
    have h2 : ∑ i ∈ I, |F i (V i ω) - F i (V' i ω)| ≤ ∑ _i ∈ I, (2 : ℝ) := by
      apply sum_le_sum; intro i _
      have := hF i (V i ω); have := hF i (V' i ω)
      calc |F i (V i ω) - F i (V' i ω)| ≤ |F i (V i ω)| + |F i (V' i ω)| := abs_sub _ _
        _ ≤ 2 := by linarith
    rw [sum_const, nsmul_eq_mul] at h2
    linarith

/-! ## 3. Expectations -/

theorem expectation_bound {Ω E ι : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Finset ι)
    (F : ι → E → ℝ) (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i) (hF : ∀ i e, |F i e| ≤ 1)
    (hLip : ∀ i e e', |F i e - F i e'| ≤ L i * dist e e')
    (V V' : ι → Ω → E) (G : Set Ω) (hGm : MeasurableSet G) (K r : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hG : ∀ ω ∈ G, ∀ i ∈ I, dist (V i ω) (V' i ω) ≤ K * r)
    (hi1 : Integrable (fun ω => ∏ i ∈ I, F i (V i ω)) μ)
    (hi2 : Integrable (fun ω => ∏ i ∈ I, F i (V' i ω)) μ) :
    |∫ ω, ∏ i ∈ I, F i (V i ω) ∂μ - ∫ ω, ∏ i ∈ I, F i (V' i ω) ∂μ| ≤
      (∑ i ∈ I, L i) * (K * r) + 2 * I.card * μ.real Gᶜ := by
  rw [← integral_sub hi1 hi2]
  have hind : Integrable (Gᶜ.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hGm.compl
  have hrhs : Integrable (fun ω => (∑ i ∈ I, L i) * (K * r) + 2 * I.card * Gᶜ.indicator 1 ω) μ :=
    (integrable_const _).add (hind.const_mul _)
  refine le_trans abs_integral_le_integral_abs ?_
  refine le_trans (integral_mono (hi1.sub hi2).abs hrhs fun ω =>
    pointwise_bound I F L hL hF hLip V V' G K r hK hr hG ω) ?_
  rw [integral_add (integrable_const _) (hind.const_mul _), integral_const, integral_const_mul]
  have : ∫ ω, Gᶜ.indicator (1 : Ω → ℝ) ω ∂μ = μ.real Gᶜ := by
    have e : (Gᶜ.indicator (1 : Ω → ℝ)) = Gᶜ.indicator (fun _ => (1 : ℝ)) := rfl
    rw [e, integral_indicator_const _ hGm.compl, smul_eq_mul, mul_one]
  rw [this]
  simp [Measure.real]

/-! ## 4. Equicontinuity -/

/-- If for every `η > 0` there is a small-field event uniform in the lattice `n` (`μ_n(Gᶜ) ≤ η`) with a Lipschitz
constant `K(η)` for the shift on it, and `|s_n(x) − s_n(x′)| ≤ τ_n + C K(η) r + 2N η` holds (`τ_n → 0` is the UV part
that decorrelates at the lattice spacing; about a factor 0.75 per step for the free field), then the equicontinuity
form of Theorem W follows. -/
theorem equicontinuous_of_small_field {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (s : ℕ → X → ℝ) (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (nhds 0)) (C N : ℝ) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hstep : ∀ η > 0, ∃ K ≥ 0, ∀ n, ∀ d ∈ D, ∀ d' ∈ D,
      |s n d - s n d'| ≤ τ n + C * K * dist d d' + 2 * N * η) :
    ∀ ε > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ ε := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := hstep (ε / (6 * (N + 1))) (by positivity)
  refine ⟨ε / (3 * (C * K + 1)), by positivity, fun d hd d' hd' hdd => ?_⟩
  have hev : ∀ᶠ n in atTop, τ n ≤ ε / 3 :=
    (hτ.eventually (Iic_mem_nhds (by positivity : (0:ℝ) < ε / 3))).mono fun n hn => hn
  refine hev.mono fun n hn => ?_
  have h := hb n d hd d' hd'
  have hCK : 0 ≤ C * K := mul_nonneg hC hK
  have h1 : C * K * dist d d' ≤ ε / 3 := by
    have hpos : 0 < 3 * (C * K + 1) := by positivity
    have : dist d d' * (3 * (C * K + 1)) < ε := by rwa [lt_div_iff₀ hpos] at hdd
    nlinarith [dist_nonneg (x := d) (y := d')]
  have h2 : 2 * N * (ε / (6 * (N + 1))) ≤ ε / 3 := by
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

#print axioms abs_prod_sub_prod_le
#print axioms pointwise_bound
#print axioms expectation_bound
#print axioms equicontinuous_of_small_field

end RegularityStep
