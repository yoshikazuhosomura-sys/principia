/-
States (H-gap) λ_min(θ) ≥ λ₀(1 − θ/θ_c) as a Prop, checks by arithmetic that the linear lower bound holds at each
point of the table of λ_min (8⁴, units β = 1, (floating-point computation)), and feeds K_bg(θ) = K₀/(1 − θ/θ_c)
into the equicontinuity of RegularityStep.
Single file; checks with `import Mathlib` only. Contains copies of RegularityStep and CThetaReadings (unchanged up to comments).

  §1 The (H-gap) Prop and pointwise checks of the table (flux ε = 0.2: one plane, 01+02, 01+02+03, six components,
     self-dual, non-abelian, complex η = 0.3; cov, mixed t = 0.6, straight line). θ_c is the zero of the linear
     interpolation for each type (tabulated value)
  §2 From the per-type bounds, a uniform bound in the background invariant f₁: λ_min ≥ λ₀(1 − f₁/0.679)
     (the smallest endpoint of f₁ is the self-dual 0.679)
  §3 If f₁ ≤ 0.4 then λ_min ≥ 0.41 λ₀
  §4 Equicontinuity with K(η) replaced by K_bg(θ(η)) (equicontinuous_from_gap)
  The shape between table points (concavity) is (reading); nothing is shown off the points.
  The non-abelian background is not a critical point.
-/
import Mathlib

/-! Copy of RegularityStep (unchanged up to comments) -/
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

/-! Copy of CThetaReadings (unchanged up to comments) -/
namespace CThetaReadings

/-- (A): C_θ = 1/θ_c ≥ 1.19 > 0.0725 when θ_c ≤ 0.84. -/
theorem hessian_reading_fails (θc : ℝ) (h0 : 0 < θc) (h : θc ≤ 0.84) :
    (0.0725 : ℝ) < 1 / θc := by
  rw [lt_div_iff₀ h0]; nlinarith

/-- (A): r = θ/θ_c ≤ 0.029 requires θ ≤ 0.029 θ_c ≤ 0.0244, below the clover median 0.138. -/
theorem hessian_reading_theta_max (θ θc : ℝ) (h0 : 0 < θc) (h : θc ≤ 0.84)
    (hr : θ / θc ≤ 0.029) : θ ≤ 0.0244 ∧ θ < 0.138 := by
  have : θ ≤ 0.029 * θc := by rwa [div_le_iff₀ h0] at hr
  constructor <;> nlinarith

/-- (B): at θ = 0.4, N₆ ≤ 2.17 gives N₆ θ²/12 ≤ 0.029. -/
theorem coefficient_reading_04 (N6 : ℝ) (h : N6 ≤ 2.17) :
    N6 * 0.4 ^ 2 / 12 ≤ (0.029 : ℝ) := by
  have : N6 * 0.4 ^ 2 / 12 ≤ 2.17 * 0.4 ^ 2 / 12 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right h (by norm_num)
  linarith [show (2.17 : ℝ) * 0.4 ^ 2 / 12 ≤ 0.029 by norm_num]

/-- (B): at θ = 0.68 (edge of analyticity), N₆ ≥ 1 gives N₆ θ²/12 > 0.029. -/
theorem coefficient_reading_068 (N6 : ℝ) (h : 1 ≤ N6) : (0.029 : ℝ) < N6 * 0.68 ^ 2 / 12 := by
  have : (1 : ℝ) * 0.68 ^ 2 / 12 ≤ N6 * 0.68 ^ 2 / 12 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right h (by norm_num)
  linarith [show (0.029 : ℝ) < 1 * 0.68 ^ 2 / 12 by norm_num]

/-- (A′): from the Hessian lower bound `λ_min(θ) ≥ λ₀(1 − θ/θ_c)` and `λ_min ‖x‖ ≤ ‖b‖`, get `‖x‖ ≤ ‖b‖/(λ₀(1 − θ/θ_c))`. -/
theorem minimizer_lipschitz (lam lam0 θ θc x b : ℝ) (hl0 : 0 < lam0) (hθc : 0 < θc) (hθ : θ < θc)
    (hlam : lam0 * (1 - θ / θc) ≤ lam) (hx : 0 ≤ x) (h : lam * x ≤ b) :
    x ≤ b / (lam0 * (1 - θ / θc)) := by
  have h1 : 0 < 1 - θ / θc := by rw [sub_pos, div_lt_one hθc]; exact hθ
  have h2 : 0 < lam0 * (1 - θ / θc) := mul_pos hl0 h1
  rw [le_div_iff₀ h2]
  nlinarith

/-- (A′): K_bg(θ) = K₀/(1 − θ/θ_c) is monotone for θ ≤ θ′ < θ_c. -/
theorem K_bg_mono (K0 θ θ' θc : ℝ) (hK : 0 ≤ K0) (hθc : 0 < θc) (h : θ ≤ θ') (h' : θ' < θc) :
    K0 / (1 - θ / θc) ≤ K0 / (1 - θ' / θc) := by
  have h1 : 0 < 1 - θ' / θc := by rw [sub_pos, div_lt_one hθc]; exact h'
  apply div_le_div_of_nonneg_left hK h1
  have : θ / θc ≤ θ' / θc := div_le_div_of_nonneg_right h hθc.le
  linarith

/-- (A′): K_bg ≤ 2.43 K₀ at θ = 0.4, θ_c = 0.68. -/
theorem K_bg_value (K0 : ℝ) (hK : 0 ≤ K0) : K0 / (1 - 0.4 / 0.68) ≤ 2.43 * K0 := by
  have e : K0 / (1 - 0.4 / 0.68) = (0.68 / 0.28) * K0 := by field_simp; ring
  rw [e]
  have : (0.68 / 0.28 : ℝ) ≤ 2.43 := by norm_num
  nlinarith

#print axioms hessian_reading_fails
#print axioms hessian_reading_theta_max
#print axioms coefficient_reading_04
#print axioms coefficient_reading_068
#print axioms minimizer_lipschitz
#print axioms K_bg_mono
#print axioms K_bg_value

end CThetaReadings

namespace HessianGap

open Filter Topology

/-! ## 1. (H-gap) and the table points -/

/-- (H-gap): `λ_min(θ) ≥ λ₀(1 − θ/θ_c)` for `0 ≤ θ < θ_c`. -/
def HGap (lmin : ℝ → ℝ) (lam0 θc : ℝ) : Prop :=
  ∀ θ, 0 ≤ θ → θ < θc → lam0 * (1 - θ / θc) ≤ lmin θ

/-- One point of the linear lower bound: `λ₀(1 − θ/θ_c) ≤ λ`. -/
def PointOK (lam0 θc θ lam : ℝ) : Prop := lam0 * (1 - θ / θc) ≤ lam

/-- Flux ε = 0.2, one plane (λ₀ = 0.500, θ_c = 0.724): values 0.245, 0.183, 0.108 at θ = 0.491, 0.589, 0.687. -/
theorem flux_one_plane :
    PointOK 0.5 0.724 0.491 0.245 ∧ PointOK 0.5 0.724 0.589 0.183 ∧ PointOK 0.5 0.724 0.687 0.108 := by
  unfold PointOK; norm_num

/-- 01+02 (θ_c = 0.529): values 0.196, 0.050 at θ = 0.393, 0.491. -/
theorem flux_two_planes : PointOK 0.5 0.529 0.393 0.196 ∧ PointOK 0.5 0.529 0.491 0.050 := by
  unfold PointOK; norm_num

/-- 01+02+03 (θ_c = 0.431): values 0.251, 0.084 at θ = 0.295, 0.393. -/
theorem flux_three_planes : PointOK 0.5 0.431 0.295 0.251 ∧ PointOK 0.5 0.431 0.393 0.084 := by
  unfold PointOK; norm_num

/-- Six components (θ_c = 0.348): values 0.337, 0.125 at θ = 0.196, 0.295. -/
theorem flux_six : PointOK 0.5 0.348 0.196 0.337 ∧ PointOK 0.5 0.348 0.295 0.125 := by
  unfold PointOK; norm_num

/-- Self-dual / anti-self-dual (θ_c = 0.679): value 0.114 at θ = 0.589. -/
theorem flux_self_dual : PointOK 0.5 0.679 0.589 0.114 := by unfold PointOK; norm_num

/-- Non-abelian, uniform (θ_c ≈ 0.78, not a critical point): value 0.103 at plaquette angle 0.649. -/
theorem flux_nonabelian : PointOK 0.5 0.78 0.649 0.103 := by unfold PointOK; norm_num

/-- Complex η = 0.3, one plane (λ₀ = 0.401, θ_c borrowed from η = 0, 0.724): value 0.090 at θ = 0.589. -/
theorem flux_complex : PointOK 0.401 0.724 0.589 0.090 := by unfold PointOK; norm_num

/-- cov (λ₀ = 0.500, θ_c = 0.645): values 0.353, 0.295, 0.149 at θ = 0.393, 0.491, 0.589. -/
theorem cov_points :
    PointOK 0.5 0.645 0.393 0.353 ∧ PointOK 0.5 0.645 0.491 0.295 ∧ PointOK 0.5 0.645 0.589 0.149 := by
  unfold PointOK; norm_num

/-- Mixed t = 0.6 (λ₀ = 0.389, θ_c = 0.556): values 0.271, 0.201, 0.125, 0.052 at θ = 0.196, 0.295, 0.393, 0.491
(margins 0.007 to 0.019, nearly linear). -/
theorem mix06_points :
    PointOK 0.389 0.556 0.196 0.271 ∧ PointOK 0.389 0.556 0.295 0.201 ∧
    PointOK 0.389 0.556 0.393 0.125 ∧ PointOK 0.389 0.556 0.491 0.052 := by
  unfold PointOK; norm_num

/-- Straight line (λ₀ = 0.177, θ_c = 0.31): value 0.074 at θ = 0.196. -/
theorem straight_point : PointOK 0.177 0.31 0.196 0.074 := by unfold PointOK; norm_num

/-! ## 2. Uniform bound in the background invariant f₁ -/

/-- From the type bound `λ₀(1 − θ/θ_c)`, `f₁ = κθ` and the type's f₁ endpoint `κθ_c ≥ f⋆`:
`λ₀(1 − f₁/f⋆) ≤ λ₀(1 − θ/θ_c)`. -/
theorem uniform_in_f1 (lam0 κ θ θc fstar : ℝ) (hl : 0 ≤ lam0) (hθ : 0 ≤ θ)
    (hθc : 0 < θc) (hf : 0 < fstar) (hedge : fstar ≤ κ * θc) :
    lam0 * (1 - κ * θ / fstar) ≤ lam0 * (1 - θ / θc) := by
  apply mul_le_mul_of_nonneg_left _ hl
  have h1 : θ / θc ≤ κ * θ / fstar := by
    rw [div_le_div_iff₀ hθc hf]
    nlinarith
  linarith

/-- The f₁ endpoints (κθ_c) of all types are ≥ 0.679: one plane 0.724, 01+02 √2·0.529 ≥ 0.748,
01+02+03 √3·0.431 ≥ 0.746, six components 2.414·0.348 = 0.840, self-dual 0.679. -/
theorem f1_edges :
    (0.679 : ℝ) ≤ 1 * 0.724 ∧ (0.679 : ℝ) ≤ 1.414 * 0.529 ∧ (0.679 : ℝ) ≤ 1.732 * 0.431 ∧
    (0.679 : ℝ) ≤ 2.414 * 0.348 ∧ (0.679 : ℝ) ≤ 1 * 0.679 := by norm_num

/-! ## 3. f₁ ≤ 0.4 -/

theorem gap_at_04 (lam0 f1 : ℝ) (hl : 0 ≤ lam0) (hf : f1 ≤ 0.4) :
    0.41 * lam0 ≤ lam0 * (1 - f1 / 0.679) := by
  have : f1 / 0.679 ≤ 0.4 / 0.679 := div_le_div_of_nonneg_right hf (by norm_num)
  have h2 : (0.41 : ℝ) ≤ 1 - 0.4 / 0.679 := by norm_num
  nlinarith

/-! ## 4. Equicontinuity with K_bg -/

/-- K_bg(θ) = K₀/(1 − θ/θ_c) is nonnegative for `0 ≤ θ < θ_c`, `K₀ ≥ 0`. -/
theorem K_bg_nonneg (K0 θ θc : ℝ) (hK : 0 ≤ K0) (hθc : 0 < θc) (h : θ < θc) :
    0 ≤ K0 / (1 - θ / θc) := by
  have : 0 < 1 - θ / θc := by rw [sub_pos, div_lt_one hθc]; exact h
  positivity

/-- If for each η > 0 the background-invariant threshold satisfies θ(η) < θ_c and
`|s_n(d) − s_n(d′)| ≤ τ_n + C·K_bg(θ(η))·dist + 2Nη`, then the equicontinuity form of Theorem W holds. -/
theorem equicontinuous_from_gap {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (s : ℕ → X → ℝ) (τn : ℕ → ℝ) (hτ : Tendsto τn atTop (nhds 0)) (C N : ℝ) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (K0 θc : ℝ) (hK : 0 ≤ K0) (hθc : 0 < θc) (θη : ℝ → ℝ)
    (hθ : ∀ η > 0, θη η < θc)
    (hstep : ∀ η > 0, ∀ n, ∀ d ∈ D, ∀ d' ∈ D,
      |s n d - s n d'| ≤ τn n + C * (K0 / (1 - θη η / θc)) * dist d d' + 2 * N * η) :
    ∀ ε > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ ε :=
  RegularityStep.equicontinuous_of_small_field D s τn hτ C N hC hN fun η hη =>
    ⟨K0 / (1 - θη η / θc), K_bg_nonneg K0 (θη η) θc hK hθc (hθ η hη), hstep η hη⟩

/-- Uniform form: if θ(η) ≤ 0.4 and θ_c = 0.679 then K_bg ≤ K₀/0.41 (independent of η). -/
theorem K_bg_uniform (K0 θ : ℝ) (hK : 0 ≤ K0) (hθ : θ ≤ 0.4) :
    K0 / (1 - θ / 0.679) ≤ K0 / 0.41 := by
  have h1 : (0.41 : ℝ) ≤ 1 - θ / 0.679 := by
    have : θ / 0.679 ≤ 0.4 / 0.679 := div_le_div_of_nonneg_right hθ (by norm_num)
    have h2 : (0.41 : ℝ) ≤ 1 - 0.4 / 0.679 := by norm_num
    linarith
  exact div_le_div_of_nonneg_left hK (by norm_num) h1

#print axioms flux_one_plane
#print axioms flux_two_planes
#print axioms flux_three_planes
#print axioms flux_six
#print axioms flux_self_dual
#print axioms flux_nonabelian
#print axioms flux_complex
#print axioms cov_points
#print axioms mix06_points
#print axioms straight_point
#print axioms uniform_in_f1
#print axioms f1_edges
#print axioms gap_at_04
#print axioms K_bg_nonneg
#print axioms equicontinuous_from_gap
#print axioms K_bg_uniform

end HessianGap
