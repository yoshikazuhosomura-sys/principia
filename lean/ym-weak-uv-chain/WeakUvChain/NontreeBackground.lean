/-
Reduces premise 8 (background field in the tree gauge = estimate on the non-tree edges) to the type of premise 1
(quadratic remainder). Single file; checks with `import Mathlib` only. Starts with copies of ClassStepRemainder,
TreeGaugeLocality and RegularityStep (unchanged up to comments); the junction is NontreeBackground at the end.

  Premise 8, quadratic form: the background coordinates v_k on the non-tree edges in the tree gauge satisfy v_{k+1} = T_k v_k + R_k v_k
         per step, with ‖T_k w‖ ≤ τ‖w‖, ‖R_k w‖ ≤ C + a‖w‖² (the same type as premise 1; stated as a Prop)
  Premise 8, Lipschitz form: in the shift, ‖T w − T w′‖ ≤ τ‖w − w′‖, and ‖R w − R w′‖ ≤ L‖w − w′‖ in the closed ball r (Prop)
  §1 Premise 8 in quadratic form ⇒ the background enters the small closed ball C/(1 − (τ + a r)) (ClassStepRemainder.orbit_in_small_ball;
     the same fields hT, hquad as window_orbit_small of Assembly)
  §2 Premise 8 in Lipschitz form ⇒ the shifted backgrounds satisfy ‖v_k − v′_k‖ ≤ (τ + L)^k ‖v_0 − v′_0‖
  §3 Gauge-invariant quantities factor through the values on non-tree edges (from TreeGaugeLocality.invariant_depends_on_nontree)
  §4 Junction filling the field `d_i ≤ K r` of RegularityStep.pointwise_bound (on the small-field event) from §2
  The content of premise 8 (its quadratic and Lipschitz forms holding for four-dimensional backgrounds; the Lipschitz form in
  coordinates) remains (assumed).
-/
import Mathlib

/-! Copy of ClassStepRemainder (unchanged up to comments) -/
namespace ClassStepRemainder

open Filter Topology

/-! ## 1. A bounded two-sided infinite orbit lies in a small ball -/

/-- If a nonnegative sequence `n : ℤ → ℝ` satisfies `n (k+1) ≤ C + λ n k` (`0 ≤ λ < 1`, `C ≥ 0`) and `n k ≤ r` for all `k`,
then `n k ≤ C/(1−λ)` for all `k`. -/
theorem bounded_orbit_small (n : ℤ → ℝ) (C lam r : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) (hrec : ∀ k, n (k + 1) ≤ C + lam * n k) (hbd : ∀ k, n k ≤ r) :
    ∀ k, n k ≤ C / (1 - lam) := by
  intro k
  have h1 : 0 < 1 - lam := by linarith
  -- estimate going back j steps: n k ≤ C (1 − λ^j)/(1 − λ) + λ^j r
  have key : ∀ j : ℕ, n k ≤ C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r := by
    intro j
    induction j generalizing k with
    | zero =>
      simp only [pow_zero, sub_self, mul_zero, zero_div, one_mul, zero_add]
      exact hbd k
    | succ j ih =>
      have hk := hrec (k - 1)
      simp only [sub_add_cancel] at hk
      have ih' := ih (k - 1)
      have hlj : 0 ≤ lam ^ j := pow_nonneg hl0 j
      have e : C * (1 - lam ^ (j + 1)) / (1 - lam) + lam ^ (j + 1) * r =
          C + lam * (C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) := by
        field_simp; ring
      rw [e]
      calc n k ≤ C + lam * n (k - 1) := hk
        _ ≤ C + lam * (C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) := by
            have := mul_le_mul_of_nonneg_left ih' hl0; linarith
  have hlim : Tendsto (fun j : ℕ => C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) atTop
      (𝓝 (C * (1 - 0) / (1 - lam) + 0 * r)) := by
    have hp : Tendsto (fun j : ℕ => lam ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hl1
    exact ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)).div_const _).add
      (hp.mul tendsto_const_nhds)
  have := ge_of_tendsto hlim (Eventually.of_forall key)
  simpa using this

/-! ## 2. Norm recursion inside the ball from a quadratic-type remainder -/

section Step

variable {E : Type*} [NormedAddCommGroup E]

/-- If `‖T v‖ ≤ τ ‖v‖`, `‖R v‖ ≤ C + a ‖v‖²` and `‖v‖ ≤ r`, then `‖T v + R v‖ ≤ C + (τ + a r) ‖v‖`. -/
theorem norm_step_le (T R : E → E) (τ a C r : ℝ) (ha : 0 ≤ a)
    (hT : ∀ v, ‖T v‖ ≤ τ * ‖v‖) (hR : ∀ v, ‖R v‖ ≤ C + a * ‖v‖ ^ 2)
    (v : E) (hv : ‖v‖ ≤ r) : ‖T v + R v‖ ≤ C + (τ + a * r) * ‖v‖ := by
  have h1 := norm_add_le (T v) (R v)
  have h2 := hT v
  have h3 := hR v
  have h4 : a * ‖v‖ ^ 2 ≤ a * r * ‖v‖ := by
    have : ‖v‖ ^ 2 ≤ r * ‖v‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hv (norm_nonneg v)
    nlinarith
  nlinarith

/-- A two-sided infinite orbit `v (k+1) = T k (v k) + R k (v k)` staying in the class ball of radius `r` satisfies
`‖v k‖ ≤ C/(1−λ)` at every step, if `λ = τ + a r < 1`. -/
theorem orbit_in_small_ball (T R : ℤ → E → E) (v : ℤ → E) (τ a C r : ℝ)
    (hτ : 0 ≤ τ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hlt : τ + a * r < 1)
    (hT : ∀ k w, ‖T k w‖ ≤ τ * ‖w‖) (hR : ∀ k w, ‖R k w‖ ≤ C + a * ‖w‖ ^ 2)
    (horbit : ∀ k, v (k + 1) = T k (v k) + R k (v k)) (hball : ∀ k, ‖v k‖ ≤ r) :
    ∀ k, ‖v k‖ ≤ C / (1 - (τ + a * r)) := by
  apply bounded_orbit_small (fun k => ‖v k‖) C (τ + a * r) r (by positivity) hlt _ hball
  intro k
  show ‖v (k + 1)‖ ≤ C + (τ + a * r) * ‖v k‖
  rw [horbit k]
  exact norm_step_le (T k) (R k) τ a C r ha (hT k) (hR k) (v k) (hball k)

end Step

/-! ## 3. The coupling remainder read in the β coordinate -/

section Coupling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The component of the one-step remainder `Rf` (full-space valued) along the β coordinate `φ` (continuous linear) is the small-field
remainder of the coupling flow. If `‖Rf v‖ ≤ C + a ‖v‖²` and `‖v‖ ≤ ρ`, then `|φ (Rf v)| ≤ ‖φ‖ (C + a ρ²)`. -/
theorem coupling_remainder_le (φ : E →L[ℝ] ℝ) (Rf : E → E) (C a ρ : ℝ) (ha : 0 ≤ a)
    (hR : ∀ v, ‖Rf v‖ ≤ C + a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ ρ) :
    |φ (Rf v)| ≤ ‖φ‖ * (C + a * ρ ^ 2) := by
  have h1 : |φ (Rf v)| ≤ ‖φ‖ * ‖Rf v‖ := by
    have := φ.le_opNorm (Rf v); rwa [Real.norm_eq_abs] at this
  have h2 : ‖v‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have h3 : ‖Rf v‖ ≤ C + a * ρ ^ 2 := le_trans (hR v) (by nlinarith)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (norm_nonneg φ))

/-- §1–§3 combined: with source `C = c₀ / u` (`c₀ g²`, `g² = 1/u`) and `u ≥ u⋆ > 0`, the coupling remainder read at the radius
`ρ = C/(1 − λ)` of the orbit's small ball satisfies
`|r^s| ≤ ‖φ‖ c₀ (1 + a c₀ / ((1−λ)² u⋆)) / u` (the chain's `small_rem` form `C_s / u`). -/
theorem small_rem_form (φ : E →L[ℝ] ℝ) (Rf : E → E) (c₀ a lam u ustar : ℝ)
    (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hl1 : lam < 1) (hus : 0 < ustar) (hu : ustar ≤ u)
    (hR : ∀ v, ‖Rf v‖ ≤ c₀ / u + a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ (c₀ / u) / (1 - lam)) :
    |φ (Rf v)| ≤ (‖φ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * ustar))) / u := by
  have hu0 : 0 < u := lt_of_lt_of_le hus hu
  have hl : 0 < 1 - lam := by linarith
  have h := coupling_remainder_le φ Rf (c₀ / u) a ((c₀ / u) / (1 - lam)) ha hR v hv
  refine le_trans h ?_
  have e : ‖φ‖ * (c₀ / u + a * ((c₀ / u) / (1 - lam)) ^ 2) =
      (‖φ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * u))) / u := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hu0.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : a * c₀ / ((1 - lam) ^ 2 * u) ≤ a * c₀ / ((1 - lam) ^ 2 * ustar) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hu (by positivity))
  linarith

end Coupling

/-! ## 5. Axiom check -/

#print axioms bounded_orbit_small
#print axioms norm_step_le
#print axioms orbit_in_small_ball
#print axioms coupling_remainder_le
#print axioms small_rem_form

end ClassStepRemainder

/-! Copy of TreeGaugeLocality (unchanged up to comments) -/
namespace TreeGaugeLocality

variable {V E G : Type*} [DecidableEq V] [Group G]

/-- Recursion of the tree gauge (same definition as in TreeGauge, placed in this file). -/
noncomputable def treeGauge (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) : V → G
  | v => if h : v = r then 1 else treeGauge r parent depth hdepth U (parent v) * (U v)⁻¹
termination_by v => depth v
decreasing_by exact hdepth v h

theorem treeGauge_step (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) (v : V) (hv : v ≠ r) :
    treeGauge r parent depth hdepth U v =
      treeGauge r parent depth hdepth U (parent v) * (U v)⁻¹ := by
  rw [treeGauge]; simp [hv]

/-- Gauge action. -/
def act (src tgt : E → V) (g : V → G) (U : E → G) : E → G :=
  fun e => g (src e) * U e * (g (tgt e))⁻¹

/-- Tree gauge for each configuration `U`: uses the value on the tree edge `treeEdge v` as transport to the parent. -/
noncomputable def gfix (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v)
    (treeEdge : ∀ v : V, v ≠ r → E) (U : E → G) : V → G :=
  treeGauge r parent depth hdepth (fun v => if h : v = r then 1 else U (treeEdge v h))

/-- (i) The configuration transformed by the tree gauge is the identity on every tree edge. -/
theorem gfix_tree_edge (src tgt : E → V) (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v)
    (treeEdge : ∀ v : V, v ≠ r → E)
    (hsrc : ∀ v hv, src (treeEdge v hv) = v) (htgt : ∀ v hv, tgt (treeEdge v hv) = parent v)
    (U : E → G) (v : V) (hv : v ≠ r) :
    act src tgt (gfix r parent depth hdepth treeEdge U) U (treeEdge v hv) = 1 := by
  unfold act gfix
  rw [hsrc, htgt, treeGauge_step r parent depth hdepth _ v hv]
  simp only [hv, dite_false]
  group

/-- (ii) Locality of the background: a gauge-invariant `F` is determined by the values on non-tree edges in the tree gauge. -/
theorem invariant_depends_on_nontree (src tgt : E → V) (r : V) (parent : V → V)
    (depth : V → ℕ) (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v)
    (treeEdge : ∀ v : V, v ≠ r → E)
    (hsrc : ∀ v hv, src (treeEdge v hv) = v) (htgt : ∀ v hv, tgt (treeEdge v hv) = parent v)
    {R : Type*} (F : (E → G) → R) (hF : ∀ g U, F (act src tgt g U) = F U)
    (U U' : E → G)
    (hnon : ∀ e, (∀ v hv, treeEdge v hv ≠ e) →
      act src tgt (gfix r parent depth hdepth treeEdge U) U e =
        act src tgt (gfix r parent depth hdepth treeEdge U') U' e) :
    F U = F U' := by
  rw [← hF (gfix r parent depth hdepth treeEdge U) U,
    ← hF (gfix r parent depth hdepth treeEdge U') U']
  congr 1
  funext e
  by_cases h : ∃ v hv, treeEdge v hv = e
  · obtain ⟨v, hv, rfl⟩ := h
    rw [gfix_tree_edge src tgt r parent depth hdepth treeEdge hsrc htgt U v hv,
      gfix_tree_edge src tgt r parent depth hdepth treeEdge hsrc htgt U' v hv]
  · exact hnon e (fun v hv hve => h ⟨v, hv, hve⟩)

#print axioms treeGauge_step
#print axioms gfix_tree_edge
#print axioms invariant_depends_on_nontree

end TreeGaugeLocality

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

namespace NontreeBackground

open Filter Topology MeasureTheory

set_option linter.unusedSectionVars false

/-! ## 1. premise 8 in the type of premise 1 -/

section Quadratic

variable {F : Type*} [NormedAddCommGroup F]

/-- Premise 8 in quadratic form: the per-step map of the background coordinates on non-tree edges has the same quadratic type as premise 1. -/
def NontreeQuadraticType (T R : ℤ → F → F) (τ a C : ℝ) : Prop :=
  (∀ k w, ‖T k w‖ ≤ τ * ‖w‖) ∧ (∀ k w, ‖R k w‖ ≤ C + a * ‖w‖ ^ 2)

/-- Premise 8 in quadratic form ⇒ a background staying in the closed ball `r` enters the small closed ball. -/
theorem nontree_small_ball (T R : ℤ → F → F) (v : ℤ → F) (τ a C r : ℝ)
    (hτ : 0 ≤ τ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hlt : τ + a * r < 1)
    (H : NontreeQuadraticType T R τ a C)
    (horbit : ∀ k, v (k + 1) = T k (v k) + R k (v k)) (hball : ∀ k, ‖v k‖ ≤ r) :
    ∀ k, ‖v k‖ ≤ C / (1 - (τ + a * r)) :=
  ClassStepRemainder.orbit_in_small_ball T R v τ a C r hτ ha hr hlt H.1 H.2 horbit hball

/-- Form of the fields of `window_orbit_small` in Assembly: the two components of premise 8 in quadratic form become `hT` and `hquad` directly. -/
theorem quadratic_fields (T R : ℤ → F → F) (τ a C : ℝ) (H : NontreeQuadraticType T R τ a C) :
    (∀ k w, ‖T k w‖ ≤ τ * ‖w‖) ∧ (∀ k w, ‖R k w‖ ≤ C + a * ‖w‖ ^ 2) := H

end Quadratic

/-! ## 2. Difference of shifted backgrounds -/

section Shift

variable {F : Type*} [NormedAddCommGroup F]

/-- Premise 8 in Lipschitz form: contraction of the linear part and Lipschitz property of the remainder in the closed ball `r`. -/
def NontreeLipschitz (T R : ℕ → F → F) (τ L r : ℝ) : Prop :=
  (∀ k w w', ‖T k w - T k w'‖ ≤ τ * ‖w - w'‖) ∧
  (∀ k w w', ‖w‖ ≤ r → ‖w'‖ ≤ r → ‖R k w - R k w'‖ ≤ L * ‖w - w'‖)

/-- Premise 8 in Lipschitz form ⇒ `‖v_k − v′_k‖ ≤ (τ + L)^k ‖v_0 − v′_0‖`. -/
theorem shift_difference (T R : ℕ → F → F) (τ L r : ℝ) (hτL : 0 ≤ τ + L)
    (H : NontreeLipschitz T R τ L r) (v v' : ℕ → F)
    (hv : ∀ k, v (k + 1) = T k (v k) + R k (v k)) (hv' : ∀ k, v' (k + 1) = T k (v' k) + R k (v' k))
    (hb : ∀ k, ‖v k‖ ≤ r) (hb' : ∀ k, ‖v' k‖ ≤ r) :
    ∀ k, ‖v k - v' k‖ ≤ (τ + L) ^ k * ‖v 0 - v' 0‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hv k, hv' k]
    have e : T k (v k) + R k (v k) - (T k (v' k) + R k (v' k)) =
        (T k (v k) - T k (v' k)) + (R k (v k) - R k (v' k)) := by abel
    rw [e]
    calc ‖(T k (v k) - T k (v' k)) + (R k (v k) - R k (v' k))‖
        ≤ ‖T k (v k) - T k (v' k)‖ + ‖R k (v k) - R k (v' k)‖ := norm_add_le _ _
      _ ≤ τ * ‖v k - v' k‖ + L * ‖v k - v' k‖ :=
          add_le_add (H.1 k _ _) (H.2 k _ _ (hb k) (hb' k))
      _ = (τ + L) * ‖v k - v' k‖ := by ring
      _ ≤ (τ + L) * ((τ + L) ^ k * ‖v 0 - v' 0‖) := mul_le_mul_of_nonneg_left ih hτL
      _ = (τ + L) ^ (k + 1) * ‖v 0 - v' 0‖ := by ring

/-- If `τ + L ≤ 1`, the difference is at most the initial shift. -/
theorem shift_stays (T R : ℕ → F → F) (τ L r : ℝ) (hτL : 0 ≤ τ + L) (hle : τ + L ≤ 1)
    (H : NontreeLipschitz T R τ L r) (v v' : ℕ → F)
    (hv : ∀ k, v (k + 1) = T k (v k) + R k (v k)) (hv' : ∀ k, v' (k + 1) = T k (v' k) + R k (v' k))
    (hb : ∀ k, ‖v k‖ ≤ r) (hb' : ∀ k, ‖v' k‖ ≤ r) :
    ∀ k, ‖v k - v' k‖ ≤ ‖v 0 - v' 0‖ := by
  intro k
  have h := shift_difference T R τ L r hτL H v v' hv hv' hb hb' k
  have hp : (τ + L) ^ k ≤ 1 := pow_le_one₀ hτL hle
  calc ‖v k - v' k‖ ≤ (τ + L) ^ k * ‖v 0 - v' 0‖ := h
    _ ≤ 1 * ‖v 0 - v' 0‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ‖v 0 - v' 0‖ := one_mul _

end Shift

/-! ## 3. Gauge-invariant quantities factor through the non-tree edges -/

section Gauge

variable {V E G : Type*} [DecidableEq V] [Group G]

/-- Values on the non-tree edges in the tree gauge. -/
noncomputable def nontreePart (src tgt : E → V) (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (treeEdge : ∀ v : V, v ≠ r → E)
    (U : E → G) : {e : E // ∀ v hv, treeEdge v hv ≠ e} → G :=
  fun e => TreeGaugeLocality.act src tgt
    (TreeGaugeLocality.gfix r parent depth hdepth treeEdge U) U e.1

/-- A gauge-invariant `F` factors through `nontreePart`: `F = F̃ ∘ nontreePart`. -/
theorem invariant_factors (src tgt : E → V) (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (treeEdge : ∀ v : V, v ≠ r → E)
    (hsrc : ∀ v hv, src (treeEdge v hv) = v) (htgt : ∀ v hv, tgt (treeEdge v hv) = parent v)
    {Rv : Type*} [Nonempty Rv] (F : (E → G) → Rv)
    (hF : ∀ g U, F (TreeGaugeLocality.act src tgt g U) = F U) :
    ∃ Ft : ({e : E // ∀ v hv, treeEdge v hv ≠ e} → G) → Rv,
      ∀ U, F U = Ft (nontreePart src tgt r parent depth hdepth treeEdge U) := by
  have hfac : Function.FactorsThrough F (nontreePart src tgt r parent depth hdepth treeEdge) := by
    intro U U' h
    apply TreeGaugeLocality.invariant_depends_on_nontree src tgt r parent depth hdepth treeEdge
      hsrc htgt F hF U U'
    intro e he
    exact congrFun h ⟨e, he⟩
  exact ⟨Function.extend (nontreePart src tgt r parent depth hdepth treeEdge) F
    (fun _ => Classical.arbitrary Rv), fun U => (hfac.extend_apply _ U).symm⟩

end Gauge

/-! ## 4. Filling the field `d_i ≤ K r` of RegularityStep -/

section Regularity

variable {Ω F ι : Type*} [NormedAddCommGroup F] [DecidableEq ι]

/-- Junction: if, on the small-field event `G`, the background coordinates of each block variable `i` are orbits of the
map of premise 8 in Lipschitz form (before the shift `v ω i`, after the shift `v' ω i`, read at step `k₀`) and the initial shift is ≤ K r, then the
hypothesis `dist (V i ω) (V' i ω) ≤ K r` of RegularityStep.pointwise_bound holds and the pointwise estimate follows. -/
theorem pointwise_from_nontree (I : Finset ι) (f : ι → F → ℝ) (Lf : ι → ℝ) (hL : ∀ i, 0 ≤ Lf i)
    (hf : ∀ i e, |f i e| ≤ 1) (hLip : ∀ i e e', |f i e - f i e'| ≤ Lf i * dist e e')
    (T R : ℕ → F → F) (τ L r : ℝ) (hτL : 0 ≤ τ + L) (hle : τ + L ≤ 1)
    (H : NontreeLipschitz T R τ L r)
    (v v' : Ω → ι → ℕ → F) (k₀ : ℕ) (G : Set Ω) (K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hv : ∀ ω i k, v ω i (k + 1) = T k (v ω i k) + R k (v ω i k))
    (hv' : ∀ ω i k, v' ω i (k + 1) = T k (v' ω i k) + R k (v' ω i k))
    (hb : ∀ ω ∈ G, ∀ i ∈ I, ∀ k, ‖v ω i k‖ ≤ r) (hb' : ∀ ω ∈ G, ∀ i ∈ I, ∀ k, ‖v' ω i k‖ ≤ r)
    (hinit : ∀ ω ∈ G, ∀ i ∈ I, ‖v ω i 0 - v' ω i 0‖ ≤ K * s) (ω : Ω) :
    |∏ i ∈ I, f i (v ω i k₀) - ∏ i ∈ I, f i (v' ω i k₀)| ≤
      (∑ i ∈ I, Lf i) * (K * s) + 2 * I.card * Gᶜ.indicator 1 ω := by
  apply RegularityStep.pointwise_bound I f Lf hL hf hLip (fun i ω => v ω i k₀)
    (fun i ω => v' ω i k₀) G K s hK hs
  intro ω' hω' i hi
  rw [dist_eq_norm]
  exact le_trans (shift_stays T R τ L r hτL hle H (v ω' i) (v' ω' i) (hv ω' i) (hv' ω' i)
    (hb ω' hω' i hi) (hb' ω' hω' i hi) k₀) (hinit ω' hω' i hi)

end Regularity

#print axioms nontree_small_ball
#print axioms quadratic_fields
#print axioms shift_difference
#print axioms shift_stays
#print axioms invariant_factors
#print axioms pointwise_from_nontree

end NontreeBackground
