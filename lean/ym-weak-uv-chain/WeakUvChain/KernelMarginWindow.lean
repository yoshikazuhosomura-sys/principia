/-
Feeds the factor-2 margin at the window numbers for β = 33, 36, 38 into the margin field of the ker φ version of the
small_rem chain. Single file; checks with `import Mathlib` only. Starts with a copy of KernelMarginNumbers (which
contains copies of SmallRemKernel and MarginRatioTwo; unchanged up to comments), with KernelMarginWindow added at the end.

  u⋆ = β/4 = 8.25, 9, 9.5. τ = 0.6953 and a = 4.3348 are kept at their β = 28 values (floating-point computation)
  (per-β values not cross-checked).
  c₀ = 0.022: the closed-ball condition holds (u ≥ 5.48); the remaining bound on DZ is 0.0053 (β = 33), 0.0057 (36),
  0.0059 (38).
  c₀ = 0.04: for β = 33 to 38 the closed-ball condition fails (u ≥ 9.97 is needed) and the margin fails even with DZ = 0.
  The estimate of DZ (D ≈ βy_h/6 (assumed), Z = 96P₁(y_h) (floating-point computation)) is floating-point arithmetic
  and is not formalised here.
-/
import Mathlib

/-! Copy of SmallRemKernel (unchanged up to comments) -/
namespace SmallRemKernel

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 0. Copy of UltravioletChain (unchanged up to comments) -/

namespace UltravioletChain

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 1. (H-β): from the small-field step and the large-field step -/

/-- Per-step premises (for each bare inverse coupling `x`). `u k x` is the inverse coupling after `k` steps, `z k x` the large-field
activity, `w k x` the large-field supply generated at that step, `rs`, `rl` the small-field and large-field remainders of the coupling flow.
All fields are imposed only inside the domain (`u⋆ ≤ u` at all previous steps). -/
structure CouplingSteps (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ)
    (b C D ρ A B Z ustar : ℝ) : Prop where
  ustar_pos : 0 < ustar
  hb : 0 < b
  hC : 0 ≤ C
  hD : 0 ≤ D
  hρ : 0 ≤ ρ
  hA : 0 ≤ A
  hB : 0 ≤ B
  /-- S_k: one coupling step (leading flow term `b` and two remainders) -/
  flow : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → u (k + 1) x = u k x - b + rs k x + rl k x
  /-- S_k: small-field remainder `|r^s| ≤ C g²` -/
  small_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rs k x| ≤ C / u k x
  /-- L_k: supply from the large-field gas to the coupling -/
  large_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rl k x| ≤ D * z k x
  /-- L_k: activity recursion -/
  act_rec : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
    z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2
  act_nonneg : ∀ k x, 0 ≤ z k x
  act_init : ∀ x, z 0 x ≤ Z
  /-- L_k: rarity (the supply is larger for stronger coupling; `Φ` is decreasing on the domain) -/
  supply : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → w k x ≤ Φ (u k x)
  supply_anti : ∀ s t, ustar ≤ s → s ≤ t → Φ t ≤ Φ s
  /-- Invariant interval: even with the supply at the worst coupling `u⋆`, the activity stays ≤ `Z` -/
  fix : ρ * Z + A * Φ ustar + B * Z ^ 2 ≤ Z
  /-- Margin: the sum of the remainders is at most half the flow -/
  margin : C / ustar + D * Z ≤ b / 2

/-- Inside the domain the activity stays ≤ `Z`. -/
theorem activity_le {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    (H : CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → z k x ≤ Z := by
  intro k
  induction k with
  | zero => intro x _; exact H.act_init x
  | succ k ih =>
    intro x hdom
    have hdom' : ∀ j ≤ k, ustar ≤ u j x := fun j hj => hdom j (by omega)
    have hz := ih x hdom'
    have hw : w k x ≤ Φ ustar :=
      le_trans (H.supply k x hdom') (H.supply_anti _ _ le_rfl (hdom' k le_rfl))
    have h1 : ρ * z k x ≤ ρ * Z := mul_le_mul_of_nonneg_left hz H.hρ
    have h2 : A * w k x ≤ A * Φ ustar := mul_le_mul_of_nonneg_left hw H.hA
    have h3 : z k x ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (H.act_nonneg k x) hz 2
    have h4 : B * z k x ^ 2 ≤ B * Z ^ 2 := mul_le_mul_of_nonneg_left h3 H.hB
    linarith [H.act_rec k x hdom', H.fix]

/-- The (H-β) form: inside the domain `u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2`. -/
theorem hbeta_of_steps {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    (H : CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2 := by
  intro k x hdom
  have hu : ustar ≤ u k x := hdom k le_rfl
  have hz := activity_le H k x hdom
  have hdiv : C / u k x ≤ C / ustar := div_le_div_of_nonneg_left H.hC H.ustar_pos hu
  have hDz : D * z k x ≤ D * Z := mul_le_mul_of_nonneg_left hz H.hD
  have hs := abs_le.mp (le_trans (H.small_rem k x hdom) hdiv)
  have hl := abs_le.mp (le_trans (H.large_rem k x hdom) hDz)
  have hf := H.flow k x hdom
  have hm := H.margin
  constructor <;> nlinarith [hs.1, hs.2, hl.1, hl.2]

/-! ## 2. (H-sf): from the rarity of large-field events -/

section SmallField

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Union bound: if finitely many large-field events `Bad b` (`b ∈ R`) each have probability `≤ ε`,
the small-field event (none occurs) has probability `≥ 1 − |R| ε`. -/
theorem small_field_mass_of_rarity (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} (R : Finset ι) (Bad : ι → Set Ω) (ε : ℝ≥0∞)
    (hbad : ∀ b ∈ R, μ (Bad b) ≤ ε) (Good : Set Ω) (hgood : (⋃ b ∈ R, Bad b)ᶜ ⊆ Good) :
    1 - R.card * ε ≤ μ Good := by
  have hU : μ (⋃ b ∈ R, Bad b) ≤ R.card * ε := by
    calc μ (⋃ b ∈ R, Bad b) ≤ ∑ b ∈ R, μ (Bad b) := measure_biUnion_finset_le R Bad
      _ ≤ ∑ _b ∈ R, ε := Finset.sum_le_sum hbad
      _ = R.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
  set U := ⋃ b ∈ R, Bad b with hUdef
  have h1 : (1 : ℝ≥0∞) ≤ μ U + μ Uᶜ := by
    rw [← measure_univ (μ := μ)]
    calc μ univ = μ (U ∪ Uᶜ) := by rw [union_compl_self]
      _ ≤ μ U + μ Uᶜ := measure_union_le _ _
  have h2 : 1 - μ U ≤ μ Uᶜ := tsub_le_iff_left.mpr h1
  calc 1 - R.card * ε ≤ 1 - μ U := tsub_le_tsub_left hU 1
    _ ≤ μ Uᶜ := h2
    _ ≤ μ Good := measure_mono hgood

/-- Invariant form: the large-field event is defined by an invariant `I b` of the field strength on each block (e.g. f₁ − f₂)
exceeding the threshold `θ_h`. The small-field event is `I b ≤ θ_h` for all `b ∈ R`. -/
theorem small_field_mass_invariant (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} (R : Finset ι) (I : ι → Ω → ℝ) (θh : ℝ) (ε : ℝ≥0∞)
    (hbad : ∀ b ∈ R, μ {ω | θh < I b ω} ≤ ε) :
    1 - R.card * ε ≤ μ {ω | ∀ b ∈ R, I b ω ≤ θh} := by
  apply small_field_mass_of_rarity μ R (fun b => {ω | θh < I b ω}) ε hbad
  intro ω hω
  simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hω
  exact hω

end SmallField

/-! ## 3. (H-reg): measure-theoretic part of the one-step lemma, gauge fixing, equicontinuity -/

section Regularity

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]

/-- For a bounded (`|F| ≤ M`) `L`-Lipschitz observable, the difference of expectations of the images under two block maps is at most
the expectation of `min(2M, L·d)` of their distance. -/
theorem expectation_diff_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : E → ℝ) (M L : ℝ) (hM : ∀ e, |F e| ≤ M)
    (hLip : ∀ e e', |F e - F e'| ≤ L * dist e e')
    (V₁ V₂ : Ω → E)
    (hi₁ : Integrable (fun ω => F (V₁ ω)) μ) (hi₂ : Integrable (fun ω => F (V₂ ω)) μ)
    (him : Integrable (fun ω => min (2 * M) (L * dist (V₁ ω) (V₂ ω))) μ) :
    |∫ ω, F (V₁ ω) ∂μ - ∫ ω, F (V₂ ω) ∂μ| ≤
      ∫ ω, min (2 * M) (L * dist (V₁ ω) (V₂ ω)) ∂μ := by
  rw [← integral_sub hi₁ hi₂]
  refine le_trans (abs_integral_le_integral_abs) (integral_mono (hi₁.sub hi₂).abs him ?_)
  intro ω
  simp only
  refine le_min ?_ (hLip _ _)
  have h1 := hM (V₁ ω); have h2 := hM (V₂ ω)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Splitting by the small-field event `G`: `∫ min(2M, L·D) ≤ ∫_G L·D + 2M μ(Gᶜ)`. -/
theorem split_small_field (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (M L : ℝ)
    (G : Set Ω) (hG : MeasurableSet G)
    (him : Integrable (fun ω => min (2 * M) (L * D ω)) μ)
    (hiD : Integrable (G.indicator fun ω => L * D ω) μ) :
    ∫ ω, min (2 * M) (L * D ω) ∂μ ≤
      ∫ ω, G.indicator (fun ω => L * D ω) ω ∂μ + 2 * M * (μ Gᶜ).toReal := by
  have hic : Integrable (Gᶜ.indicator fun _ => 2 * M) μ :=
    (integrable_const (2 * M)).indicator hG.compl
  have hpt : ∀ ω, min (2 * M) (L * D ω) ≤
      G.indicator (fun ω => L * D ω) ω + Gᶜ.indicator (fun _ => 2 * M) ω := by
    intro ω
    by_cases h : ω ∈ G
    · rw [indicator_of_mem h, indicator_of_notMem (by simpa using h)]
      simp only [add_zero]; exact min_le_right _ _
    · rw [indicator_of_notMem h, indicator_of_mem (by simpa using h)]
      simp only [zero_add]; exact min_le_left _ _
  calc ∫ ω, min (2 * M) (L * D ω) ∂μ
      ≤ ∫ ω, (G.indicator (fun ω => L * D ω) ω + Gᶜ.indicator (fun _ => 2 * M) ω) ∂μ :=
        integral_mono him (hiD.add hic) hpt
    _ = ∫ ω, G.indicator (fun ω => L * D ω) ω ∂μ + ∫ ω, Gᶜ.indicator (fun _ => 2 * M) ω ∂μ :=
        integral_add hiD hic
    _ = ∫ ω, G.indicator (fun ω => L * D ω) ω ∂μ + 2 * M * (μ Gᶜ).toReal := by
        rw [integral_indicator_const _ hG.compl]
        simp [Measure.real, smul_eq_mul, mul_comm]

/-- Gauge fixing G_k: the difference of a gauge-invariant `L`-Lipschitz observable is bounded by the distance measured in any gauge `g`
(the background-field estimate may be used in the gauge where it holds). -/
theorem gauge_choice {G : Type*} (act : G → E → E) (F : E → ℝ) (L : ℝ)
    (hinv : ∀ g e, F (act g e) = F e) (hLip : ∀ e e', |F e - F e'| ≤ L * dist e e')
    (g : G) (e e' : E) : |F e - F e'| ≤ L * dist (act g e) (act g e') := by
  rw [← hinv g e, ← hinv g e']; exact hLip _ _

end Regularity

section Equicontinuity

variable {X : Type*} [PseudoMetricSpace X]

/-- If the estimate splits into a term τ_n going to 0 with the lattice and a term Ω(r) going to 0 with the shift,
the form of the `equicontinuous` field of Theorem W follows. -/
theorem equicontinuous_of_split (D : Set X) (s : ℕ → X → ℝ) (τ : ℕ → ℝ) (Ωr : ℝ → ℝ)
    (hτ : Tendsto τ atTop (𝓝 0))
    (hΩ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ωr r ≤ η)
    (hsplit : ∀ n, ∀ d ∈ D, ∀ d' ∈ D, |s n d - s n d'| ≤ τ n + Ωr (dist d d')) :
    ∀ η > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ η := by
  intro η hη
  obtain ⟨δ, hδ, hΩδ⟩ := hΩ (η / 2) (by positivity)
  refine ⟨δ, hδ, fun d hd d' hd' hdd => ?_⟩
  have hev : ∀ᶠ n in atTop, τ n ≤ η / 2 :=
    (hτ.eventually (Iic_mem_nhds (by positivity : (0:ℝ) < η / 2))).mono fun n hn => hn
  refine hev.mono fun n hn => ?_
  have := hsplit n d hd d' hd'
  have := hΩδ (dist d d') dist_nonneg hdd
  linarith

/-- The sum of two estimates going to 0 also goes to 0 (assembling τ and Ω from parts). -/
theorem vanishing_add (Ω₁ Ω₂ : ℝ → ℝ)
    (h₁ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ω₁ r ≤ η)
    (h₂ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ω₂ r ≤ η) :
    ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ω₁ r + Ω₂ r ≤ η := by
  intro η hη
  obtain ⟨δ₁, hδ₁, k₁⟩ := h₁ (η / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, k₂⟩ := h₂ (η / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r hr hrδ => ?_⟩
  have := k₁ r hr (lt_of_lt_of_le hrδ (min_le_left _ _))
  have := k₂ r hr (lt_of_lt_of_le hrδ (min_le_right _ _))
  linarith

/-- The linear term `c·r` (smoothness of the background) goes to 0. -/
theorem vanishing_linear (c : ℝ) (hc : 0 ≤ c) :
    ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → c * r ≤ η := by
  intro η hη
  refine ⟨η / (c + 1), by positivity, fun r hr hrδ => ?_⟩
  have hc1 : 0 < c + 1 := by linarith
  have : r * (c + 1) < η := by rwa [lt_div_iff₀ hc1] at hrδ
  nlinarith

end Equicontinuity

/-! ## 4. The chain: from per-step premises to the three fields of Theorem W -/

section Chain

variable {X : Type*} [PseudoMetricSpace X]
variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]

/-- The bundled chain premises.
* `steps`: the coupling part of S_k and L_k (§1).
* `rarity`: the rarity in L_k. For each block `b ∈ R m` at scale `m`, the probability of the large-field event (invariant form) is
  ≤ `ε m` on fine enough lattices.
* `split`: the one-step estimate through S_k, G_k, (H-reg-lf) splits into a term going to 0 with the lattice and one going to 0 with the shift. -/
structure ChainHypotheses (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (b C D ρ A B Z ustar : ℝ)
    (ν : ℕ → ∀ m, Measure (E m)) {ι : ℕ → Type*} (R : ∀ m, Finset (ι m))
    (I : ∀ m, ι m → E m → ℝ) (θh : ℕ → ℝ) (ε : ℕ → ℝ≥0∞)
    (Dset : Set X) (s : ℕ → X → ℝ) (τ : ℕ → ℝ) (Ωr : ℝ → ℝ) : Prop where
  steps : CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar
  prob : ∀ n m, IsProbabilityMeasure (ν n m)
  rarity : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m, ν n m {ω | θh m < I m i ω} ≤ ε m
  lattice_vanishing : Tendsto τ atTop (𝓝 0)
  shift_vanishing : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ωr r ≤ η
  split : ∀ n, ∀ d ∈ Dset, ∀ d' ∈ Dset, |s n d - s n d'| ≤ τ n + Ωr (dist d d')

/-- Chain theorem: from the per-step premises follow (H-β) (the `hS` form of the bare-coupling lemma (W0)), (H-sf) (the `small_field_mass` form, with the event
defined by the invariant) and (H-reg) (the `equicontinuous` form) of Theorem W. -/
theorem chain_to_hypotheses {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    {ν : ℕ → ∀ m, Measure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R I θh ε Dset s τ Ωr) :
    (∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2) ∧
    (∀ m, ∀ᶠ n in atTop,
      1 - (R m).card * ε m ≤ ν n m {ω | ∀ i ∈ R m, I m i ω ≤ θh m}) ∧
    (∀ η > 0, ∃ δ > 0, ∀ d ∈ Dset, ∀ d' ∈ Dset, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ η) := by
  refine ⟨hbeta_of_steps H.steps, ?_, ?_⟩
  · intro m
    refine (H.rarity m).mono fun n hn => ?_
    have := H.prob n m
    exact small_field_mass_invariant (ν n m) (R m) (I m) (θh m) (ε m) hn
  · exact equicontinuous_of_split Dset s τ Ωr H.lattice_vanishing H.shift_vanishing H.split

end Chain

/-! ## 5. Axiom check -/

#print axioms activity_le
#print axioms hbeta_of_steps
#print axioms small_field_mass_of_rarity
#print axioms small_field_mass_invariant
#print axioms expectation_diff_le
#print axioms split_small_field
#print axioms gauge_choice
#print axioms equicontinuous_of_split
#print axioms vanishing_add
#print axioms vanishing_linear
#print axioms chain_to_hypotheses

end UltravioletChain

/-! ## 1. The ker φ form of the remainder -/

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ker φ form of the remainder: if the source part `s` is in ker φ, the quadratic part `q` satisfies `‖q v‖ ≤ a‖v‖²`, the orbit lies in the
closed ball `‖v‖ ≤ (c₀/u)/(1−λ)`, and the coupling increment is `r = d + u·φ(Rf v)` (`|d| ≤ δ` the difference between λ* and the universal value),
then `|r| ≤ δ + ‖φ‖ a c₀²/((1−λ)² u)`. -/
theorem small_rem_kernel (φ : E →L[ℝ] ℝ) (Rf q : E → E) (s : E) (hs : φ s = 0)
    (hRf : ∀ v, Rf v = s + q v) (a c₀ lam u δ d : ℝ) (ha : 0 ≤ a) (hl : lam < 1) (hu : 0 < u)
    (hq : ∀ v, ‖q v‖ ≤ a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ (c₀ / u) / (1 - lam))
    (hd : |d| ≤ δ) :
    |d + u * φ (Rf v)| ≤ δ + ‖φ‖ * (a * c₀ ^ 2 / ((1 - lam) ^ 2 * u)) := by
  have hl0 : 0 < 1 - lam := by linarith
  have h1 : φ (Rf v) = φ (q v) := by rw [hRf, map_add, hs, zero_add]
  have h2 : |φ (q v)| ≤ ‖φ‖ * ‖q v‖ := by
    have := φ.le_opNorm (q v); rwa [Real.norm_eq_abs] at this
  have h3 : ‖v‖ ^ 2 ≤ ((c₀ / u) / (1 - lam)) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have h4 : ‖q v‖ ≤ a * ((c₀ / u) / (1 - lam)) ^ 2 :=
    le_trans (hq v) (mul_le_mul_of_nonneg_left h3 ha)
  have h5 : |φ (q v)| ≤ ‖φ‖ * (a * ((c₀ / u) / (1 - lam)) ^ 2) :=
    le_trans h2 (mul_le_mul_of_nonneg_left h4 (norm_nonneg φ))
  have e : u * (a * ((c₀ / u) / (1 - lam)) ^ 2) = a * c₀ ^ 2 / ((1 - lam) ^ 2 * u) := by
    field_simp
  have h6 : |u * φ (Rf v)| ≤ ‖φ‖ * (a * c₀ ^ 2 / ((1 - lam) ^ 2 * u)) := by
    rw [h1, abs_mul, abs_of_pos hu, ← e]
    calc u * |φ (q v)| ≤ u * (‖φ‖ * (a * ((c₀ / u) / (1 - lam)) ^ 2)) :=
          mul_le_mul_of_nonneg_left h5 hu.le
      _ = ‖φ‖ * (u * (a * ((c₀ / u) / (1 - lam)) ^ 2)) := by ring
  calc |d + u * φ (Rf v)| ≤ |d| + |u * φ (Rf v)| := abs_add_le _ _
    _ ≤ δ + ‖φ‖ * (a * c₀ ^ 2 / ((1 - lam) ^ 2 * u)) := add_le_add hd h6

/-- If `‖φ‖ ≤ 1` (`‖φ‖ = 1` for the direct-sum norm used here), then `|r| ≤ δ + C₂/u` with `C₂ = a c₀²/(1−λ)²`. -/
theorem small_rem_kernel_unit (φ : E →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (Rf q : E → E) (s : E) (hs : φ s = 0)
    (hRf : ∀ v, Rf v = s + q v) (a c₀ lam u δ d : ℝ) (ha : 0 ≤ a) (hl : lam < 1) (hu : 0 < u)
    (hq : ∀ v, ‖q v‖ ≤ a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ (c₀ / u) / (1 - lam))
    (hd : |d| ≤ δ) :
    |d + u * φ (Rf v)| ≤ δ + (a * c₀ ^ 2 / (1 - lam) ^ 2) / u := by
  have h := small_rem_kernel φ Rf q s hs hRf a c₀ lam u δ d ha hl hu hq v hv hd
  have hl0 : 0 < 1 - lam := by linarith
  have hC : 0 ≤ a * c₀ ^ 2 / ((1 - lam) ^ 2 * u) := by positivity
  have e : a * c₀ ^ 2 / ((1 - lam) ^ 2 * u) = (a * c₀ ^ 2 / (1 - lam) ^ 2) / u := by
    field_simp
  rw [← e]
  nlinarith

/-! ## 2. Type caveat: the coupling increment vanishes for the projected remainder -/

/-- For a remainder with values in ker φ (the projected remainder), `u·φ(R v) = 0`. The chain's small_rem takes the unprojected remainder. -/
theorem projected_remainder_zero (φ : E →L[ℝ] ℝ) (R : E → E) (hR : ∀ v, φ (R v) = 0)
    (u : ℝ) (v : E) : u * φ (R v) = 0 := by rw [hR, mul_zero]

/-- The unprojected and projected remainders differ only by the component in the complement of ker φ:
`Rf = P Rf + (Rf − P Rf)`, and if `φ ∘ P = 0` then `φ(Rf v) = φ(Rf v − P(Rf v))`. -/
theorem coupling_from_unprojected (φ : E →L[ℝ] ℝ) (P : E → E) (hP : ∀ w, φ (P w) = 0)
    (Rf : E → E) (v : E) : φ (Rf v) = φ (Rf v - P (Rf v)) := by
  rw [map_sub, hP, sub_zero]

end Kernel

/-! ## 3. The ker φ version of the per-step premises and (H-β) -/

/-- Per-step premises (ker φ version): UltravioletChain.CouplingSteps with `small_rem` replaced by `|r^s| ≤ δ + C₂/u` and
`margin` replaced by `δ + C₂/u⋆ + DZ ≤ b/2`. -/
structure CouplingStepsKer (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ)
    (b δ C₂ D ρ A B Z ustar : ℝ) : Prop where
  ustar_pos : 0 < ustar
  hb : 0 < b
  hδ : 0 ≤ δ
  hC : 0 ≤ C₂
  hD : 0 ≤ D
  hρ : 0 ≤ ρ
  hA : 0 ≤ A
  hB : 0 ≤ B
  flow : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → u (k + 1) x = u k x - b + rs k x + rl k x
  small_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rs k x| ≤ δ + C₂ / u k x
  large_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rl k x| ≤ D * z k x
  act_rec : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
    z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2
  act_nonneg : ∀ k x, 0 ≤ z k x
  act_init : ∀ x, z 0 x ≤ Z
  supply : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → w k x ≤ Φ (u k x)
  supply_anti : ∀ s t, ustar ≤ s → s ≤ t → Φ t ≤ Φ s
  fix : ρ * Z + A * Φ ustar + B * Z ^ 2 ≤ Z
  margin : δ + C₂ / ustar + D * Z ≤ b / 2

theorem activity_le_ker {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b δ C₂ D ρ A B Z ustar : ℝ}
    (H : CouplingStepsKer u z w rs rl Φ b δ C₂ D ρ A B Z ustar) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → z k x ≤ Z := by
  intro k
  induction k with
  | zero => intro x _; exact H.act_init x
  | succ k ih =>
    intro x hdom
    have hdom' : ∀ j ≤ k, ustar ≤ u j x := fun j hj => hdom j (by omega)
    have hz := ih x hdom'
    have hw : w k x ≤ Φ ustar :=
      le_trans (H.supply k x hdom') (H.supply_anti _ _ le_rfl (hdom' k le_rfl))
    have h1 : ρ * z k x ≤ ρ * Z := mul_le_mul_of_nonneg_left hz H.hρ
    have h2 : A * w k x ≤ A * Φ ustar := mul_le_mul_of_nonneg_left hw H.hA
    have h3 : z k x ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (H.act_nonneg k x) hz 2
    have h4 : B * z k x ^ 2 ≤ B * Z ^ 2 := mul_le_mul_of_nonneg_left h3 H.hB
    linarith [H.act_rec k x hdom', H.fix]

/-- The (H-β) form (ker φ version): inside the domain `u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2`. -/
theorem hbeta_of_steps_ker {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b δ C₂ D ρ A B Z ustar : ℝ}
    (H : CouplingStepsKer u z w rs rl Φ b δ C₂ D ρ A B Z ustar) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2 := by
  intro k x hdom
  have hu : ustar ≤ u k x := hdom k le_rfl
  have hz := activity_le_ker H k x hdom
  have hdiv : C₂ / u k x ≤ C₂ / ustar := div_le_div_of_nonneg_left H.hC H.ustar_pos hu
  have hDz : D * z k x ≤ D * Z := mul_le_mul_of_nonneg_left hz H.hD
  have hs := abs_le.mp (le_trans (H.small_rem k x hdom) (add_le_add le_rfl hdiv))
  have hl := abs_le.mp (le_trans (H.large_rem k x hdom) hDz)
  have hf := H.flow k x hdom
  have hm := H.margin
  constructor <;> nlinarith [hs.1, hs.2, hl.1, hl.2]

/-! ## 4. Junction with UltravioletChain -/

/-- The original per-step premises are the case δ = 0. -/
theorem steps_ker_of_steps {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    (H : UltravioletChain.CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar) :
    CouplingStepsKer u z w rs rl Φ b 0 C D ρ A B Z ustar where
  ustar_pos := H.ustar_pos
  hb := H.hb
  hδ := le_rfl
  hC := H.hC
  hD := H.hD
  hρ := H.hρ
  hA := H.hA
  hB := H.hB
  flow := H.flow
  small_rem k x h := by rw [zero_add]; exact H.small_rem k x h
  large_rem := H.large_rem
  act_rec := H.act_rec
  act_nonneg := H.act_nonneg
  act_init := H.act_init
  supply := H.supply
  supply_anti := H.supply_anti
  fix := H.fix
  margin := by rw [zero_add]; exact H.margin

/-- For δ = 0 the ker φ version of (H-β) and the original hbeta_of_steps give the same conclusion. -/
theorem hbeta_agrees {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    (H : UltravioletChain.CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar) :
    (∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2) :=
  hbeta_of_steps_ker (steps_ker_of_steps H)

/-- Building the per-step premises from the ker φ form of the remainder: if each step's remainder has the form `r^s = d + u·φ(Rf v)`
and satisfies the hypotheses of `small_rem_kernel_unit`, then the `small_rem` field `|r^s| ≤ δ + C₂/u` holds. -/
theorem small_rem_field_of_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u rs : ℕ → ℝ → ℝ) (ustar : ℝ) (hus : 0 < ustar)
    (φ : E →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (Rf q : ℕ → E → E) (s : ℕ → E) (hs : ∀ k, φ (s k) = 0)
    (hRf : ∀ k v, Rf k v = s k + q k v) (a c₀ lam δ : ℝ) (ha : 0 ≤ a) (hl : lam < 1)
    (hq : ∀ k v, ‖q k v‖ ≤ a * ‖v‖ ^ 2) (v : ℕ → ℝ → E) (d : ℕ → ℝ → ℝ)
    (hv : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → ‖v k x‖ ≤ (c₀ / u k x) / (1 - lam))
    (hd : ∀ k x, |d k x| ≤ δ)
    (hrs : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → rs k x = d k x + u k x * φ (Rf k (v k x))) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rs k x| ≤ δ + (a * c₀ ^ 2 / (1 - lam) ^ 2) / u k x := by
  intro k x hdom
  have hu : 0 < u k x := lt_of_lt_of_le hus (hdom k le_rfl)
  rw [hrs k x hdom]
  exact small_rem_kernel_unit φ hφ (Rf k) (q k) (s k) (hs k) (hRf k) a c₀ lam (u k x) δ (d k x)
    ha hl hu (hq k) (v k x) (hv k x hdom) (hd k x)

section Chain

variable {X : Type*} [PseudoMetricSpace X]
variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]

/-- ker φ version of the chain structure (only the `steps` field replaced). -/
structure ChainHypothesesKer (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (b δ C₂ D ρ A B Z ustar : ℝ)
    (ν : ℕ → ∀ m, Measure (E m)) {ι : ℕ → Type*} (R : ∀ m, Finset (ι m))
    (I : ∀ m, ι m → E m → ℝ) (θh : ℕ → ℝ) (ε : ℕ → ℝ≥0∞)
    (Dset : Set X) (s : ℕ → X → ℝ) (τ : ℕ → ℝ) (Ωr : ℝ → ℝ) : Prop where
  steps : CouplingStepsKer u z w rs rl Φ b δ C₂ D ρ A B Z ustar
  prob : ∀ n m, IsProbabilityMeasure (ν n m)
  rarity : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m, ν n m {ω | θh m < I m i ω} ≤ ε m
  lattice_vanishing : Tendsto τ atTop (𝓝 0)
  shift_vanishing : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ωr r ≤ η
  split : ∀ n, ∀ d ∈ Dset, ∀ d' ∈ Dset, |s n d - s n d'| ≤ τ n + Ωr (dist d d')

/-- Junction: from the ker φ chain, the three conclusions ((H-β), (H-sf), (H-reg)) of the same type as UltravioletChain.chain_to_hypotheses.
UltravioletGlue accepts this type, so they pass directly to the fields of Theorem W. -/
theorem chain_to_hypotheses_ker {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ}
    {b δ C₂ D ρ A B Z ustar : ℝ}
    {ν : ℕ → ∀ m, Measure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : ChainHypothesesKer u z w rs rl Φ b δ C₂ D ρ A B Z ustar ν R I θh ε Dset s τ Ωr) :
    (∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2) ∧
    (∀ m, ∀ᶠ n in atTop,
      1 - (R m).card * ε m ≤ ν n m {ω | ∀ i ∈ R m, I m i ω ≤ θh m}) ∧
    (∀ η > 0, ∃ δ > 0, ∀ d ∈ Dset, ∀ d' ∈ Dset, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ η) := by
  refine ⟨hbeta_of_steps_ker H.steps, ?_, ?_⟩
  · intro m
    refine (H.rarity m).mono fun n hn => ?_
    have := H.prob n m
    exact UltravioletChain.small_field_mass_invariant (ν n m) (R m) (I m) (θh m) (ε m) hn
  · exact UltravioletChain.equicontinuous_of_split Dset s τ Ωr H.lattice_vanishing
      H.shift_vanishing H.split

/-- The original chain structure is the δ = 0 case of the ker φ version (agrees with the conclusion of chain_to_hypotheses). -/
theorem chain_ker_of_chain {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ}
    {b C D ρ A B Z ustar : ℝ}
    {ν : ℕ → ∀ m, Measure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : UltravioletChain.ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R I θh ε Dset s τ Ωr) :
    ChainHypothesesKer u z w rs rl Φ b 0 C D ρ A B Z ustar ν R I θh ε Dset s τ Ωr where
  steps := steps_ker_of_steps H.steps
  prob := H.prob
  rarity := H.rarity
  lattice_vanishing := H.lattice_vanishing
  shift_vanishing := H.shift_vanishing
  split := H.split

end Chain

#print axioms small_rem_kernel
#print axioms small_rem_kernel_unit
#print axioms projected_remainder_zero
#print axioms coupling_from_unprojected
#print axioms activity_le_ker
#print axioms hbeta_of_steps_ker
#print axioms steps_ker_of_steps
#print axioms hbeta_agrees
#print axioms small_rem_field_of_kernel
#print axioms chain_to_hypotheses_ker
#print axioms chain_ker_of_chain

end SmallRemKernel

/-! Copy of MarginRatioTwo (unchanged up to comments) -/
namespace MarginRatioTwo

/-! ## 1. Upper and lower bounds for b/2 = b₀ ln 2 -/

theorem half_b2_lower : (0.03218 : ℝ) ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hden : 0 < 48 * Real.pi ^ 2 := by positivity
  have h1 : 22 / (48 * 3.1416 ^ 2) ≤ 22 / (48 * Real.pi ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) hden; nlinarith
  have h2 : (0.03218 : ℝ) ≤ 22 / (48 * 3.1416 ^ 2) * 0.6931471803 := by norm_num
  have h3 : 22 / (48 * 3.1416 ^ 2) * 0.6931471803 ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 :=
    mul_le_mul h1 hlog2.le (by norm_num) (by positivity)
  linarith

theorem half_b2_upper : 22 / (48 * Real.pi ^ 2) * Real.log 2 < (0.0322 : ℝ) := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hlog2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 22 / (48 * Real.pi ^ 2) ≤ 22 / (48 * 3.1415 ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
  have h2 : 22 / (48 * 3.1415 ^ 2) * (0.6931471808 : ℝ) < 0.0322 := by norm_num
  have h3 : 22 / (48 * Real.pi ^ 2) * Real.log 2 ≤ 22 / (48 * 3.1415 ^ 2) * 0.6931471808 :=
    mul_le_mul h1 hlog2.le hlog0.le (by norm_num)
  linarith

/-! ## 2. Closed-ball condition -/

/-- The value of `(1−λ) r = 3(1−τ)²/(16a)` at the window numbers. -/
theorem ball_bound_value :
    (0.004015 : ℝ) ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) ∧
    (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) ≤ (0.004016 : ℝ) := by
  constructor <;> norm_num

/-- c₀ = 0.022: the closed-ball condition holds if `u ≥ 5.48` (β = 4u ≥ 21.92). -/
theorem ball_c022 (u : ℝ) (hu : 5.48 ≤ u) :
    0.022 / u ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) := by
  have hb := ball_bound_value.1
  have hu0 : 0 < u := by linarith
  rw [div_le_iff₀ hu0]; nlinarith

/-- c₀ = 0.04: the closed-ball condition fails at β = 28 (u = 7). -/
theorem ball_c04_fails_beta28 :
    (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) < (0.04 : ℝ) / 7 := by
  norm_num

/-- c₀ = 0.04: the closed-ball condition holds if `u ≥ 9.97` (β ≥ 39.88). -/
theorem ball_c04 (u : ℝ) (hu : 9.97 ≤ u) :
    0.04 / u ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) := by
  have hb := ball_bound_value.1
  have hu0 : 0 < u := by linarith
  rw [div_le_iff₀ hu0]; nlinarith

/-! ## 3. The form ‖ψ‖ = u⋆ -/

/-- β = 28, c₀ = 0.022, ‖ψ‖ ≤ 7: the margin at factor 2 holds up to DZ ≤ 0.0044. -/
theorem margin2_beta28_c022 (ψ DZ : ℝ) (hψ : ψ ≤ 7) (hDZ : DZ ≤ 0.0044) :
    ψ * 0.022 * (1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7)) / 7 + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hb := half_b2_lower
  have hF : (1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) : ℝ) ≤ 1.261 := by norm_num
  have hF0 : (0 : ℝ) ≤ 1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) := by norm_num
  have : ψ * 0.022 * (1 + 4.3348 * 0.022 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7)) / 7 ≤
      7 * 0.022 * 1.261 / 7 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (mul_le_mul_of_nonneg_right hψ (by norm_num)) hF hF0 (by norm_num)
  norm_num at this ⊢
  linarith

/-- With ‖ψ‖ = u⋆, c₀ = 0.04 never fits the factor-2 margin for any u⋆ > 0:
`u⋆ · c₀ · F / u⋆ = c₀ F ≥ c₀ = 0.04 > b₀ ln 2`. -/
theorem margin2_c04_fform_fails (ustar DZ : ℝ) (hus : 0 < ustar) (hDZ : 0 ≤ DZ) :
    22 / (48 * Real.pi ^ 2) * Real.log 2 <
      ustar * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar)) / ustar + DZ := by
  have hb := half_b2_upper
  have hF : (1 : ℝ) ≤ 1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar) := by
    have : (0 : ℝ) ≤ 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar) := by positivity
    linarith
  have e : ustar * 0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar)) / ustar =
      0.04 * (1 + 4.3348 * 0.04 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * ustar)) := by
    field_simp
  rw [e]; nlinarith

/-! ## 4. The ker φ form: |δλ| + C₂/u -/

/-- β = 28 (u⋆ = 7), c₀ = 0.022, |δλ| ≤ 0.022: holds up to DZ ≤ 0.0044. -/
theorem margin2_ker_beta28_c022 (δ DZ : ℝ) (hδ : |δ| ≤ 0.022) (hDZ : DZ ≤ 0.0044) :
    |δ| + 4.3348 * 0.022 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hb := half_b2_lower
  have hC : (4.3348 * 0.022 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) : ℝ) ≤ 0.00574 := by norm_num
  linarith

/-- β = 54 (u⋆ = 13.5), c₀ = 0.04, |δλ| ≤ 0.022: holds up to DZ ≤ 0.0003. -/
theorem margin2_ker_beta54_c04 (δ DZ : ℝ) (hδ : |δ| ≤ 0.022) (hDZ : DZ ≤ 0.0003) :
    |δ| + 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) + DZ ≤
      22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  have hb := half_b2_lower
  have hC : (4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) : ℝ) ≤ 0.00984 := by
    norm_num
  linarith

/-- β = 40 (u⋆ = 10), c₀ = 0.04, at the edge δλ = 0.022: fails even with DZ = 0. -/
theorem margin2_ker_beta40_c04_fails (DZ : ℝ) (hDZ : 0 ≤ DZ) :
    22 / (48 * Real.pi ^ 2) * Real.log 2 <
      0.022 + 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 10) + DZ := by
  have hb := half_b2_upper
  have hC : (0.0132 : ℝ) ≤ 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 10) := by
    norm_num
  linarith

#print axioms half_b2_lower
#print axioms half_b2_upper
#print axioms ball_bound_value
#print axioms ball_c022
#print axioms ball_c04_fails_beta28
#print axioms ball_c04
#print axioms margin2_beta28_c022
#print axioms margin2_c04_fform_fails
#print axioms margin2_ker_beta28_c022
#print axioms margin2_ker_beta54_c04
#print axioms margin2_ker_beta40_c04_fails

end MarginRatioTwo

/-! Copy of KernelMarginNumbers (unchanged up to comments) -/
namespace KernelMarginNumbers

/-- Flow at scale factor 2. -/
noncomputable def bRatioTwo : ℝ := 2 * (22 / (48 * Real.pi ^ 2) * Real.log 2)

theorem bRatioTwo_pos : 0 < bRatioTwo := by
  unfold bRatioTwo
  have := MarginRatioTwo.half_b2_lower
  linarith

/-- Coefficient of the quadratic term C₂ = a c₀²/(1−λ)². -/
noncomputable def C2 (c₀ : ℝ) : ℝ := 4.3348 * c₀ ^ 2 / (1 - (3 * 0.6953 + 1) / 4) ^ 2

theorem C2_nonneg (c₀ : ℝ) : 0 ≤ C2 c₀ := by unfold C2; positivity

/-- β = 28, c₀ = 0.022: the margin field. -/
theorem margin_beta28 (D Z : ℝ) (hDZ : D * Z ≤ 0.0044) :
    0.022 + C2 0.022 / 7 + D * Z ≤ bRatioTwo / 2 := by
  have h := MarginRatioTwo.margin2_ker_beta28_c022 0.022 (D * Z) (by norm_num [abs_of_pos]) hDZ
  have e : C2 0.022 / 7 = 4.3348 * 0.022 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 7) := by
    unfold C2; rw [div_div]
  have e2 : bRatioTwo / 2 = 22 / (48 * Real.pi ^ 2) * Real.log 2 := by unfold bRatioTwo; ring
  rw [e, e2]
  have : |(0.022 : ℝ)| = 0.022 := abs_of_pos (by norm_num)
  rw [this] at h
  exact h

/-- β = 54, c₀ = 0.04: the margin field. -/
theorem margin_beta54 (D Z : ℝ) (hDZ : D * Z ≤ 0.0003) :
    0.022 + C2 0.04 / 13.5 + D * Z ≤ bRatioTwo / 2 := by
  have h := MarginRatioTwo.margin2_ker_beta54_c04 0.022 (D * Z) (by norm_num [abs_of_pos]) hDZ
  have e : C2 0.04 / 13.5 = 4.3348 * 0.04 ^ 2 / ((1 - (3 * 0.6953 + 1) / 4) ^ 2 * 13.5) := by
    unfold C2; rw [div_div]
  have e2 : bRatioTwo / 2 = 22 / (48 * Real.pi ^ 2) * Real.log 2 := by unfold bRatioTwo; ring
  rw [e, e2]
  have : |(0.022 : ℝ)| = 0.022 := abs_of_pos (by norm_num)
  rw [this] at h
  exact h

/-- Assembles the per-step premises of the β = 28 chain with numbers (the margin field is filled numerically;
only DZ ≤ 0.0044 remains). -/
theorem steps_beta28 (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (D ρ A B Z : ℝ)
    (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (flow : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → u (k + 1) x = u k x - bRatioTwo + rs k x + rl k x)
    (small_rem : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → |rs k x| ≤ 0.022 + C2 0.022 / u k x)
    (large_rem : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → |rl k x| ≤ D * z k x)
    (act_rec : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) →
      z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2)
    (act_nonneg : ∀ k x, 0 ≤ z k x) (act_init : ∀ x, z 0 x ≤ Z)
    (supply : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → w k x ≤ Φ (u k x))
    (supply_anti : ∀ s t, 7 ≤ s → s ≤ t → Φ t ≤ Φ s)
    (fix : ρ * Z + A * Φ 7 + B * Z ^ 2 ≤ Z) (hDZ : D * Z ≤ 0.0044) :
    SmallRemKernel.CouplingStepsKer u z w rs rl Φ bRatioTwo 0.022 (C2 0.022) D ρ A B Z 7 where
  ustar_pos := by norm_num
  hb := bRatioTwo_pos
  hδ := by norm_num
  hC := C2_nonneg _
  hD := hD
  hρ := hρ
  hA := hA
  hB := hB
  flow := flow
  small_rem := small_rem
  large_rem := large_rem
  act_rec := act_rec
  act_nonneg := act_nonneg
  act_init := act_init
  supply := supply
  supply_anti := supply_anti
  fix := fix
  margin := margin_beta28 D Z hDZ

/-- The (H-β) form for β = 28 (factor 2): `u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2`, b = 2b₀ ln 2. -/
theorem hbeta_beta28 (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (D ρ A B Z : ℝ)
    (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (flow : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → u (k + 1) x = u k x - bRatioTwo + rs k x + rl k x)
    (small_rem : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → |rs k x| ≤ 0.022 + C2 0.022 / u k x)
    (large_rem : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → |rl k x| ≤ D * z k x)
    (act_rec : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) →
      z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2)
    (act_nonneg : ∀ k x, 0 ≤ z k x) (act_init : ∀ x, z 0 x ≤ Z)
    (supply : ∀ k x, (∀ j ≤ k, 7 ≤ u j x) → w k x ≤ Φ (u k x))
    (supply_anti : ∀ s t, 7 ≤ s → s ≤ t → Φ t ≤ Φ s)
    (fix : ρ * Z + A * Φ 7 + B * Z ^ 2 ≤ Z) (hDZ : D * Z ≤ 0.0044) :
    ∀ k x, (∀ j ≤ k, 7 ≤ u j x) →
      u k x - 3 * bRatioTwo / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - bRatioTwo / 2 :=
  SmallRemKernel.hbeta_of_steps_ker (steps_beta28 u z w rs rl Φ D ρ A B Z hD hρ hA hB flow
    small_rem large_rem act_rec act_nonneg act_init supply supply_anti fix hDZ)

#print axioms bRatioTwo_pos
#print axioms C2_nonneg
#print axioms margin_beta28
#print axioms margin_beta54
#print axioms steps_beta28
#print axioms hbeta_beta28

end KernelMarginNumbers

namespace KernelMarginWindow

open KernelMarginNumbers

/-- c₀ = 0.022, β = 33 (u⋆ = 8.25): holds up to DZ ≤ 0.0053. -/
theorem margin_beta33 (D Z : ℝ) (hDZ : D * Z ≤ 0.0053) :
    0.022 + C2 0.022 / 8.25 + D * Z ≤ bRatioTwo / 2 := by
  have hb := MarginRatioTwo.half_b2_lower
  have e2 : bRatioTwo / 2 = 22 / (48 * Real.pi ^ 2) * Real.log 2 := by unfold bRatioTwo; ring
  have hC : C2 0.022 / 8.25 ≤ 0.00487 := by unfold C2; norm_num
  rw [e2]; linarith

/-- c₀ = 0.022, β = 36 (u⋆ = 9): holds up to DZ ≤ 0.0057. -/
theorem margin_beta36 (D Z : ℝ) (hDZ : D * Z ≤ 0.0057) :
    0.022 + C2 0.022 / 9 + D * Z ≤ bRatioTwo / 2 := by
  have hb := MarginRatioTwo.half_b2_lower
  have e2 : bRatioTwo / 2 = 22 / (48 * Real.pi ^ 2) * Real.log 2 := by unfold bRatioTwo; ring
  have hC : C2 0.022 / 9 ≤ 0.004464 := by unfold C2; norm_num
  rw [e2]; linarith

/-- c₀ = 0.022, β = 38 (u⋆ = 9.5): holds up to DZ ≤ 0.0059. -/
theorem margin_beta38 (D Z : ℝ) (hDZ : D * Z ≤ 0.0059) :
    0.022 + C2 0.022 / 9.5 + D * Z ≤ bRatioTwo / 2 := by
  have hb := MarginRatioTwo.half_b2_lower
  have e2 : bRatioTwo / 2 = 22 / (48 * Real.pi ^ 2) * Real.log 2 := by unfold bRatioTwo; ring
  have hC : C2 0.022 / 9.5 ≤ 0.00423 := by unfold C2; norm_num
  rw [e2]; linarith

/-- c₀ = 0.04 fails the margin at each of β = 33, 36, 38, even with DZ = 0 (C₂/u⋆ ≥ 0.0139 for u⋆ ≤ 9.5). -/
theorem c04_fails (ustar DZ : ℝ) (hus : 0 < ustar) (hu : ustar ≤ 9.5) (hDZ : 0 ≤ DZ) :
    bRatioTwo / 2 < 0.022 + C2 0.04 / ustar + DZ := by
  have hb := MarginRatioTwo.half_b2_upper
  have e2 : bRatioTwo / 2 = 22 / (48 * Real.pi ^ 2) * Real.log 2 := by unfold bRatioTwo; ring
  have hC0 : (0.0139 : ℝ) ≤ C2 0.04 / 9.5 := by unfold C2; norm_num
  have hC : C2 0.04 / 9.5 ≤ C2 0.04 / ustar :=
    div_le_div_of_nonneg_left (C2_nonneg _) hus hu
  rw [e2]; linarith

/-- c₀ = 0.04 also fails the closed-ball condition for u⋆ ≤ 9.5. -/
theorem c04_ball_fails (ustar : ℝ) (hus : 0 < ustar) (hu : ustar ≤ 9.5) :
    (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) < 0.04 / ustar := by
  have hb := MarginRatioTwo.ball_bound_value.2
  have : (0.04 : ℝ) / 9.5 ≤ 0.04 / ustar := div_le_div_of_nonneg_left (by norm_num) hus hu
  have h2 : (0.004016 : ℝ) < 0.04 / 9.5 := by norm_num
  linarith

/-- c₀ = 0.022 satisfies the closed-ball condition for β = 33 to 38 (u⋆ ≥ 8.25). -/
theorem c022_ball (u : ℝ) (hu : 8.25 ≤ u) :
    0.022 / u ≤ (1 - (3 * 0.6953 + 1) / 4) * ((1 - 0.6953) / (4 * 4.3348)) :=
  MarginRatioTwo.ball_c022 u (by linarith)

/-- Assembles the per-step premises with the numbers for u⋆ and the margin (c₀ = 0.022, δ = 0.022, factor 2). -/
theorem steps_window (ustar : ℝ) (hus : 0 < ustar)
    (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (D ρ A B Z : ℝ)
    (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (flow : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → u (k + 1) x = u k x - bRatioTwo + rs k x + rl k x)
    (small_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rs k x| ≤ 0.022 + C2 0.022 / u k x)
    (large_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rl k x| ≤ D * z k x)
    (act_rec : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2)
    (act_nonneg : ∀ k x, 0 ≤ z k x) (act_init : ∀ x, z 0 x ≤ Z)
    (supply : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → w k x ≤ Φ (u k x))
    (supply_anti : ∀ s t, ustar ≤ s → s ≤ t → Φ t ≤ Φ s)
    (fix : ρ * Z + A * Φ ustar + B * Z ^ 2 ≤ Z)
    (hmargin : 0.022 + C2 0.022 / ustar + D * Z ≤ bRatioTwo / 2) :
    SmallRemKernel.CouplingStepsKer u z w rs rl Φ bRatioTwo 0.022 (C2 0.022) D ρ A B Z ustar where
  ustar_pos := hus
  hb := bRatioTwo_pos
  hδ := by norm_num
  hC := C2_nonneg _
  hD := hD
  hρ := hρ
  hA := hA
  hB := hB
  flow := flow
  small_rem := small_rem
  large_rem := large_rem
  act_rec := act_rec
  act_nonneg := act_nonneg
  act_init := act_init
  supply := supply
  supply_anti := supply_anti
  fix := fix
  margin := hmargin

/-- The (H-β) form for β = 33 (factor 2, c₀ = 0.022, DZ ≤ 0.0053). β = 36, 38 are the same via margin_beta36, 38. -/
theorem hbeta_beta33 (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (D ρ A B Z : ℝ)
    (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (flow : ∀ k x, (∀ j ≤ k, 8.25 ≤ u j x) → u (k + 1) x = u k x - bRatioTwo + rs k x + rl k x)
    (small_rem : ∀ k x, (∀ j ≤ k, 8.25 ≤ u j x) → |rs k x| ≤ 0.022 + C2 0.022 / u k x)
    (large_rem : ∀ k x, (∀ j ≤ k, 8.25 ≤ u j x) → |rl k x| ≤ D * z k x)
    (act_rec : ∀ k x, (∀ j ≤ k, 8.25 ≤ u j x) →
      z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2)
    (act_nonneg : ∀ k x, 0 ≤ z k x) (act_init : ∀ x, z 0 x ≤ Z)
    (supply : ∀ k x, (∀ j ≤ k, 8.25 ≤ u j x) → w k x ≤ Φ (u k x))
    (supply_anti : ∀ s t, 8.25 ≤ s → s ≤ t → Φ t ≤ Φ s)
    (fix : ρ * Z + A * Φ 8.25 + B * Z ^ 2 ≤ Z) (hDZ : D * Z ≤ 0.0053) :
    ∀ k x, (∀ j ≤ k, 8.25 ≤ u j x) →
      u k x - 3 * bRatioTwo / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - bRatioTwo / 2 :=
  SmallRemKernel.hbeta_of_steps_ker (steps_window 8.25 (by norm_num) u z w rs rl Φ D ρ A B Z
    hD hρ hA hB flow small_rem large_rem act_rec act_nonneg act_init supply supply_anti fix
    (margin_beta33 D Z hDZ))

#print axioms margin_beta33
#print axioms margin_beta36
#print axioms margin_beta38
#print axioms c04_fails
#print axioms c04_ball_fails
#print axioms c022_ball
#print axioms steps_window
#print axioms hbeta_beta33

end KernelMarginWindow
