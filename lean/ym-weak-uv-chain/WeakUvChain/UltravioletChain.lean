/-
The chain deriving the three premises (H-β)(H-reg)(H-sf) of Theorem W from abstract per-step lemmas (small-field step S_k,
large-field step L_k, gauge-fixing step G_k). Single file; checks with `import Mathlib` only.

  §1 (H-β): from S_k (coupling step u_{k+1} = u_k − b + r^s_k + r^ℓ_k, |r^s_k| ≤ C/u_k) and
     L_k (|r^ℓ_k| ≤ D z_k, activity recursion z_{k+1} ≤ ρ z_k + A w_k + B z_k², supply w_k ≤ Φ(u_k)),
     within the domain: activity z_k ≤ Z and u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2 (the (H-β) form of Theorem W).
  §2 (H-sf): if each large-field event (any measurable event, including ones of the form I_b > θ_h for a field-strength
     invariant) has probability ≤ ε, then the small-field event has probability ≥ 1 − |R| ε (union bound); the field form of Theorem W.
  §3 (H-reg): the measure-theoretic part of the one-step lemma (difference of expectations of bounded Lipschitz observables
     ≤ min of expectations, split by the small-field event), gauge fixing G_k (gauge-invariant observables may be measured
     in any gauge), and a bound split into "a term vanishing with the lattice" and "a term vanishing with the shift",
     giving the equicontinuity field form of Theorem W.
  §4 Chain: the three fields from a structure bundling the three.
  §5 #print axioms

The activity recursion of §1 has the same type as the large-field activity recursion bundle (`joint_invariant`),
re-proved in this file with the step direction (fine to coarse, inverse coupling decreasing) and a domain.
The class of effective actions, the integral bounds and the large-field probabilities themselves enter as premises.
-/
import Mathlib

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
