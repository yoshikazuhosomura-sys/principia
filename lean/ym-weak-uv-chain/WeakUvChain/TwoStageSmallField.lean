/-
Two-step form of (H-sf). Single file; checks with `import Mathlib` only.

  The "two-step condition": large-field rarity is counted by the plaquette angle y_p ≥ y_h of the raw field, and the
  edge of analyticity is protected by the invariant f₁ > θ_bg (= 0.68) of the background (smooth field).
  The bad event of block i is
      Bad_i = (⋃_{p ∈ plaq i} {y_h < Y_p}) ∪ (⋃_{x ∈ pts i} {θ_bg < f_x}),
  and if the probability per plaquette is ≤ P₁ and per point ≤ S_bg, then
      μ(Bad_i) ≤ |plaq i|·P₁ + |pts i|·S_bg,
      μ(no block is bad) ≥ 1 − n_box·[n_p·P₁ + n_pt·S_bg]
  (η ≲ n_box·[96·P₁(y_h) + 16·S_bg(0.68)] is the case n_p = 96, n_pt = 16). Only union bounds; the probability
  values are floating-point computations.
  §1 two-term bound for one block  §2 indicator invariant I_i ∈ {0, 1} and rephrasing of events
  §3 mass of the two-step small-field event  §4 glue to the rarity field of UltravioletChain
  §5 reading the (H-sf) field of the chain with the two-step event
  (The body of UltravioletChain is copied in §0, unchanged up to comments; the glue theorems are §4 and §5.)
-/
import Mathlib

namespace TwoStageSmallField

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

/-! ## 1. Two-term bound for one block -/

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {Pl Pt : Type*}

/-- Bad event for one block: some plaquette angle exceeds `y_h`, or some point's background invariant exceeds `θ`. -/
def badSet (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) : Set Ω :=
  {ω | (∃ p ∈ plaq, yh < Y p ω) ∨ (∃ x ∈ pts, θ < f x ω)}

/-- Good event for one block (the two-stage small-field condition). -/
def goodSet (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) : Set Ω :=
  {ω | (∀ p ∈ plaq, Y p ω ≤ yh) ∧ (∀ x ∈ pts, f x ω ≤ θ)}

theorem badSet_eq (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) :
    badSet plaq pts Y f yh θ = (⋃ p ∈ plaq, {ω | yh < Y p ω}) ∪ (⋃ x ∈ pts, {ω | θ < f x ω}) := by
  ext ω; simp [badSet]

theorem goodSet_eq_compl (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ)
    (f : Pt → Ω → ℝ) (yh θ : ℝ) :
    goodSet plaq pts Y f yh θ = (badSet plaq pts Y f yh θ)ᶜ := by
  ext ω; simp only [goodSet, badSet, mem_ofPred_eq, mem_compl_iff, not_or, not_exists, not_and,
    not_lt]

/-- Two-term union bound: `μ(Bad) ≤ |plaq|·P₁ + |pts|·S_bg`. -/
theorem block_bad_le (μ : Measure Ω) (plaq : Finset Pl) (pts : Finset Pt)
    (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ) (yh θ : ℝ) (P₁ S : ℝ≥0∞)
    (hY : ∀ p ∈ plaq, μ {ω | yh < Y p ω} ≤ P₁) (hf : ∀ x ∈ pts, μ {ω | θ < f x ω} ≤ S) :
    μ (badSet plaq pts Y f yh θ) ≤ plaq.card * P₁ + pts.card * S := by
  rw [badSet_eq]
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · calc μ (⋃ p ∈ plaq, {ω | yh < Y p ω}) ≤ ∑ p ∈ plaq, μ {ω | yh < Y p ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ plaq, P₁ := Finset.sum_le_sum hY
      _ = plaq.card * P₁ := by rw [Finset.sum_const, nsmul_eq_mul]
  · calc μ (⋃ x ∈ pts, {ω | θ < f x ω}) ≤ ∑ x ∈ pts, μ {ω | θ < f x ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _x ∈ pts, S := Finset.sum_le_sum hf
      _ = pts.card * S := by rw [Finset.sum_const, nsmul_eq_mul]

/-- With counting bounds: if `|plaq| ≤ n_p` and `|pts| ≤ n_pt`, then `μ(Bad) ≤ n_p·P₁ + n_pt·S_bg`. -/
theorem block_bad_le_counts (μ : Measure Ω) (plaq : Finset Pl) (pts : Finset Pt)
    (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ) (yh θ : ℝ) (P₁ S : ℝ≥0∞) (np npt : ℕ)
    (hnp : plaq.card ≤ np) (hnpt : pts.card ≤ npt)
    (hY : ∀ p ∈ plaq, μ {ω | yh < Y p ω} ≤ P₁) (hf : ∀ x ∈ pts, μ {ω | θ < f x ω} ≤ S) :
    μ (badSet plaq pts Y f yh θ) ≤ np * P₁ + npt * S := by
  refine le_trans (block_bad_le μ plaq pts Y f yh θ P₁ S hY hf) (add_le_add ?_ ?_)
  · have : (plaq.card : ℝ≥0∞) ≤ np := by exact_mod_cast hnp
    gcongr
  · have : (pts.card : ℝ≥0∞) ≤ npt := by exact_mod_cast hnpt
    gcongr

/-! ## 2. Indicator invariant -/

open Classical in
/-- Two-stage indicator invariant of a block: 1 if bad, 0 if good. The form that goes into the chain's `I` field (threshold `θ_h = 1/2`). -/
noncomputable def twoStageIndex (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ)
    (f : Pt → Ω → ℝ) (yh θ : ℝ) (ω : Ω) : ℝ :=
  if (∃ p ∈ plaq, yh < Y p ω) ∨ (∃ x ∈ pts, θ < f x ω) then 1 else 0

theorem index_bad_eq (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) :
    {ω | (1 / 2 : ℝ) < twoStageIndex plaq pts Y f yh θ ω} = badSet plaq pts Y f yh θ := by
  ext ω
  simp only [mem_ofPred_eq, badSet, twoStageIndex]
  split_ifs with h
  · simp only [h, iff_true]; norm_num
  · simp only [h, iff_false, not_lt]; norm_num

theorem index_good_eq (plaq : Finset Pl) (pts : Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) (ω : Ω) :
    twoStageIndex plaq pts Y f yh θ ω ≤ 1 / 2 ↔
      (∀ p ∈ plaq, Y p ω ≤ yh) ∧ (∀ x ∈ pts, f x ω ≤ θ) := by
  have h := congrArg (fun s : Set Ω => ω ∈ s) (index_bad_eq plaq pts Y f yh θ)
  simp only [mem_ofPred_eq, eq_iff_iff] at h
  have h2 := congrArg (fun s : Set Ω => ω ∈ s) (goodSet_eq_compl plaq pts Y f yh θ)
  simp only [eq_iff_iff, mem_compl_iff] at h2
  rw [← not_lt, h]
  exact h2.symm.trans (by simp [goodSet])

end Block

/-! ## 3. Mass of the two-stage small-field event -/

section Mass

variable {Ω : Type*} [MeasurableSpace Ω] {ι Pl Pt : Type*}

/-- Two-stage form of (H-sf): for each block `i ∈ R`, plaquettes `plaq i` (≤ n_p of them) and points `pts i` (≤ n_pt of them); if each
plaquette has probability ≤ P₁ and each point ≤ S_bg, then the event that every block is good has probability ≥ 1 − |R|·(n_p·P₁ + n_pt·S_bg). -/
theorem small_field_two_stage (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Finset ι)
    (plaq : ι → Finset Pl) (pts : ι → Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) (P₁ S : ℝ≥0∞) (np npt : ℕ)
    (hnp : ∀ i ∈ R, (plaq i).card ≤ np) (hnpt : ∀ i ∈ R, (pts i).card ≤ npt)
    (hY : ∀ i ∈ R, ∀ p ∈ plaq i, μ {ω | yh < Y p ω} ≤ P₁)
    (hf : ∀ i ∈ R, ∀ x ∈ pts i, μ {ω | θ < f x ω} ≤ S) :
    1 - R.card * (np * P₁ + npt * S) ≤
      μ {ω | ∀ i ∈ R, (∀ p ∈ plaq i, Y p ω ≤ yh) ∧ (∀ x ∈ pts i, f x ω ≤ θ)} := by
  apply UltravioletChain.small_field_mass_of_rarity μ R (fun i => badSet (plaq i) (pts i) Y f yh θ)
  · intro i hi
    exact block_bad_le_counts μ (plaq i) (pts i) Y f yh θ P₁ S np npt (hnp i hi) (hnpt i hi)
      (hY i hi) (hf i hi)
  · intro ω hω
    simp only [mem_compl_iff, mem_iUnion, not_exists] at hω
    intro i hi
    have := hω i hi
    have h2 := congrArg (fun s : Set Ω => ω ∈ s) (goodSet_eq_compl (plaq i) (pts i) Y f yh θ)
    simp only [eq_iff_iff, mem_compl_iff] at h2
    exact h2.mpr this

/-- The η form: if `|R| ≤ n_box` then `|R|·(n_p·P₁ + n_pt·S_bg) ≤ n_box·(n_p·P₁ + n_pt·S_bg)`. -/
theorem eta_le (R : Finset ι) (nbox np npt : ℕ) (P₁ S : ℝ≥0∞) (hR : R.card ≤ nbox) :
    (R.card : ℝ≥0∞) * (np * P₁ + npt * S) ≤ nbox * (np * P₁ + npt * S) := by
  have : (R.card : ℝ≥0∞) ≤ nbox := by exact_mod_cast hR
  gcongr

/-- Form `1 − n_box·[n_p·P₁ + n_pt·S_bg] ≤ μ(small field)`. -/
theorem small_field_two_stage_box (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Finset ι)
    (plaq : ι → Finset Pl) (pts : ι → Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) (P₁ S : ℝ≥0∞) (nbox np npt : ℕ) (hR : R.card ≤ nbox)
    (hnp : ∀ i ∈ R, (plaq i).card ≤ np) (hnpt : ∀ i ∈ R, (pts i).card ≤ npt)
    (hY : ∀ i ∈ R, ∀ p ∈ plaq i, μ {ω | yh < Y p ω} ≤ P₁)
    (hf : ∀ i ∈ R, ∀ x ∈ pts i, μ {ω | θ < f x ω} ≤ S) :
    1 - nbox * (np * P₁ + npt * S) ≤
      μ {ω | ∀ i ∈ R, (∀ p ∈ plaq i, Y p ω ≤ yh) ∧ (∀ x ∈ pts i, f x ω ≤ θ)} :=
  le_trans (tsub_le_tsub_left (eta_le R nbox np npt P₁ S hR) 1)
    (small_field_two_stage μ R plaq pts Y f yh θ P₁ S np npt hnp hnpt hY hf)

end Mass

/-! ## 4. Junction with the chain's rarity field -/

section ChainGlue

variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]
variable {ι Pl Pt : ℕ → Type*}

/-- Junction: if the per-plaquette and per-point probability bounds hold on fine enough lattices, the two-stage indicator invariant
gives the `rarity` field of UltravioletChain.ChainHypotheses (`θ_h = 1/2`, `ε_m = n_p·P₁ + n_pt·S_bg`). -/
theorem rarity_two_stage (ν : ℕ → ∀ m, Measure (E m)) (R : ∀ m, Finset (ι m))
    (plaq : ∀ m, ι m → Finset (Pl m)) (pts : ∀ m, ι m → Finset (Pt m))
    (Y : ∀ m, Pl m → E m → ℝ) (f : ∀ m, Pt m → E m → ℝ) (yh θ : ℕ → ℝ)
    (P₁ S : ℕ → ℝ≥0∞) (np npt : ℕ → ℕ)
    (hnp : ∀ m, ∀ i ∈ R m, (plaq m i).card ≤ np m)
    (hnpt : ∀ m, ∀ i ∈ R m, (pts m i).card ≤ npt m)
    (hprob : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m,
      (∀ p ∈ plaq m i, ν n m {ω | yh m < Y m p ω} ≤ P₁ m) ∧
      (∀ x ∈ pts m i, ν n m {ω | θ m < f m x ω} ≤ S m)) :
    ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m,
      ν n m {ω | (fun _ => (1 / 2 : ℝ)) m <
        (fun m i => twoStageIndex (plaq m i) (pts m i) (Y m) (f m) (yh m) (θ m)) m i ω} ≤
        (fun m => (np m : ℝ≥0∞) * P₁ m + npt m * S m) m := by
  intro m
  refine (hprob m).mono fun n hn i hi => ?_
  simp only
  rw [index_bad_eq]
  exact block_bad_le_counts (ν n m) (plaq m i) (pts m i) (Y m) (f m) (yh m) (θ m) (P₁ m) (S m)
    (np m) (npt m) (hnp m i hi) (hnpt m i hi) (hn i hi).1 (hn i hi).2

/-! ## 5. Building the chain with the two-stage event, and reading its (H-sf) field as the two-stage event -/

variable {X : Type*} [PseudoMetricSpace X]

/-- Building the chain structure with the two-stage indicator invariant (the rarity field is filled by `rarity_two_stage`). -/
theorem chain_hypotheses_two_stage {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ}
    {b C D ρ A B Z ustar : ℝ}
    (ν : ℕ → ∀ m, Measure (E m)) (R : ∀ m, Finset (ι m))
    (plaq : ∀ m, ι m → Finset (Pl m)) (pts : ∀ m, ι m → Finset (Pt m))
    (Y : ∀ m, Pl m → E m → ℝ) (f : ∀ m, Pt m → E m → ℝ) (yh θ : ℕ → ℝ)
    (P₁ S : ℕ → ℝ≥0∞) (np npt : ℕ → ℕ)
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (hsteps : UltravioletChain.CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar)
    (hP : ∀ n m, IsProbabilityMeasure (ν n m))
    (hnp : ∀ m, ∀ i ∈ R m, (plaq m i).card ≤ np m)
    (hnpt : ∀ m, ∀ i ∈ R m, (pts m i).card ≤ npt m)
    (hprob : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m,
      (∀ p ∈ plaq m i, ν n m {ω | yh m < Y m p ω} ≤ P₁ m) ∧
      (∀ x ∈ pts m i, ν n m {ω | θ m < f m x ω} ≤ S m))
    (hτ : Tendsto τ atTop (𝓝 0))
    (hΩ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ωr r ≤ η)
    (hsplit : ∀ n, ∀ d ∈ Dset, ∀ d' ∈ Dset, |s n d - s n d'| ≤ τ n + Ωr (dist d d')) :
    UltravioletChain.ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R
      (fun m i => twoStageIndex (plaq m i) (pts m i) (Y m) (f m) (yh m) (θ m))
      (fun _ => (1 / 2 : ℝ)) (fun m => (np m : ℝ≥0∞) * P₁ m + npt m * S m) Dset s τ Ωr where
  steps := hsteps
  prob := hP
  rarity := rarity_two_stage ν R plaq pts Y f yh θ P₁ S np npt hnp hnpt hprob
  lattice_vanishing := hτ
  shift_vanishing := hΩ
  split := hsplit

/-- Reading the chain's (H-sf) field as the two-stage event: the second conclusion of chain_to_hypotheses becomes
mass ≥ 1 − |R_m|·(n_p·P₁ + n_pt·S_bg) of the event "angle ≤ y_h at all plaquettes and background invariant ≤ θ at all points"
(and 1 − n_box·[…] if moreover |R_m| ≤ n_box). -/
theorem hsf_two_stage {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ}
    {b C D ρ A B Z ustar : ℝ}
    (ν : ℕ → ∀ m, Measure (E m)) (R : ∀ m, Finset (ι m))
    (plaq : ∀ m, ι m → Finset (Pl m)) (pts : ∀ m, ι m → Finset (Pt m))
    (Y : ∀ m, Pl m → E m → ℝ) (f : ∀ m, Pt m → E m → ℝ) (yh θ : ℕ → ℝ)
    (P₁ S : ℕ → ℝ≥0∞) (np npt nbox : ℕ → ℕ)
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : UltravioletChain.ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R
      (fun m i => twoStageIndex (plaq m i) (pts m i) (Y m) (f m) (yh m) (θ m))
      (fun _ => (1 / 2 : ℝ)) (fun m => (np m : ℝ≥0∞) * P₁ m + npt m * S m) Dset s τ Ωr)
    (hR : ∀ m, (R m).card ≤ nbox m) :
    ∀ m, ∀ᶠ n in atTop,
      1 - nbox m * (np m * P₁ m + npt m * S m) ≤
        ν n m {ω | ∀ i ∈ R m, (∀ p ∈ plaq m i, Y m p ω ≤ yh m) ∧ (∀ x ∈ pts m i, f m x ω ≤ θ m)} := by
  intro m
  refine ((UltravioletChain.chain_to_hypotheses H).2.1 m).mono fun n hn => ?_
  have hset : {ω | ∀ i ∈ R m, twoStageIndex (plaq m i) (pts m i) (Y m) (f m) (yh m) (θ m) ω ≤ 1 / 2} =
      {ω | ∀ i ∈ R m, (∀ p ∈ plaq m i, Y m p ω ≤ yh m) ∧ (∀ x ∈ pts m i, f m x ω ≤ θ m)} := by
    ext ω
    simp only [mem_ofPred_eq]
    exact forall₂_congr fun i _ => index_good_eq _ _ _ _ _ _ ω
  rw [hset] at hn
  exact le_trans (tsub_le_tsub_left (eta_le (R m) (nbox m) (np m) (npt m) (P₁ m) (S m) (hR m)) 1) hn

end ChainGlue

#print axioms badSet_eq
#print axioms goodSet_eq_compl
#print axioms block_bad_le
#print axioms block_bad_le_counts
#print axioms index_bad_eq
#print axioms index_good_eq
#print axioms small_field_two_stage
#print axioms eta_le
#print axioms small_field_two_stage_box
#print axioms rarity_two_stage
#print axioms chain_hypotheses_two_stage
#print axioms hsf_two_stage

end TwoStageSmallField
