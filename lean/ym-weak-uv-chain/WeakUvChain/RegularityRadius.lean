/-
Radius r(η) for (H-reg-lf): on the two-step small-field event of TwoStageSmallField (angle per plaquette ≤ y_h,
background invariant ≤ θ), take the radius of the closed ball of background coordinates to be r(η) = r(y_h(η), θ(η)),
and connect it to RegularityConstant.Keta.
Single file; checks with `import Mathlib` only. The bodies of TwoStageSmallField (containing a copy of UltravioletChain)
and RegularityConstant (containing copies of NontreeBackground and others) are placed at the top, unchanged up to comments.

  §1 η ↔ (y_h, θ): if n_box[n_p P₁(y_h) + n_pt S_bg(θ)] ≤ η, the complement of the two-step event G has probability ≤ η (real form).
  §2 Form of the radius ((P-geom), assumed): on G the background coordinates satisfy ‖v‖ ≤ r(y_h, θ) = C_θ θ + C_y y_h/β.
  §3 Amplification τ + ℓ/u + 2a r < 1 ⇔ r < (1 − τ − ℓ/u)/(2a). With the numerical values (τ ≤ 0.6953, ℓ ≤ 0.36,
     a = 4.3348, u ≥ 7), r ≤ 0.029 gives amplification < 1 and K(η) ≤ κ (independent of η). The window radius
     κ/(4a) ≤ 0.0176 lies inside.
  §4 Difference of expectations ≤ (ΣL)K(η)ρ + 2|I|η, and equicontinuity from a K uniform over all η whose radius is ≤ 0.029.
  C_θ and C_y (conversion between relative coordinates and field angles) remain assumed.
-/
import Mathlib

/-! Copy of TwoStageSmallField (unchanged up to comments) -/
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

/-! Copy of NontreeBackground (unchanged up to comments) -/
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

/-! Copy of RegularityConstant (unchanged up to comments) -/
namespace RegularityConstant

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false

/-! ## 1. Lipschitz constant in a closed ball -/

section Lip

variable {F : Type*} [NormedAddCommGroup F]

/-- From the increment bound of the quadratic-type remainder: in the closed ball `r`, `L = ℓ + 2ar` for NontreeLipschitz. -/
theorem lipschitz_on_ball (T R : ℕ → F → F) (τ ℓ a r : ℝ) (ha : 0 ≤ a)
    (hT : ∀ k w w', ‖T k w - T k w'‖ ≤ τ * ‖w - w'‖)
    (hR : ∀ k w w', ‖R k w - R k w'‖ ≤ (ℓ + a * (‖w‖ + ‖w'‖)) * ‖w - w'‖) :
    NontreeBackground.NontreeLipschitz T R τ (ℓ + 2 * a * r) r := by
  refine ⟨hT, fun k w w' hw hw' => le_trans (hR k w w') ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith

end Lip

/-! ## 2. K(η) -/

/-- K(η) = κ·(τ + ℓ + 2a r(η))^{k₀}. -/
def Keta (κ τ ℓ a : ℝ) (rη : ℝ → ℝ) (k₀ : ℕ) (η : ℝ) : ℝ :=
  κ * (τ + (ℓ + 2 * a * rη η)) ^ k₀

theorem Keta_nonneg (κ τ ℓ a : ℝ) (rη : ℝ → ℝ) (k₀ : ℕ) (η : ℝ) (hκ : 0 ≤ κ)
    (h0 : 0 ≤ τ + (ℓ + 2 * a * rη η)) : 0 ≤ Keta κ τ ℓ a rη k₀ η := by
  unfold Keta; positivity

/-- If the amplification is at most 1, then K(η) ≤ κ (independent of η). -/
theorem Keta_le (κ τ ℓ a : ℝ) (rη : ℝ → ℝ) (k₀ : ℕ) (η : ℝ) (hκ : 0 ≤ κ)
    (h0 : 0 ≤ τ + (ℓ + 2 * a * rη η)) (h1 : τ + (ℓ + 2 * a * rη η) ≤ 1) :
    Keta κ τ ℓ a rη k₀ η ≤ κ := by
  unfold Keta
  have := pow_le_one₀ h0 h1 (n := k₀)
  nlinarith

/-! ## 3. Difference of expectations -/

section Expectation

variable {Ω F ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] [DecidableEq ι]

/-- On the small-field event `G`, for trajectories satisfying premise 8 in Lipschitz form whose background coordinates stay in the closed ball `r`,
with initial shift ≤ κρ:
`|E Π f_i(v k₀) − E Π f_i(v′ k₀)| ≤ (ΣL_i)·(κ(τ+L)^{k₀})·ρ + 2|I| μ(Gᶜ)`. -/
theorem expectation_from_nontree (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Finset ι)
    (f : ι → F → ℝ) (Lf : ι → ℝ) (hL : ∀ i, 0 ≤ Lf i) (hf : ∀ i e, |f i e| ≤ 1)
    (hLip : ∀ i e e', |f i e - f i e'| ≤ Lf i * dist e e')
    (T R : ℕ → F → F) (τ L r : ℝ) (hτL : 0 ≤ τ + L)
    (H : NontreeBackground.NontreeLipschitz T R τ L r)
    (v v' : Ω → ι → ℕ → F) (k₀ : ℕ) (G : Set Ω) (hGm : MeasurableSet G) (κ ρ : ℝ)
    (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hv : ∀ ω i k, v ω i (k + 1) = T k (v ω i k) + R k (v ω i k))
    (hv' : ∀ ω i k, v' ω i (k + 1) = T k (v' ω i k) + R k (v' ω i k))
    (hb : ∀ ω ∈ G, ∀ i ∈ I, ∀ k, ‖v ω i k‖ ≤ r) (hb' : ∀ ω ∈ G, ∀ i ∈ I, ∀ k, ‖v' ω i k‖ ≤ r)
    (hinit : ∀ ω ∈ G, ∀ i ∈ I, ‖v ω i 0 - v' ω i 0‖ ≤ κ * ρ)
    (hi1 : Integrable (fun ω => ∏ i ∈ I, f i (v ω i k₀)) μ)
    (hi2 : Integrable (fun ω => ∏ i ∈ I, f i (v' ω i k₀)) μ) :
    |∫ ω, ∏ i ∈ I, f i (v ω i k₀) ∂μ - ∫ ω, ∏ i ∈ I, f i (v' ω i k₀) ∂μ| ≤
      (∑ i ∈ I, Lf i) * ((κ * (τ + L) ^ k₀) * ρ) + 2 * I.card * μ.real Gᶜ := by
  apply RegularityStep.expectation_bound μ I f Lf hL hf hLip (fun i ω => v ω i k₀)
    (fun i ω => v' ω i k₀) G hGm (κ * (τ + L) ^ k₀) ρ (by positivity) hρ _ hi1 hi2
  intro ω hω i hi
  rw [dist_eq_norm]
  have h := NontreeBackground.shift_difference T R τ L r hτL H (v ω i) (v' ω i) (hv ω i) (hv' ω i)
    (hb ω hω i hi) (hb' ω hω i hi) k₀
  have hp : 0 ≤ (τ + L) ^ k₀ := pow_nonneg hτL k₀
  calc ‖v ω i k₀ - v' ω i k₀‖ ≤ (τ + L) ^ k₀ * ‖v ω i 0 - v' ω i 0‖ := h
    _ ≤ (τ + L) ^ k₀ * (κ * ρ) := mul_le_mul_of_nonneg_left (hinit ω hω i hi) hp
    _ = κ * (τ + L) ^ k₀ * ρ := by ring

/-- Combined with §1: with closed-ball radius `r`, `L = ℓ + 2ar` and K = Keta. -/
theorem expectation_Keta (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Finset ι)
    (f : ι → F → ℝ) (Lf : ι → ℝ) (hL : ∀ i, 0 ≤ Lf i) (hf : ∀ i e, |f i e| ≤ 1)
    (hLip : ∀ i e e', |f i e - f i e'| ≤ Lf i * dist e e')
    (T R : ℕ → F → F) (τ ℓ a : ℝ) (ha : 0 ≤ a) (rη : ℝ → ℝ) (η : ℝ)
    (hpos : 0 ≤ τ + (ℓ + 2 * a * rη η))
    (hT : ∀ k w w', ‖T k w - T k w'‖ ≤ τ * ‖w - w'‖)
    (hR : ∀ k w w', ‖R k w - R k w'‖ ≤ (ℓ + a * (‖w‖ + ‖w'‖)) * ‖w - w'‖)
    (v v' : Ω → ι → ℕ → F) (k₀ : ℕ) (G : Set Ω) (hGm : MeasurableSet G) (κ ρ : ℝ)
    (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hv : ∀ ω i k, v ω i (k + 1) = T k (v ω i k) + R k (v ω i k))
    (hv' : ∀ ω i k, v' ω i (k + 1) = T k (v' ω i k) + R k (v' ω i k))
    (hb : ∀ ω ∈ G, ∀ i ∈ I, ∀ k, ‖v ω i k‖ ≤ rη η)
    (hb' : ∀ ω ∈ G, ∀ i ∈ I, ∀ k, ‖v' ω i k‖ ≤ rη η)
    (hinit : ∀ ω ∈ G, ∀ i ∈ I, ‖v ω i 0 - v' ω i 0‖ ≤ κ * ρ)
    (hi1 : Integrable (fun ω => ∏ i ∈ I, f i (v ω i k₀)) μ)
    (hi2 : Integrable (fun ω => ∏ i ∈ I, f i (v' ω i k₀)) μ) :
    |∫ ω, ∏ i ∈ I, f i (v ω i k₀) ∂μ - ∫ ω, ∏ i ∈ I, f i (v' ω i k₀) ∂μ| ≤
      (∑ i ∈ I, Lf i) * (Keta κ τ ℓ a rη k₀ η * ρ) + 2 * I.card * μ.real Gᶜ := by
  have H := lipschitz_on_ball T R τ ℓ a (rη η) ha hT hR
  have := expectation_from_nontree μ I f Lf hL hf hLip T R τ (ℓ + 2 * a * rη η) (rη η) hpos H
    v v' k₀ G hGm κ ρ hκ hρ hv hv' hb hb' hinit hi1 hi2
  unfold Keta; exact this

end Expectation

/-! ## 4. Equicontinuity -/

/-- Glue: if for each η, `|s_n(d) − s_n(d′)| ≤ τ_n + C·K(η)·dist(d, d′) + 2Nη` (K = Keta), then
RegularityStep.equicontinuous_of_small_field gives the equicontinuity form of Theorem W. -/
theorem equicontinuous_from_Keta {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (s : ℕ → X → ℝ) (τn : ℕ → ℝ) (hτ : Tendsto τn atTop (nhds 0)) (C N : ℝ) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (κ τ ℓ a : ℝ) (rη : ℝ → ℝ) (k₀ : ℕ) (hκ : 0 ≤ κ)
    (hpos : ∀ η > 0, 0 ≤ τ + (ℓ + 2 * a * rη η))
    (hstep : ∀ η > 0, ∀ n, ∀ d ∈ D, ∀ d' ∈ D,
      |s n d - s n d'| ≤ τn n + C * Keta κ τ ℓ a rη k₀ η * dist d d' + 2 * N * η) :
    ∀ ε > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ ε :=
  RegularityStep.equicontinuous_of_small_field D s τn hτ C N hC hN fun η hη =>
    ⟨Keta κ τ ℓ a rη k₀ η, Keta_nonneg κ τ ℓ a rη k₀ η hκ (hpos η hη), hstep η hη⟩

#print axioms lipschitz_on_ball
#print axioms Keta_nonneg
#print axioms Keta_le
#print axioms expectation_from_nontree
#print axioms expectation_Keta
#print axioms equicontinuous_from_Keta

end RegularityConstant

namespace RegularityRadius

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 1. η ↔ (y_h, θ) -/

/-- If the two-step event has mass `≥ 1 − X` and `X ≤ ofReal η`, the complement has (real) probability ≤ η. -/
theorem compl_real_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Set Ω) (hG : MeasurableSet G) (X : ℝ≥0∞) (η : ℝ) (hη : 0 ≤ η)
    (hmass : 1 - X ≤ μ G) (hX : X ≤ ENNReal.ofReal η) : μ.real Gᶜ ≤ η := by
  have h1 : 1 ≤ μ G + X := tsub_le_iff_right.mp hmass
  have h2 : 1 ≤ μ G + ENNReal.ofReal η := le_trans h1 (add_le_add le_rfl hX)
  have h3 : μ Gᶜ ≤ ENNReal.ofReal η := by
    rw [prob_compl_eq_one_sub hG]; exact tsub_le_iff_left.mpr h2
  have h4 : (μ Gᶜ).toReal ≤ η := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rwa [ENNReal.toReal_ofReal hη] at this
  simpa [Measure.real] using h4

/-- Glue: for the event of TwoStageSmallField.small_field_two_stage_box, if `n_box[n_p P₁ + n_pt S] ≤ ofReal η`,
the complement has probability ≤ η. -/
theorem two_stage_compl_le {Ω ι Pl Pt : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : Finset ι)
    (plaq : ι → Finset Pl) (pts : ι → Finset Pt) (Y : Pl → Ω → ℝ) (f : Pt → Ω → ℝ)
    (yh θ : ℝ) (P₁ S : ℝ≥0∞) (nbox np npt : ℕ) (hR : R.card ≤ nbox)
    (hnp : ∀ i ∈ R, (plaq i).card ≤ np) (hnpt : ∀ i ∈ R, (pts i).card ≤ npt)
    (hY : ∀ i ∈ R, ∀ p ∈ plaq i, μ {ω | yh < Y p ω} ≤ P₁)
    (hf : ∀ i ∈ R, ∀ x ∈ pts i, μ {ω | θ < f x ω} ≤ S)
    (hGm : MeasurableSet {ω | ∀ i ∈ R, (∀ p ∈ plaq i, Y p ω ≤ yh) ∧ (∀ x ∈ pts i, f x ω ≤ θ)})
    (η : ℝ) (hη : 0 ≤ η) (heta : (nbox : ℝ≥0∞) * (np * P₁ + npt * S) ≤ ENNReal.ofReal η) :
    μ.real {ω | ∀ i ∈ R, (∀ p ∈ plaq i, Y p ω ≤ yh) ∧ (∀ x ∈ pts i, f x ω ≤ θ)}ᶜ ≤ η :=
  compl_real_le μ _ hGm _ η hη
    (TwoStageSmallField.small_field_two_stage_box μ R plaq pts Y f yh θ P₁ S nbox np npt hR hnp hnpt
      hY hf) heta

/-! ## 2. Form of the radius -/

/-- r(y_h, θ) = C_θ θ + C_y y_h/β (the assumed form (P-geom)). -/
noncomputable def radius (Cθ Cy β yh θ : ℝ) : ℝ := Cθ * θ + Cy * yh / β

/-! ## 3. Amplification -/

/-- Amplification < 1 ⇔ r < (1 − τ − ℓ′)/(2a) (ℓ′ = ℓ/u). -/
theorem amp_lt_one_iff (τ ℓ' a r : ℝ) (ha : 0 < a) :
    τ + (ℓ' + 2 * a * r) < 1 ↔ r < (1 - τ - ℓ') / (2 * a) := by
  rw [lt_div_iff₀ (by positivity)]; constructor <;> intro h <;> linarith

/-- Numerical values: if τ ≤ 0.6953, 0 ≤ ℓ ≤ 0.36, u ≥ 7, 0 ≤ r ≤ 0.029, then the amplification `τ + ℓ/u + 2·4.3348·r < 1`. -/
theorem amp_lt_one_numbers (τ ℓ u r : ℝ) (hτ : τ ≤ 0.6953) (hℓ : ℓ ≤ 0.36)
    (hu : 7 ≤ u) (hr : r ≤ 0.029) : τ + (ℓ / u + 2 * 4.3348 * r) < 1 := by
  have hu0 : 0 < u := by linarith
  have h1 : ℓ / u ≤ 0.36 / 7 := by
    calc ℓ / u ≤ 0.36 / u := div_le_div_of_nonneg_right hℓ hu0.le
      _ ≤ 0.36 / 7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu
  have h2 : (0.6953 : ℝ) + (0.36 / 7 + 2 * 4.3348 * 0.029) < 1 := by norm_num
  nlinarith

/-- The window radius κ/(4a) lies within 0.029 (if τ ≥ 0.678, ℓ ≥ 0, u > 0, then κ/(4a) ≤ 0.0186). -/
theorem window_radius_inside (τ ℓ u : ℝ) (hτ : 0.678 ≤ τ) (hℓ : 0 ≤ ℓ) (hu : 0 < u) :
    (1 - τ - ℓ / u) / (4 * 4.3348) ≤ 0.029 := by
  have : 0 ≤ ℓ / u := div_nonneg hℓ hu.le
  rw [div_le_iff₀ (by norm_num)]; linarith

/-- For η whose radius is ≤ 0.029, K(η) ≤ κ. -/
theorem Keta_uniform (κ τ ℓ u Cθ Cy β : ℝ) (yhη θη : ℝ → ℝ) (k₀ : ℕ) (η : ℝ) (hκ : 0 ≤ κ)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 0.6953) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 0.36) (hu : 7 ≤ u)
    (hr0 : 0 ≤ radius Cθ Cy β (yhη η) (θη η)) (hr : radius Cθ Cy β (yhη η) (θη η) ≤ 0.029) :
    RegularityConstant.Keta κ τ (ℓ / u) 4.3348 (fun η => radius Cθ Cy β (yhη η) (θη η)) k₀ η ≤ κ := by
  have hu0 : 0 < u := by linarith
  have hpos : 0 ≤ τ + (ℓ / u + 2 * 4.3348 * radius Cθ Cy β (yhη η) (θη η)) := by
    have := div_nonneg hℓ0 hu0.le; positivity
  exact RegularityConstant.Keta_le κ τ (ℓ / u) 4.3348 _ k₀ η hκ hpos
    (amp_lt_one_numbers τ ℓ u _ hτ hℓ hu hr).le

/-! ## 4. Expectations and equicontinuity -/

/-- η-form of the difference of expectations: replace `2|I| μ(Gᶜ)` in RegularityConstant.expectation_Keta by `2|I| η`. -/
theorem expectation_eta (A Bv m η : ℝ) (hm : m ≤ η) (hc : 0 ≤ Bv)
    (h : A ≤ Bv * m + 0) : A ≤ Bv * η := by nlinarith

/-- Equicontinuity: if for each η > 0 the radius is ≤ 0.029 and `|s_n(d) − s_n(d′)| ≤ τ_n + C·K(η)·dist + 2Nη`,
then the equicontinuity form of Theorem W holds (K(η) a function of the radius). -/
theorem equicontinuous_two_stage {X : Type*} [PseudoMetricSpace X] (D : Set X)
    (s : ℕ → X → ℝ) (τn : ℕ → ℝ) (hτn : Tendsto τn atTop (nhds 0)) (C N : ℝ) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (κ τ ℓ u Cθ Cy β : ℝ) (yhη θη : ℝ → ℝ) (k₀ : ℕ) (hκ : 0 ≤ κ)
    (hτ0 : 0 ≤ τ) (hℓ0 : 0 ≤ ℓ) (hu : 7 ≤ u)
    (hr0 : ∀ η > 0, 0 ≤ radius Cθ Cy β (yhη η) (θη η))
    (hstep : ∀ η > 0, ∀ n, ∀ d ∈ D, ∀ d' ∈ D,
      |s n d - s n d'| ≤ τn n + C * RegularityConstant.Keta κ τ (ℓ / u) 4.3348
        (fun η => radius Cθ Cy β (yhη η) (θη η)) k₀ η * dist d d' + 2 * N * η) :
    ∀ ε > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ ε := by
  have hu0 : 0 < u := by linarith
  exact RegularityConstant.equicontinuous_from_Keta D s τn hτn C N hC hN κ τ (ℓ / u) 4.3348
    (fun η => radius Cθ Cy β (yhη η) (θη η)) k₀ hκ
    (fun η hη => by have := div_nonneg hℓ0 hu0.le; have := hr0 η hη; positivity) hstep

#print axioms compl_real_le
#print axioms two_stage_compl_le
#print axioms amp_lt_one_iff
#print axioms amp_lt_one_numbers
#print axioms window_radius_inside
#print axioms Keta_uniform
#print axioms expectation_eta
#print axioms equicontinuous_two_stage

end RegularityRadius
