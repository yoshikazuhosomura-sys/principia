/-
Reading reflection positivity as a condition on the support of observables rather than on the blocking factor.
Single file; checks with `import Mathlib` only.

  §0 Copy of §2–§4 and the block-variable part of §8 of WeakUltravioletExistence (unchanged up to comments).
  §1 Support (dependence set): support of the pull-back from coordinatewise locality and the support of the observable;
     addition of reach in terms of heights; once the support is fixed, factorisation through restriction
     (the form of pullback_mem_positive).
  §2 Scale arithmetic: the sum of reaches for blocking factor 2, Σ d·ℓ₀/2^(m+k) ≤ 2d·ℓ₀/2^m;
     from the condition 4d ≤ 2^{m₀} on m₀, 2d·ℓ_{m+m₀} ≤ ℓ_m/2.
  §3 Finite lattice: reflection positivity of the push-forward measure for coarse observables whose fine support lies on
     the positive side of the plane.
  §4 Reading every other step: assuming reflection positivity only on a cofinal set of scales (e.g. even steps),
     from B∘Θ = Θ∘B and the pull-back preserving the positive side, reflection positivity at all scales
     (BlockConclusion) is recovered in the limit.
  §5 #print axioms

No specific lattice shape, Wilson action or family of paths is used. These enter as premises: "coordinatewise
dependence sets", "heights" and "reflection positivity at the fine lattice points".
-/
import Mathlib

/-! ## 0. Copy of WeakUltravioletExistence (unchanged up to comments) -/
namespace WeakUltravioletExistence

open Filter Topology MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 2. Sequences of probability measures on a compact configuration space -/

section Measures

variable {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E] [BorelSpace E]

/-- A sequence of probability measures on a compact metric space has a weakly convergent subsequence
(Prokhorov in the compact case; the limit is a probability measure). -/
theorem exists_subseq_tendsto_probabilityMeasure (ν : ℕ → ProbabilityMeasure E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νl : ProbabilityMeasure E,
      Tendsto (ν ∘ φ) atTop (𝓝 νl) := by
  obtain ⟨a, -, φ, hφ, h⟩ := isCompact_univ.tendsto_subseq (x := ν) (fun _ => mem_univ _)
  exact ⟨φ, hφ, a, h⟩

end Measures

/-! ## 3. A common subsequence at all coarse scales (projective system) -/

section Projective

variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)] [∀ m, MetricSpace (E m)]
  [∀ m, CompactSpace (E m)] [∀ m, BorelSpace (E m)]

/-- From sequences of measures `ν n m` on the coarse configuration spaces `E m` at each scale `m` (the lattice-`n` measure pushed forward
to the block variables at scale `m`), one can extract a subsequence common to all `m`. -/
theorem exists_common_subseq (ν : ℕ → ∀ m, ProbabilityMeasure (E m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νl : ∀ m, ProbabilityMeasure (E m),
      ∀ m, Tendsto (fun k => ν (φ k) m) atTop (𝓝 (νl m)) := by
  obtain ⟨a, -, φ, hφ, h⟩ := isCompact_univ.tendsto_subseq (x := ν) (fun _ => mem_univ _)
  exact ⟨φ, hφ, a, fun m => ((continuous_apply m).tendsto a).comp h⟩

/-- If the coarsening maps `B m : E (m+1) → E m` are continuous and the push-forwards are consistent on fine enough lattices
(pushing forward by `B m` gives the measure at the next coarser scale), the subsequential limits are also consistent. -/
theorem limit_consistent (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (hcons : ∀ m, ∀ᶠ n in atTop,
      (ν n (m + 1)).map (hB m).measurable.aemeasurable = ν n m)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (νl : ∀ m, ProbabilityMeasure (E m))
    (hlim : ∀ m, Tendsto (fun k => ν (φ k) m) atTop (𝓝 (νl m))) :
    ∀ m, (νl (m + 1)).map (hB m).measurable.aemeasurable = νl m := by
  intro m
  have h1 : Tendsto (fun k => (ν (φ k) (m + 1)).map (hB m).measurable.aemeasurable) atTop
      (𝓝 ((νl (m + 1)).map (hB m).measurable.aemeasurable)) :=
    ((ProbabilityMeasure.continuous_map (hB m)).tendsto _).comp (hlim (m + 1))
  have hev : ∀ᶠ k in atTop,
      ν (φ k) m = (ν (φ k) (m + 1)).map (hB m).measurable.aemeasurable :=
    (hφ.tendsto_atTop.eventually (hcons m)).mono (fun k hk => hk.symm)
  have h2 : Tendsto (fun k => (ν (φ k) (m + 1)).map (hB m).measurable.aemeasurable) atTop
      (𝓝 (νl m)) := (hlim m).congr' hev
  exact tendsto_nhds_unique h1 h2

end Projective

/-! ## 4. Closed conditions survive the limit (measure level) -/

section ClosedConditions

variable {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E] [BorelSpace E]

/-- Reflection positivity: if the reflection `Θ` is continuous and `∫ F(Θω) F(ω) ≥ 0` on each lattice for all `F` in the family `A`
of positive-time observables, the same holds for the weak limit. -/
theorem reflection_positivity_limit (Θ : E → E) (hΘ : Continuous Θ)
    (A : Set (BoundedContinuousFunction E ℝ))
    (ν : ℕ → ProbabilityMeasure E) (νl : ProbabilityMeasure E)
    (hlim : Tendsto ν atTop (𝓝 νl))
    (hRP : ∀ᶠ n in atTop, ∀ F ∈ A, 0 ≤ ∫ ω, F (Θ ω) * F ω ∂(ν n : Measure E)) :
    ∀ F ∈ A, 0 ≤ ∫ ω, F (Θ ω) * F ω ∂(νl : Measure E) := by
  intro F hF
  set G : BoundedContinuousFunction E ℝ := F.compContinuous ⟨Θ, hΘ⟩ * F
  have hG : ∀ ω, G ω = F (Θ ω) * F ω := fun ω => rfl
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) G
  simp only [hG] at ht
  exact ge_of_tendsto ht (hRP.mono fun n hn => hn F hF)

/-- Approximate symmetry: for a continuous map `g`, if for each observable `f`
`|∫ f∘g dν_n − ∫ f dν_n| ≤ ε_n(f)` with `ε_n(f) → 0`, the limit is invariant under `g`
(`ε = 0` is the case of an exact lattice symmetry). -/
theorem approx_invariance_limit (g : E → E) (hg : Continuous g)
    (ν : ℕ → ProbabilityMeasure E) (νl : ProbabilityMeasure E)
    (hlim : Tendsto ν atTop (𝓝 νl))
    (ε : ℕ → BoundedContinuousFunction E ℝ → ℝ)
    (hε : ∀ f, Tendsto (fun n => ε n f) atTop (𝓝 0))
    (hsym : ∀ᶠ n in atTop, ∀ f,
      |∫ ω, f (g ω) ∂(ν n : Measure E) - ∫ ω, f ω ∂(ν n : Measure E)| ≤ ε n f) :
    ∀ f : BoundedContinuousFunction E ℝ,
      ∫ ω, f (g ω) ∂(νl : Measure E) = ∫ ω, f ω ∂(νl : Measure E) := by
  intro f
  set fg : BoundedContinuousFunction E ℝ := f.compContinuous ⟨g, hg⟩
  have hfg : ∀ ω, fg ω = f (g ω) := fun ω => rfl
  have t1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) fg
  have t2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  simp only [hfg] at t1
  have td := (t1.sub t2).abs
  have hle : |∫ ω, f (g ω) ∂(νl : Measure E) - ∫ ω, f ω ∂(νl : Measure E)| ≤ 0 :=
    le_of_tendsto_of_tendsto td (hε f) (hsym.mono fun n hn => hn f)
  have := abs_nonpos_iff.mp hle
  linarith

/-- Lower bounds on probabilities of closed sets survive the limit (the small-field event does not collapse in the limit). -/
theorem closed_mass_lower_limit (C : Set E) (hC : IsClosed C) (c : ℝ≥0∞)
    (ν : ℕ → ProbabilityMeasure E) (νl : ProbabilityMeasure E)
    (hlim : Tendsto ν atTop (𝓝 νl))
    (hlow : ∀ᶠ n in atTop, c ≤ (ν n : Measure E) C) :
    c ≤ (νl : Measure E) C := by
  have h := MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hC
  have h1 : c ≤ limsup (fun n => (ν n : Measure E) C) atTop :=
    le_limsup_of_frequently_le hlow.frequently (by isBoundedDefault)
  exact h1.trans (by simpa using h)

end ClosedConditions

/-! ## 5. Observable level: subsequence on a dense set and continuous extension -/

/-! ## 8. Assembly: from the premise structure to the conclusion structure -/

section AssemblyBlocks

variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)] [∀ m, MetricSpace (E m)]
  [∀ m, CompactSpace (E m)] [∀ m, BorelSpace (E m)]

/-- Premises at the block-variable level (all lattice properties, for each lattice spacing).
`ν n m` is the lattice-`n` measure pushed forward to block variables at scale `m`, `B m` the coarsening map,
`Θ m` the time reflection at scale `m`, `A m` the positive-time observables, `act g m` the lattice symmetries
(hypercubic group and coarse-lattice translations), `C m` the small-field event (a closed set), `c m` the lower bound on its probability. -/
structure BlockHypotheses (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {G : Type*} (act : G → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞) : Prop where
  consistent : ∀ m, ∀ᶠ n in atTop, (ν n (m + 1)).map (hB m).measurable.aemeasurable = ν n m
  reflection_continuous : ∀ m, Continuous (Θ m)
  reflection_positive : ∀ m, ∀ᶠ n in atTop,
    ∀ F ∈ A m, 0 ≤ ∫ ω, F (Θ m ω) * F ω ∂(ν n m : Measure (E m))
  symmetry_continuous : ∀ g m, Continuous (act g m)
  symmetric : ∀ g m, ∀ᶠ n in atTop, ∀ f : BoundedContinuousFunction (E m) ℝ,
    ∫ ω, f (act g m ω) ∂(ν n m : Measure (E m)) = ∫ ω, f ω ∂(ν n m : Measure (E m))
  small_field_closed : ∀ m, IsClosed (C m)
  small_field_mass : ∀ m, ∀ᶠ n in atTop, c m ≤ (ν n m : Measure (E m)) (C m)

/-- Conclusion at the block-variable level: the limiting projective system is consistent, reflection positive, invariant under
the lattice symmetries, and keeps the lower bound on the probability of the small-field event. -/
structure BlockConclusion (νl : ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {G : Type*} (act : G → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞) : Prop where
  consistent : ∀ m, (νl (m + 1)).map (hB m).measurable.aemeasurable = νl m
  reflection_positive : ∀ m, ∀ F ∈ A m, 0 ≤ ∫ ω, F (Θ m ω) * F ω ∂(νl m : Measure (E m))
  symmetric : ∀ g m, ∀ f : BoundedContinuousFunction (E m) ℝ,
    ∫ ω, f (act g m ω) ∂(νl m : Measure (E m)) = ∫ ω, f ω ∂(νl m : Measure (E m))
  small_field_mass : ∀ m, c m ≤ (νl m : Measure (E m)) (C m)

/-- Skeleton of the implication (block-variable level): from the premise structure, a subsequence common to all scales and a
limiting projective system satisfying the conclusion structure. -/
theorem weak_uv_block_skeleton (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {G : Type*} (act : G → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞)
    (H : BlockHypotheses ν B hB Θ A act C c) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νl : ∀ m, ProbabilityMeasure (E m),
      (∀ m, Tendsto (fun k => ν (φ k) m) atTop (𝓝 (νl m))) ∧
      BlockConclusion νl B hB Θ A act C c := by
  obtain ⟨φ, hφ, νl, hlim⟩ := exists_common_subseq ν
  have ev : ∀ {P : ℕ → Prop}, (∀ᶠ n in atTop, P n) → ∀ᶠ k in atTop, P (φ k) :=
    fun h => hφ.tendsto_atTop.eventually h
  refine ⟨φ, hφ, νl, hlim, ?_, ?_, ?_, ?_⟩
  · exact limit_consistent ν B hB H.consistent φ hφ νl hlim
  · intro m
    exact reflection_positivity_limit (Θ m) (H.reflection_continuous m) (A m)
      (fun k => ν (φ k) m) (νl m) (hlim m) (ev (H.reflection_positive m))
  · intro g m
    refine approx_invariance_limit (act g m) (H.symmetry_continuous g m)
      (fun k => ν (φ k) m) (νl m) (hlim m) (fun _ _ => 0) (fun _ => tendsto_const_nhds) ?_
    exact (ev (H.symmetric g m)).mono fun k hk f => by rw [hk f, sub_self, abs_zero]
  · intro m
    exact closed_mass_lower_limit (C m) (H.small_field_closed m) (c m)
      (fun k => ν (φ k) m) (νl m) (hlim m) (ev (H.small_field_mass m))

end AssemblyBlocks

end WeakUltravioletExistence

namespace ReflectionSupportScale

open Filter Topology MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 1. Support (dependence set) -/

section Support

/-- `f` is determined by the values of the configuration `ω : L → α` on the set `S`. -/
def DependsOn {L α β : Type*} (S : Set L) (f : (L → α) → β) : Prop :=
  ∀ ω ω' : L → α, (∀ l ∈ S, ω l = ω' l) → f ω = f ω'

theorem DependsOn.mono {L α β : Type*} {S T : Set L} {f : (L → α) → β}
    (h : DependsOn S f) (hST : S ⊆ T) : DependsOn T f :=
  fun ω ω' hω => h ω ω' (fun l hl => hω l (hST hl))

/-- Support of the pull-back: if each coordinate `b` of the map `V` is determined by `N b` and the coarse observable `F`
is determined by `Sc`, then `F ∘ V` is determined by `⋃_{b ∈ Sc} N b`. -/
theorem dependsOn_comp {L Lc α γ β : Type*} (V : (L → α) → (Lc → γ)) (N : Lc → Set L)
    (hV : ∀ b, DependsOn (N b) (fun ω => V ω b)) (Sc : Set Lc) (F : (Lc → γ) → β)
    (hF : DependsOn Sc F) :
    DependsOn (⋃ b ∈ Sc, N b) (fun ω => F (V ω)) := by
  intro ω ω' hω
  apply hF
  intro b hb
  apply hV b
  intro l hl
  exact hω l (Set.mem_biUnion hb hl)

/-- Height form. Fine link `l` has height `h l`, coarse link `b` has height `hc b` (both the minimum of the coordinate in
the reflection direction). If each coordinate is determined by fine links from its own height down to `R` below, `F`
is determined by coarse links of height ≥ `P + g`, and `R ≤ g`, then `F ∘ V` is determined on the positive side
of the plane `P` (height `≥ P`). -/
theorem dependsOn_positive_of_gap {L Lc α γ β : Type*} (h : L → ℝ) (hc : Lc → ℝ)
    (V : (L → α) → (Lc → γ)) (R : ℝ)
    (hV : ∀ b, DependsOn {l | hc b - R ≤ h l} (fun ω => V ω b))
    (F : (Lc → γ) → β) (P g : ℝ) (hF : DependsOn {b | P + g ≤ hc b} F) (hRg : R ≤ g) :
    DependsOn {l | P ≤ h l} (fun ω => F (V ω)) := by
  refine (dependsOn_comp V (fun b => {l | hc b - R ≤ h l}) hV _ F hF).mono ?_
  intro l hl
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hl
  obtain ⟨b, hb, hlb⟩ := hl
  show P ≤ h l
  linarith

/-- Addition of reach (type (B5)): if each coordinate of the step one `V₁` (fine → intermediate) is determined down to
height `R₁` below and each coordinate of step two `V₂` (intermediate → coarse) down to `R₂` below, then each
coordinate of the composition is determined down to `R₁ + R₂` below. -/
theorem dependsOn_reach_comp {L Lm Lc α γ δ : Type*} (h : L → ℝ) (hm : Lm → ℝ) (hc : Lc → ℝ)
    (V₁ : (L → α) → (Lm → γ)) (V₂ : (Lm → γ) → (Lc → δ)) (R₁ R₂ : ℝ)
    (h₁ : ∀ b, DependsOn {l | hm b - R₁ ≤ h l} (fun ω => V₁ ω b))
    (h₂ : ∀ c, DependsOn {b | hc c - R₂ ≤ hm b} (fun ω => V₂ ω c)) :
    ∀ c, DependsOn {l | hc c - (R₁ + R₂) ≤ h l} (fun ω => V₂ (V₁ ω) c) := by
  intro c
  have := dependsOn_positive_of_gap h hm V₁ R₁ h₁ (fun ω => V₂ ω c) (hc c - (R₁ + R₂)) R₁
    (by
      intro ω ω' hω
      apply h₂ c
      intro b hb
      exact hω b (by simp only [Set.mem_ofPred_eq] at hb ⊢; linarith))
    le_rfl
  exact this

/-- Once the support is fixed, factorisation through restriction (it enters the set
`{f | ∃ φ, ∀ ω, f ω = φ (πp ω)}` of `LatticeBlockReflection.pullback_mem_positive` with `πp` the restriction to `S`). -/
theorem exists_factor_of_dependsOn {L α β : Type*} [Inhabited α] (S : Set L)
    (f : (L → α) → β) (hf : DependsOn S f) :
    f ∈ {f : (L → α) → β | ∃ φ : (S → α) → β, ∀ ω, f ω = φ (fun l => ω l)} := by
  classical
  refine ⟨fun r => f (fun l => if hl : l ∈ S then r ⟨l, hl⟩ else default), fun ω => ?_⟩
  apply hf
  intro l hl
  simp [hl]

end Support

/-! ## 2. Scale arithmetic (blocking factor 2) -/

section Scales

/-- Sum of reaches for blocking factor 2: if the downward overhang of one step at step `m+k` is `d · ℓ₀ / 2^(m+k)`
(`d` in units of the coarse spacing), then however many steps are composed the sum is ≤ `2 d ℓ₀ / 2^m`. -/
theorem reach_sum_le (d ℓ₀ : ℝ) (hd : 0 ≤ d) (hℓ : 0 ≤ ℓ₀) (m N : ℕ) :
    ∑ k ∈ Finset.range N, d * (ℓ₀ / 2 ^ (m + k)) ≤ 2 * d * ℓ₀ / 2 ^ m := by
  have e : ∀ k, d * (ℓ₀ / 2 ^ (m + k)) = (d * ℓ₀ / 2 ^ m) * (1 / 2) ^ k := by
    intro k
    rw [pow_add, one_div_pow]
    field_simp
  simp_rw [e]
  rw [← Finset.mul_sum]
  have hg := sum_geometric_two_le N
  have hc : 0 ≤ d * ℓ₀ / 2 ^ m := by positivity
  calc d * ℓ₀ / 2 ^ m * ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i ≤ d * ℓ₀ / 2 ^ m * 2 :=
        mul_le_mul_of_nonneg_left hg hc
    _ = 2 * d * ℓ₀ / 2 ^ m := by ring

/-- Condition on m₀: if `4 d ≤ 2^{m₀}`, the multi-step reach bound `2 d ℓ_{m+m₀}` at step `m + m₀` is ≤
`ℓ_m / 2`, the distance from a half-integer plane of the coarse lattice at step `m` to the nearest layer. -/
theorem reach_le_half_of_m0 (d ℓ₀ : ℝ) (hℓ : 0 ≤ ℓ₀) (m m₀ : ℕ) (h4 : 4 * d ≤ 2 ^ m₀) :
    2 * d * ℓ₀ / 2 ^ (m + m₀) ≤ ℓ₀ / 2 ^ m / 2 := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hq : (0 : ℝ) < 2 ^ m₀ := by positivity
  rw [pow_add, div_le_iff₀ (by positivity), div_div]
  have : ℓ₀ / (2 ^ m * 2) * (2 ^ m * 2 ^ m₀) = ℓ₀ * 2 ^ m₀ / 2 := by
    field_simp
  rw [this]
  nlinarith

/-- Combined form: with one-step overhang `d` (units of the coarse spacing) and `4 d ≤ 2^{m₀}`, any composition from step
`m + m₀` down to the fine lattice has reach ≤ `ℓ_m / 2`. -/
theorem reach_total_le_half (d ℓ₀ : ℝ) (hd : 0 ≤ d) (hℓ : 0 ≤ ℓ₀) (m m₀ N : ℕ)
    (h4 : 4 * d ≤ 2 ^ m₀) :
    ∑ k ∈ Finset.range N, d * (ℓ₀ / 2 ^ (m + m₀ + k)) ≤ ℓ₀ / 2 ^ m / 2 :=
  (reach_sum_le d ℓ₀ hd hℓ (m + m₀) N).trans (reach_le_half_of_m0 d ℓ₀ hℓ m m₀ h4)

/-- Examples of m₀ for the overhang: `d = 1/2` (symmetric closure of cov and mixing) gives `m₀ = 1`; `d = 1` (symmetric
closure of the flux) gives `m₀ = 2`; `d = 2` (closure of vertical length 4) gives `m₀ = 3`. -/
theorem m0_examples : 4 * (1 / 2 : ℝ) ≤ 2 ^ 1 ∧ 4 * (1 : ℝ) ≤ 2 ^ 2 ∧ 4 * (2 : ℝ) ≤ 2 ^ 3 := by
  norm_num

/-- For closures with blocking factor 2 (`d ≥ 1/2`), the condition `m₀ = 0` (RP directly at the nearest layer) fails. -/
theorem m0_zero_fails (d : ℝ) (hd : 1 / 2 ≤ d) : ¬ (4 * d ≤ 2 ^ 0) := by
  norm_num; linarith

end Scales

/-! ## 3. Finite lattice: reflection positivity for observables with fine support on the positive side -/

section FiniteLattice

variable {L Lc α γ : Type*} [MeasurableSpace (L → α)] [MeasurableSpace (Lc → γ)]

/-- Assume reflection positivity at the fine lattice points for all functions determined on the positive side of the
plane `P`. If the block map `V` commutes with reflection, each coordinate is determined down to `R` below its height,
and the coarse observable `F` is determined at heights ≥ `P + g` (`R ≤ g`), then for the push-forward measure
`∫ F(Θ' e) F(e) ≥ 0`. -/
theorem coarse_rp_of_gap (μ : Measure (L → α)) (Θ : (L → α) → (L → α))
    (Θ' : (Lc → γ) → (Lc → γ)) (V : (L → α) → (Lc → γ)) (hV : Measurable V)
    (hΘ' : Measurable Θ') (hcomm : ∀ ω, V (Θ ω) = Θ' (V ω))
    (h : L → ℝ) (hc : Lc → ℝ) (P : ℝ)
    (hRP : ∀ f : (L → α) → ℝ, DependsOn {l | P ≤ h l} f → 0 ≤ ∫ ω, f (Θ ω) * f ω ∂μ)
    (R g : ℝ) (hloc : ∀ b, DependsOn {l | hc b - R ≤ h l} (fun ω => V ω b))
    (F : (Lc → γ) → ℝ) (hF : Measurable F) (hFs : DependsOn {b | P + g ≤ hc b} F)
    (hRg : R ≤ g) :
    0 ≤ ∫ e, F (Θ' e) * F e ∂(μ.map V) := by
  rw [integral_map (f := fun e => F (Θ' e) * F e) hV.aemeasurable
    ((hF.comp hΘ').mul hF).aestronglyMeasurable]
  have := hRP _ (dependsOn_positive_of_gap h hc V R hloc F P g hFs hRg)
  simp only [hcomm] at this
  exact this

/-- "Physical support" form: if positive-time observables are defined via the support of `F ∘ V`, no condition on reach
or blocking factor is needed. -/
theorem coarse_rp_of_fine_support (μ : Measure (L → α)) (Θ : (L → α) → (L → α))
    (Θ' : (Lc → γ) → (Lc → γ)) (V : (L → α) → (Lc → γ)) (hV : Measurable V)
    (hΘ' : Measurable Θ') (hcomm : ∀ ω, V (Θ ω) = Θ' (V ω))
    (Spos : Set L)
    (hRP : ∀ f : (L → α) → ℝ, DependsOn Spos f → 0 ≤ ∫ ω, f (Θ ω) * f ω ∂μ)
    (F : (Lc → γ) → ℝ) (hF : Measurable F) (hFs : DependsOn Spos (fun ω => F (V ω))) :
    0 ≤ ∫ e, F (Θ' e) * F e ∂(μ.map V) := by
  rw [integral_map (f := fun e => F (Θ' e) * F e) hV.aemeasurable
    ((hF.comp hΘ').mul hF).aestronglyMeasurable]
  have := hRP _ hFs
  simp only [hcomm] at this
  exact this

end FiniteLattice

/-! ## 4. Reading every other step: from reflection positivity on cofinal scales to all scales -/

section Cofinal

variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)] [∀ m, MetricSpace (E m)]
  [∀ m, CompactSpace (E m)] [∀ m, BorelSpace (E m)]

open WeakUltravioletExistence

/-- From reflection positivity at one finer scale to reflection positivity at the next coarser scale (for measures
consistent under push-forward). Uses `B m ∘ Θ (m+1) = Θ m ∘ B m` and that the pull-back of a positive-side
observable is on the positive side. -/
theorem rp_down (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    (hcomm : ∀ m ω, B m (Θ (m + 1) ω) = Θ m (B m ω))
    (hpull : ∀ m, ∀ F ∈ A m, F.compContinuous ⟨B m, hB m⟩ ∈ A (m + 1))
    (hΘc : ∀ m, Continuous (Θ m))
    (νl : ∀ m, ProbabilityMeasure (E m))
    (hcons : ∀ m, (νl (m + 1)).map (hB m).measurable.aemeasurable = νl m) (m : ℕ)
    (h1 : ∀ F ∈ A (m + 1), 0 ≤ ∫ ω, F (Θ (m + 1) ω) * F ω ∂(νl (m + 1) : Measure (E (m + 1)))) :
    ∀ F ∈ A m, 0 ≤ ∫ ω, F (Θ m ω) * F ω ∂(νl m : Measure (E m)) := by
  intro F hF
  have hG := h1 _ (hpull m F hF)
  rw [← hcons m, ProbabilityMeasure.toMeasure_map,
    integral_map (f := fun e => F (Θ m e) * F e) (hB m).measurable.aemeasurable
      (((F.continuous.comp (hΘc m)).mul F.continuous).aestronglyMeasurable)]
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at hG
  simp only [← hcomm m]
  exact hG

/-- Weakened premise structure: reflection positivity only on a (cofinal) set of scales `T`. Other fields as in
`BlockHypotheses`, plus commutation of reflection with the coarsening maps and the positive-side pull-back. -/
structure BlockHypothesesCofinal (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {G : Type*} (act : G → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞) (T : Set ℕ) : Prop where
  consistent : ∀ m, ∀ᶠ n in atTop, (ν n (m + 1)).map (hB m).measurable.aemeasurable = ν n m
  reflection_continuous : ∀ m, Continuous (Θ m)
  cofinal : ∀ m, ∃ m' ∈ T, m ≤ m'
  reflection_positive_on : ∀ m ∈ T, ∀ᶠ n in atTop,
    ∀ F ∈ A m, 0 ≤ ∫ ω, F (Θ m ω) * F ω ∂(ν n m : Measure (E m))
  reflection_comm : ∀ m ω, B m (Θ (m + 1) ω) = Θ m (B m ω)
  pullback_positive : ∀ m, ∀ F ∈ A m, F.compContinuous ⟨B m, hB m⟩ ∈ A (m + 1)
  symmetry_continuous : ∀ g m, Continuous (act g m)
  symmetric : ∀ g m, ∀ᶠ n in atTop, ∀ f : BoundedContinuousFunction (E m) ℝ,
    ∫ ω, f (act g m ω) ∂(ν n m : Measure (E m)) = ∫ ω, f ω ∂(ν n m : Measure (E m))
  small_field_closed : ∀ m, IsClosed (C m)
  small_field_mass : ∀ m, ∀ᶠ n in atTop, c m ≤ (ν n m : Measure (E m)) (C m)

/-- Skeleton of the implication (cofinal-scale version): the conclusion is the original `BlockConclusion`
(reflection positivity at all scales). -/
theorem weak_uv_block_skeleton_cofinal (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {G : Type*} (act : G → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞) (T : Set ℕ)
    (H : BlockHypothesesCofinal ν B hB Θ A act C c T) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νl : ∀ m, ProbabilityMeasure (E m),
      (∀ m, Tendsto (fun k => ν (φ k) m) atTop (𝓝 (νl m))) ∧
      BlockConclusion νl B hB Θ A act C c := by
  obtain ⟨φ, hφ, νl, hlim⟩ := exists_common_subseq ν
  have ev : ∀ {P : ℕ → Prop}, (∀ᶠ n in atTop, P n) → ∀ᶠ k in atTop, P (φ k) :=
    fun h => hφ.tendsto_atTop.eventually h
  have hcons := limit_consistent ν B hB H.consistent φ hφ νl hlim
  have hT : ∀ m ∈ T, ∀ F ∈ A m, 0 ≤ ∫ ω, F (Θ m ω) * F ω ∂(νl m : Measure (E m)) :=
    fun m hm => reflection_positivity_limit (Θ m) (H.reflection_continuous m) (A m)
      (fun k => ν (φ k) m) (νl m) (hlim m) (ev (H.reflection_positive_on m hm))
  -- Downward propagation: from m' ∈ T to m' − j
  have hdown : ∀ m' ∈ T, ∀ j, j ≤ m' →
      ∀ F ∈ A (m' - j), 0 ≤ ∫ ω, F (Θ (m' - j) ω) * F ω ∂(νl (m' - j) : Measure (E (m' - j))) := by
    intro m' hm' j
    induction j with
    | zero => intro _; simpa using hT m' hm'
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have e : m' - j = (m' - (j + 1)) + 1 := by omega
      rw [e] at h1
      exact rp_down B hB Θ A H.reflection_comm H.pullback_positive H.reflection_continuous
        νl hcons (m' - (j + 1)) h1
  refine ⟨φ, hφ, νl, hlim, hcons, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨m', hm', hle⟩ := H.cofinal m
    have := hdown m' hm' (m' - m) (by omega)
    have e : m' - (m' - m) = m := by omega
    rw [e] at this
    exact this
  · intro g m
    refine approx_invariance_limit (act g m) (H.symmetry_continuous g m)
      (fun k => ν (φ k) m) (νl m) (hlim m) (fun _ _ => 0) (fun _ => tendsto_const_nhds) ?_
    exact (ev (H.symmetric g m)).mono fun k hk f => by rw [hk f, sub_self, abs_zero]
  · intro m
    exact closed_mass_lower_limit (C m) (H.small_field_closed m) (c m)
      (fun k => ν (φ k) m) (νl m) (hlim m) (ev (H.small_field_mass m))

/-- The even steps are cofinal. -/
theorem even_cofinal : ∀ m : ℕ, ∃ m' ∈ {k : ℕ | Even k}, m ≤ m' :=
  fun m => ⟨2 * m, ⟨m, by ring⟩, by omega⟩

/-- The original premise (RP at all scales), with the commutation and pull-back fields added, is the special case
`T = univ` of the cofinal version. -/
theorem cofinal_of_all (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {G : Type*} (act : G → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞)
    (H : BlockHypotheses ν B hB Θ A act C c)
    (hcomm : ∀ m ω, B m (Θ (m + 1) ω) = Θ m (B m ω))
    (hpull : ∀ m, ∀ F ∈ A m, F.compContinuous ⟨B m, hB m⟩ ∈ A (m + 1)) :
    BlockHypothesesCofinal ν B hB Θ A act C c Set.univ :=
  { consistent := H.consistent, reflection_continuous := H.reflection_continuous,
    cofinal := fun m => ⟨m, Set.mem_univ _, le_rfl⟩,
    reflection_positive_on := fun m _ => H.reflection_positive m,
    reflection_comm := hcomm, pullback_positive := hpull,
    symmetry_continuous := H.symmetry_continuous, symmetric := H.symmetric,
    small_field_closed := H.small_field_closed, small_field_mass := H.small_field_mass }

end Cofinal

/-! ## 5. Axiom check -/

#print axioms DependsOn.mono
#print axioms dependsOn_comp
#print axioms dependsOn_positive_of_gap
#print axioms dependsOn_reach_comp
#print axioms exists_factor_of_dependsOn
#print axioms reach_sum_le
#print axioms reach_le_half_of_m0
#print axioms reach_total_le_half
#print axioms m0_examples
#print axioms m0_zero_fails
#print axioms coarse_rp_of_gap
#print axioms coarse_rp_of_fine_support
#print axioms rp_down
#print axioms weak_uv_block_skeleton_cofinal
#print axioms even_cofinal
#print axioms cofinal_of_all

end ReflectionSupportScale
