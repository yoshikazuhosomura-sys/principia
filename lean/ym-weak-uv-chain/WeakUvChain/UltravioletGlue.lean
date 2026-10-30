/-
Check of the glue between Theorem W and the chain: the bodies of `WeakUltravioletExistence.lean` and `UltravioletChain.lean`
are placed in one file (both unchanged up to comments; `#print axioms` collected at the end), and it is checked at the type
level that the conclusions of the chain theorem fit directly into the premise fields of Theorem W.
Single file; checks with `import Mathlib` only.
-/
import Mathlib

namespace WeakUltravioletExistence

open Filter Topology MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 1. Tuning the coupling (the bare-coupling lemma (W0)) -/

/-- the bare-coupling lemma (W0) (with domain). `u k x` is the effective inverse coupling `1/g_k²` after `k` steps, starting from the bare inverse coupling
`x = 1/g₀²`. Only inside the domain `{x | ∀ j ≤ k, u⋆ ≤ u j x}` (coupling ≤ `γ₁ = u⋆^{-1/2}` at all previous steps) do we assume
(S) the one-step remainder bound `u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2` and (C) continuity of `x ↦ u_{k+1} x`. For a target `t ≥ u⋆` and
number of steps `n` there is a bare inverse coupling `x` reaching exactly `t` after `n` steps, staying ≥ `t` at all intermediate steps,
with `t + (b/2)n ≤ x ≤ t + (3b/2)n` (one-loop type sandwich). -/
theorem exists_bare_inverse_coupling (u : ℕ → ℝ → ℝ) (b ustar t : ℝ) (n : ℕ)
    (hb : 0 < b) (h0 : ∀ x, u 0 x = x)
    (hS : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2)
    (hC : ∀ k, ContinuousOn (u (k + 1)) {x | ∀ j ≤ k, ustar ≤ u j x})
    (ht : ustar ≤ t) :
    ∃ x : ℝ, t + b / 2 * n ≤ x ∧ x ≤ t + 3 * b / 2 * n ∧ u n x = t ∧
      ∀ k ≤ n, t ≤ u k x := by
  -- sandwich for the sequence of steps (while inside the domain)
  have hdrop : ∀ x, ∀ k, (∀ j ≤ k, ustar ≤ u j x) →
      u k x ≤ x - b / 2 * k ∧ x - 3 * b / 2 * k ≤ u k x := by
    intro x k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hd
      have hd' : ∀ j ≤ k, ustar ≤ u j x := fun j hj => hd j (by omega)
      obtain ⟨i1, i2⟩ := ih hd'
      obtain ⟨s1, s2⟩ := hS k x hd'
      push_cast
      constructor <;> linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨t, by simp, by simp, h0 t, ?_⟩
    intro k hk
    have : k = 0 := by omega
    subst this; simp [h0]
  set a : ℝ := t + 3 * b / 2 * n with ha
  -- K_k: starting points in [t, a] that stay ≥ t up to step k
  let K : ℕ → Set ℝ := fun k => {x | x ∈ Icc t a ∧ ∀ j ≤ k, t ≤ u j x}
  have hKdom : ∀ k x, x ∈ K k → ∀ j ≤ k, ustar ≤ u j x :=
    fun k x hx j hj => le_trans ht (hx.2 j hj)
  have hKclosed : ∀ k, IsClosed (K k) := by
    intro k
    induction k with
    | zero =>
      have : K 0 = Icc t a := by
        ext x
        simp only [K, mem_ofPred_eq, mem_Icc]
        constructor
        · intro h; exact h.1
        · intro h
          refine ⟨h, fun j hj => ?_⟩
          have : j = 0 := by omega
          subst this; rw [h0]; exact h.1
      rw [this]; exact isClosed_Icc
    | succ k ih =>
      have hco : ContinuousOn (u (k + 1)) (K k) :=
        (hC k).mono (fun x hx => hKdom k x hx)
      have hset : K (k + 1) = K k ∩ u (k + 1) ⁻¹' Ici t := by
        ext x
        simp only [K, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, fun j hj => h2 j (by omega)⟩, h2 (k + 1) le_rfl⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun j hj => ?_⟩
          rcases Nat.lt_or_ge j (k + 1) with hlt | hge
          · exact h2 j (by omega)
          · have : j = k + 1 := by omega
            subst this; exact h3
      rw [hset]
      exact hco.preimage_isClosed_of_isClosed ih isClosed_Ici
  -- a lies in K n
  have hta : t ≤ a := by
    have : (0 : ℝ) ≤ 3 * b / 2 * n := by positivity
    linarith
  have ha_mem : a ∈ K n := by
    have key : ∀ k ≤ n, (∀ j ≤ k, t + 3 * b / 2 * ((n : ℝ) - j) ≤ u j a) := by
      intro k
      induction k with
      | zero => intro _ j hj; have : j = 0 := by omega
                subst this; simp [h0, ha]
      | succ k ih =>
        intro hk j hj
        rcases Nat.lt_or_ge j (k + 1) with hlt | hge
        · exact ih (by omega) j (by omega)
        · have : j = k + 1 := by omega
          subst this
          have ih' := ih (by omega)
          have hd : ∀ i ≤ k, ustar ≤ u i a := by
            intro i hi
            have h1 := ih' i hi
            have hin : (i : ℝ) ≤ n := by exact_mod_cast (show i ≤ n by omega)
            have : (0 : ℝ) ≤ 3 * b / 2 * ((n : ℝ) - i) := by
              apply mul_nonneg; positivity; linarith
            linarith
          have s1 := (hS k a hd).1
          have hk' := ih' k le_rfl
          push_cast
          linarith
    refine ⟨⟨hta, le_rfl⟩, fun j hj => ?_⟩
    have h1 := key n le_rfl j hj
    have hin : (j : ℝ) ≤ n := by exact_mod_cast hj
    have : (0 : ℝ) ≤ 3 * b / 2 * ((n : ℝ) - j) := by
      apply mul_nonneg; positivity; linarith
    linarith
  have hne : (K n).Nonempty := ⟨a, ha_mem⟩
  have hbdd : BddBelow (K n) := ⟨t, fun x hx => hx.1.1⟩
  set s := sInf (K n) with hs
  have hs_mem : s ∈ K n := (hKclosed n).csInf_mem hne hbdd
  have hsdom : ∀ j ≤ n, ustar ≤ u j s := hKdom n s hs_mem
  obtain ⟨d1, d2⟩ := hdrop s n hsdom
  -- u n s = t
  have hus : u n s = t := by
    by_contra hne'
    have hgt : t < u n s := lt_of_le_of_ne (hs_mem.2 n le_rfl) (Ne.symm hne')
    have hnpos : (0 : ℝ) < b / 2 * n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hst : t < s := by linarith
    -- strictly greater than t at every step
    have hall : ∀ k ≤ n, t < u k s := by
      intro k hk
      have mono : ∀ i, k + i ≤ n → u (k + i) s ≤ u k s := by
        intro i
        induction i with
        | zero => intro _; simp
        | succ i ih =>
          intro hi
          have h1 := ih (by omega)
          have h2 := (hS (k + i) s (fun j hj => hsdom j (by omega))).2
          rw [← Nat.add_assoc]
          linarith
      have := mono (n - k) (by omega)
      rw [Nat.add_sub_cancel' hk] at this
      linarith
    -- still greater than t near s (induction on the number of steps)
    have hopen : ∀ k ≤ n, ∃ ε > 0, ∀ y, dist y s < ε → ∀ j ≤ k, t < u j y := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨s - t, by linarith, fun y hy j hj => ?_⟩
        have : j = 0 := by omega
        subst this
        rw [h0]
        rw [Real.dist_eq, abs_lt] at hy
        linarith
      | succ k ih =>
        intro hk
        obtain ⟨ε, hε, hεy⟩ := ih (by omega)
        have hcw : ContinuousWithinAt (u (k + 1)) {x | ∀ j ≤ k, ustar ≤ u j x} s :=
          hC k s (fun j hj => hsdom j (by omega))
        rw [Metric.continuousWithinAt_iff] at hcw
        obtain ⟨ε', hε', hε'y⟩ := hcw (u (k + 1) s - t) (by linarith [hall (k + 1) hk])
        refine ⟨min ε ε', lt_min hε hε', fun y hy j hj => ?_⟩
        have hy1 : dist y s < ε := lt_of_lt_of_le hy (min_le_left _ _)
        have hy2 : dist y s < ε' := lt_of_lt_of_le hy (min_le_right _ _)
        rcases Nat.lt_or_ge j (k + 1) with hlt | hge
        · exact hεy y hy1 j (by omega)
        · have : j = k + 1 := by omega
          subst this
          have hydom : ∀ i ≤ k, ustar ≤ u i y := fun i hi => le_trans ht (hεy y hy1 i hi).le
          have := hε'y hydom hy2
          rw [Real.dist_eq, abs_lt] at this
          linarith
    obtain ⟨ε, hε, hεy⟩ := hopen n le_rfl
    set y := s - min (ε / 2) ((s - t) / 2) with hy
    have hm : 0 < min (ε / 2) ((s - t) / 2) := lt_min (by linarith) (by linarith)
    have hm1 : min (ε / 2) ((s - t) / 2) ≤ ε / 2 := min_le_left _ _
    have hm2 : min (ε / 2) ((s - t) / 2) ≤ (s - t) / 2 := min_le_right _ _
    have hyd : dist y s < ε := by
      rw [Real.dist_eq, hy]
      rw [abs_lt]; constructor <;> linarith
    have hyK : y ∈ K n := by
      refine ⟨⟨by linarith, by linarith [hs_mem.1.2]⟩, fun j hj => (hεy y hyd j hj).le⟩
    have := csInf_le hbdd hyK
    linarith
  refine ⟨s, ?_, ?_, hus, fun k hk => hs_mem.2 k hk⟩
  · linarith
  · linarith

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

section Observables

variable {X : Type*} [MetricSpace X]

/-- A uniformly bounded real-valued sequence on a countable set `D` has a subsequence converging at every point of `D`
(compactness of a countable product). -/
theorem exists_subseq_tendsto_on_countable (D : Set X) (hDc : D.Countable)
    (s : ℕ → X → ℝ) (Bd : ℝ) (hbd : ∀ n, ∀ d ∈ D, |s n d| ≤ Bd) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ T : D → ℝ,
      ∀ d : D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (T d)) := by
  have : Countable D := hDc.to_subtype
  let x : ℕ → (D → ℝ) := fun n d => s n d
  have hK : IsCompact (Set.univ.pi fun _ : D => Icc (-Bd) Bd) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hx : ∀ n, x n ∈ Set.univ.pi fun _ : D => Icc (-Bd) Bd := by
    intro n d _
    exact abs_le.mp (hbd n d d.2)
  obtain ⟨T, -, φ, hφ, h⟩ := hK.tendsto_subseq hx
  exact ⟨φ, hφ, T, fun d => ((continuous_apply d).tendsto T).comp h⟩

/-- If along a given subsequence `φ` the sequence converges at each point of `D` (limit `T`), and is uniformly bounded and
equicontinuous "on fine enough lattices", then `T` extends to a continuous `S` on all of `X`, with the same bound and the same modulus of continuity. -/
theorem continuous_extension_of_tendsto (D : Set X) (hDd : Dense D)
    (s : ℕ → X → ℝ) (Bd : ℝ) (hbd : ∀ n, ∀ d ∈ D, |s n d| ≤ Bd)
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ ε)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (T : D → ℝ)
    (hT : ∀ d : D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (T d))) :
    ∃ S : X → ℝ, Continuous S ∧
      (∀ d ∈ D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (S d))) ∧
      (∀ x, |S x| ≤ Bd) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → |S x - S y| ≤ ε) := by
  -- T is uniformly continuous on D
  have hTeq : ∀ ε > 0, ∃ δ > 0, ∀ d d' : D, dist d d' < δ → |T d - T d'| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := heq ε hε
    refine ⟨δ, hδ, fun d d' hdd => ?_⟩
    have hev := hφ.tendsto_atTop.eventually (h d d.2 d' d'.2 hdd)
    have hlim : Tendsto (fun k => |s (φ k) d - s (φ k) d'|) atTop (𝓝 |T d - T d'|) :=
      ((hT d).sub (hT d')).abs
    exact le_of_tendsto hlim hev
  have hTuc : UniformContinuous T := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hTeq (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun {a b} hab => ?_⟩
    rw [Real.dist_eq]
    have := h a b hab
    linarith
  have hui : IsUniformInducing (Subtype.val : D → X) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have hdr : DenseRange (Subtype.val : D → X) := hDd.denseRange_val
  set S : X → ℝ := (hui.isDenseInducing hdr).extend T with hS
  have hSuc : UniformContinuous S := uniformContinuous_uniformly_extend hui hdr hTuc
  have hSD : ∀ d : D, S d = T d := fun d => uniformly_extend_of_ind hui hdr hTuc d
  clear_value S
  refine ⟨S, hSuc.continuous, ?_, ?_, ?_⟩
  · intro d hd
    have := hT ⟨d, hd⟩
    rw [hSD ⟨d, hd⟩]
    exact this
  · -- boundedness: the closed set {x | |S x| ≤ Bd} contains D
    have hcl : IsClosed {x | |S x| ≤ Bd} :=
      isClosed_le (continuous_abs.comp hSuc.continuous) continuous_const
    have hsub : D ⊆ {x | |S x| ≤ Bd} := by
      intro d hd
      show |S d| ≤ Bd
      have hconv := hT ⟨d, hd⟩
      have : |T ⟨d, hd⟩| ≤ Bd :=
        le_of_tendsto (hconv.abs) (Eventually.of_forall (fun k => hbd (φ k) d hd))
      have e := hSD ⟨d, hd⟩
      simp only at e
      rw [e]; exact this
    intro x
    have := hcl.closure_subset_iff.mpr hsub
    rw [hDd.closure_eq] at this
    exact this (mem_univ x)
  · -- modulus of continuity: pass the estimate on D to the closure
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hTeq ε hε
    refine ⟨δ, hδ, fun x y hxy => ?_⟩
    -- view the set {p | dist p.1 p.2 < δ → |S p.1 - S p.2| ≤ ε} on the open set U = {dist < δ}
    have hU : IsOpen {p : X × X | dist p.1 p.2 < δ} :=
      isOpen_lt (continuous_fst.dist continuous_snd) continuous_const
    have hcl : IsClosed {p : X × X | |S p.1 - S p.2| ≤ ε} :=
      isClosed_le (continuous_abs.comp
        ((hSuc.continuous.comp continuous_fst).sub (hSuc.continuous.comp continuous_snd)))
        continuous_const
    have hDD : Dense (D ×ˢ D) := hDd.prod hDd
    -- U ∩ (D×D) is contained in U ∩ (a closed set), and U is open, so U ⊆ closure (U ∩ D×D)
    have hsub : {p : X × X | dist p.1 p.2 < δ} ∩ (D ×ˢ D) ⊆ {p | |S p.1 - S p.2| ≤ ε} := by
      rintro ⟨a, b⟩ ⟨hab, ha, hb⟩
      show |S a - S b| ≤ ε
      have e1 := hSD ⟨a, ha⟩
      have e2 := hSD ⟨b, hb⟩
      simp only at e1 e2
      rw [e1, e2]
      exact h ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hmem : (x, y) ∈ closure ({p : X × X | dist p.1 p.2 < δ} ∩ (D ×ˢ D)) := by
      exact hDD.open_subset_closure_inter hU hxy
    have hfin : (x, y) ∈ {p : X × X | |S p.1 - S p.2| ≤ ε} :=
      (hcl.closure_subset_iff.mpr hsub) hmem
    exact hfin

/-- From a sequence on a countable dense `D` that is uniformly bounded and equicontinuous "on fine enough lattices", one gets
a subsequence and a continuous limit `S` on all of `X`. -/
theorem exists_subseq_continuous_limit (D : Set X) (hDc : D.Countable) (hDd : Dense D)
    (s : ℕ → X → ℝ) (Bd : ℝ) (hbd : ∀ n, ∀ d ∈ D, |s n d| ≤ Bd)
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ S : X → ℝ, Continuous S ∧
      (∀ d ∈ D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (S d))) ∧
      (∀ x, |S x| ≤ Bd) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → |S x - S y| ≤ ε) := by
  obtain ⟨φ, hφ, T, hT⟩ := exists_subseq_tendsto_on_countable D hDc s Bd hbd
  exact ⟨φ, hφ, continuous_extension_of_tendsto D hDd s Bd hbd heq φ hφ T hT⟩

/-! ## 6. Invariance and positivity constraints survive the limit (observable level) -/

/-- If a continuous action `g : X → X` maps `D` to `D` and on `D`
`|s_n(g d) − s_n(d)| ≤ ε_n(d) → 0`, then the continuous extension `S` of the subsequential limit on `D` is
invariant under `g` on all of `X`. -/
theorem invariance_of_limit (D : Set X) (hDd : Dense D)
    (s : ℕ → X → ℝ) (φ : ℕ → ℕ) (S : X → ℝ) (hSc : Continuous S)
    (hlim : ∀ d ∈ D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (S d)))
    (g : X → X) (hg : Continuous g) (hgD : ∀ d ∈ D, g d ∈ D)
    (ε : ℕ → X → ℝ) (hε : ∀ d ∈ D, Tendsto (fun k => ε (φ k) d) atTop (𝓝 0))
    (hsym : ∀ n, ∀ d ∈ D, |s n (g d) - s n d| ≤ ε n d) :
    ∀ x, S (g x) = S x := by
  have hEq : EqOn (S ∘ g) S D := by
    intro d hd
    have t := ((hlim (g d) (hgD d hd)).sub (hlim d hd)).abs
    have hle : |S (g d) - S d| ≤ 0 :=
      le_of_tendsto_of_tendsto' t (hε d hd) (fun k => hsym (φ k) d hd)
    have := abs_nonpos_iff.mp hle
    simp only [Function.comp]
    linarith
  have := Continuous.ext_on hDd (hSc.comp hg) hSc hEq
  intro x
  exact congrFun this x

/-- Positivity of quadratic forms in finitely many observables (matrix form of reflection positivity): if on each lattice
`∑_{a,b} c_a c_b s_n(I a b) ≥ 0`, the same holds in the limit. -/
theorem quadratic_positivity_limit {m : ℕ} (s : ℕ → X → ℝ) (φ : ℕ → ℕ) (S : X → ℝ)
    (I : Fin m → Fin m → X)
    (hlim : ∀ a b, Tendsto (fun k => s (φ k) (I a b)) atTop (𝓝 (S (I a b))))
    (c : Fin m → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 ≤ ∑ a, ∑ b, c a * c b * s n (I a b))
    (hφ : StrictMono φ) :
    0 ≤ ∑ a, ∑ b, c a * c b * S (I a b) := by
  have ht : Tendsto (fun k => ∑ a, ∑ b, c a * c b * s (φ k) (I a b)) atTop
      (𝓝 (∑ a, ∑ b, c a * c b * S (I a b))) := by
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro b _
    exact (hlim a b).const_mul (c a * c b)
  exact ge_of_tendsto ht (hφ.tendsto_atTop.eventually hpos)

/-- Invariance under a dense subgroup extends to the whole group if the action is continuous in the group variable
(from invariance under dyadic translations to invariance under all translations of the torus). -/
theorem invariance_extends_by_density {Gc : Type*} [TopologicalSpace Gc]
    (actc : Gc → X → X) (S : X → ℝ) (hSc : Continuous S)
    (hcont : ∀ x, Continuous (fun g => actc g x))
    (Dg : Set Gc) (hDg : Dense Dg) (hinv : ∀ g ∈ Dg, ∀ x, S (actc g x) = S x) :
    ∀ g x, S (actc g x) = S x := by
  intro g x
  have hEq : EqOn (fun g => S (actc g x)) (fun _ => S x) Dg := fun g hg => hinv g hg x
  have := Continuous.ext_on hDg (hSc.comp (hcont x)) continuous_const hEq
  exact congrFun this g

/-! ## 7. No subsequence needed when increments are summable -/

/-- If `|s_{n+1}(x) − s_n(x)| ≤ δ_n` and `∑ δ_n < ∞`, then `s_n(x)` converges. -/
theorem tendsto_of_summable_increments (s : ℕ → ℝ) (δ : ℕ → ℝ)
    (hδ : Summable δ) (hinc : ∀ n, |s (n + 1) - s n| ≤ δ n) :
    ∃ L : ℝ, Tendsto s atTop (𝓝 L) := by
  have hd : Summable (fun n => dist (s n) (s n.succ)) := by
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_) hδ
    rw [Real.dist_eq, abs_sub_comm]
    exact hinc n
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hd)

/-- If a sequence converges, every subsequential limit equals its limit (uniqueness of limits). -/
theorem subseq_limit_eq (s : ℕ → ℝ) (L L' : ℝ) (hs : Tendsto s atTop (𝓝 L))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (h' : Tendsto (s ∘ φ) atTop (𝓝 L')) : L' = L :=
  tendsto_nhds_unique h' (hs.comp hφ.tendsto_atTop)

end Observables

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

section AssemblyObservables

variable {X : Type*} [MetricSpace X]

/-- Premises at the observable level. `X` is the space of observable configurations (positions and orientations of a tuple of
smeared observables), `D` the countable dense set of configurations representable on the lattice (dyadic positions), `s n x` the
expectation on lattice `n`. `act g` are the continuous symmetries (torus translations and the hypercubic group), `ε g n d` the size of
the breaking on lattice `n`. `P` is the family of matrix constraints of reflection positivity. -/
structure ObservableHypotheses (D : Set X) (s : ℕ → X → ℝ) (Bd : ℝ)
    {G : Type*} (act : G → X → X) (ε : G → ℕ → X → ℝ)
    (P : Set (Σ m : ℕ, (Fin m → Fin m → X) × (Fin m → ℝ))) : Prop where
  countable : D.Countable
  dense : Dense D
  bounded : ∀ n, ∀ d ∈ D, |s n d| ≤ Bd
  equicontinuous : ∀ η > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
    ∀ᶠ n in atTop, |s n d - s n d'| ≤ η
  act_continuous : ∀ g, Continuous (act g)
  act_maps : ∀ g, ∀ d ∈ D, act g d ∈ D
  breaking : ∀ g n, ∀ d ∈ D, |s n (act g d) - s n d| ≤ ε g n d
  breaking_vanishes : ∀ g, ∀ d ∈ D, Tendsto (fun n => ε g n d) atTop (𝓝 0)
  positivity_on_lattice : ∀ p ∈ P, (∀ a b, p.2.1 a b ∈ D) ∧
    ∀ᶠ n in atTop, 0 ≤ ∑ a, ∑ b, p.2.2 a * p.2.2 b * s n (p.2.1 a b)

/-- Conclusion at the observable level (for the limiting functional `S`). -/
structure ObservableConclusion (D : Set X) (S : X → ℝ) (Bd : ℝ)
    {G : Type*} (act : G → X → X)
    (P : Set (Σ m : ℕ, (Fin m → Fin m → X) × (Fin m → ℝ))) : Prop where
  continuous : Continuous S
  bounded : ∀ x, |S x| ≤ Bd
  modulus : ∀ η > 0, ∃ δ > 0, ∀ x y, dist x y < δ → |S x - S y| ≤ η
  invariant : ∀ g x, S (act g x) = S x
  positive : ∀ p ∈ P, 0 ≤ ∑ a, ∑ b, p.2.2 a * p.2.2 b * S (p.2.1 a b)

/-- Skeleton of the implication (observable level): there are a subsequence and a continuous functional `S` that is its limit on `D`,
and `S` is bounded, uniformly continuous, symmetry invariant, and satisfies the matrix constraints of reflection positivity. -/
theorem weak_uv_observable_skeleton (D : Set X) (s : ℕ → X → ℝ) (Bd : ℝ)
    {G : Type*} (act : G → X → X) (ε : G → ℕ → X → ℝ)
    (P : Set (Σ m : ℕ, (Fin m → Fin m → X) × (Fin m → ℝ)))
    (H : ObservableHypotheses D s Bd act ε P) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ S : X → ℝ,
      (∀ d ∈ D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (S d))) ∧
      ObservableConclusion D S Bd act P := by
  obtain ⟨φ, hφ, S, hSc, hlim, hbd, hmod⟩ :=
    exists_subseq_continuous_limit D H.countable H.dense s Bd H.bounded H.equicontinuous
  refine ⟨φ, hφ, S, hlim, hSc, hbd, hmod, ?_, ?_⟩
  · intro g
    exact invariance_of_limit D H.dense s φ S hSc hlim (act g) (H.act_continuous g)
      (H.act_maps g) (ε g) (fun d hd => (H.breaking_vanishes g d hd).comp hφ.tendsto_atTop)
      (H.breaking g)
  · intro p hp
    obtain ⟨hD, hpos⟩ := H.positivity_on_lattice p hp
    exact quadratic_positivity_limit s φ S p.2.1 (fun a b => hlim _ (hD a b)) p.2.2 hpos hφ

/-- Strong form (no subsequence): if moreover the increments are summable at each `d ∈ D`, the sequence itself converges on `D`
and the limit agrees with the `S` of the skeleton theorem. -/
theorem weak_uv_observable_full (D : Set X) (s : ℕ → X → ℝ) (Bd : ℝ)
    {G : Type*} (act : G → X → X) (ε : G → ℕ → X → ℝ)
    (P : Set (Σ m : ℕ, (Fin m → Fin m → X) × (Fin m → ℝ)))
    (H : ObservableHypotheses D s Bd act ε P)
    (δ : ℕ → X → ℝ) (hδ : ∀ d ∈ D, Summable (fun n => δ n d))
    (hinc : ∀ d ∈ D, ∀ n, |s (n + 1) d - s n d| ≤ δ n d) :
    ∃ S : X → ℝ, (∀ d ∈ D, Tendsto (fun n => s n d) atTop (𝓝 (S d))) ∧
      ObservableConclusion D S Bd act P := by
  obtain ⟨φ, hφ, S, hlim, hC⟩ := weak_uv_observable_skeleton D s Bd act ε P H
  refine ⟨S, fun d hd => ?_, hC⟩
  obtain ⟨L, hL⟩ := tendsto_of_summable_increments (fun n => s n d) (fun n => δ n d)
    (hδ d hd) (hinc d hd)
  have := subseq_limit_eq (fun n => s n d) L (S d) hL φ hφ (hlim d hd)
  rw [this]; exact hL

end AssemblyObservables

section AssemblyCombined

variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)] [∀ m, MetricSpace (E m)]
  [∀ m, CompactSpace (E m)] [∀ m, BorelSpace (E m)]
variable {X : Type*} [MetricSpace X]

/-- Observables are represented by continuous functions of block variables: on fine enough lattices, the lattice-`n` expectation
at `d ∈ D` equals the integral of a bounded continuous function `F d` of the block variables at scale `lev d`. -/
structure Representation (ν : ℕ → ∀ m, ProbabilityMeasure (E m)) (D : Set X)
    (s : ℕ → X → ℝ) (lev : X → ℕ) (F : ∀ x, BoundedContinuousFunction (E (lev x)) ℝ) :
    Prop where
  represent : ∀ d ∈ D, ∀ᶠ n in atTop,
    s n d = ∫ ω, F d ω ∂(ν n (lev d) : Measure (E (lev d)))

/-- Skeleton of the implication (combined form): taking one subsequence of the block-variable measures, along it all observables
converge on `D`, the limit is given by integrals against the limiting measures, extends continuously to all of `X`, and satisfies
all the observable-level conclusions. -/
theorem weak_uv_skeleton (ν : ℕ → ∀ m, ProbabilityMeasure (E m))
    (B : ∀ m, E (m + 1) → E m) (hB : ∀ m, Continuous (B m))
    (Θ : ∀ m, E m → E m) (A : ∀ m, Set (BoundedContinuousFunction (E m) ℝ))
    {Gb : Type*} (actb : Gb → ∀ m, E m → E m)
    (C : ∀ m, Set (E m)) (c : ℕ → ℝ≥0∞)
    (D : Set X) (s : ℕ → X → ℝ) (Bd : ℝ)
    {G : Type*} (act : G → X → X) (ε : G → ℕ → X → ℝ)
    (P : Set (Σ m : ℕ, (Fin m → Fin m → X) × (Fin m → ℝ)))
    (lev : X → ℕ) (F : ∀ x, BoundedContinuousFunction (E (lev x)) ℝ)
    (HB : BlockHypotheses ν B hB Θ A actb C c)
    (HO : ObservableHypotheses D s Bd act ε P)
    (HR : Representation ν D s lev F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νl : ∀ m, ProbabilityMeasure (E m),
      (∀ m, Tendsto (fun k => ν (φ k) m) atTop (𝓝 (νl m))) ∧
      BlockConclusion νl B hB Θ A actb C c ∧
      ∃ S : X → ℝ,
        (∀ d ∈ D, S d = ∫ ω, F d ω ∂(νl (lev d) : Measure (E (lev d)))) ∧
        (∀ d ∈ D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (S d))) ∧
        ObservableConclusion D S Bd act P := by
  obtain ⟨φ, hφ, νl, hlim, HC⟩ := weak_uv_block_skeleton ν B hB Θ A actb C c HB
  set T : D → ℝ := fun d => ∫ ω, F d ω ∂(νl (lev d) : Measure (E (lev d))) with hTdef
  have hT : ∀ d : D, Tendsto (fun k => s (φ k) d) atTop (𝓝 (T d)) := by
    intro d
    have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hlim (lev d))) (F d)
    have hev : ∀ᶠ k in atTop,
        ∫ ω, F d ω ∂(ν (φ k) (lev d) : Measure (E (lev d))) = s (φ k) d :=
      (hφ.tendsto_atTop.eventually (HR.represent d d.2)).mono (fun k hk => hk.symm)
    exact hint.congr' hev
  obtain ⟨S, hSc, hSlim, hSbd, hSmod⟩ :=
    continuous_extension_of_tendsto D HO.dense s Bd HO.bounded HO.equicontinuous φ hφ T hT
  refine ⟨φ, hφ, νl, hlim, HC, S, ?_, hSlim, hSc, hSbd, hSmod, ?_, ?_⟩
  · intro d hd
    exact tendsto_nhds_unique (hSlim d hd) (hT ⟨d, hd⟩)
  · intro g
    exact invariance_of_limit D HO.dense s φ S hSc hSlim (act g) (HO.act_continuous g)
      (HO.act_maps g) (ε g) (fun d hd => (HO.breaking_vanishes g d hd).comp hφ.tendsto_atTop)
      (HO.breaking g)
  · intro p hp
    obtain ⟨hD, hpos⟩ := HO.positivity_on_lattice p hp
    exact quadratic_positivity_limit s φ S p.2.1 (fun a b => hSlim _ (hD a b)) p.2.2 hpos hφ

end AssemblyCombined

/-! ## 9. Axiom check -/


end WeakUltravioletExistence


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


end UltravioletChain

namespace UltravioletGlue

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Glue for (H-β): from the chain premises and continuity (C) within the domain, (W0) of Theorem W (the bare-coupling lemma (W0)) follows. -/
theorem glue_bare_coupling {X : Type*} [PseudoMetricSpace X]
    {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]
    {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    {ν : ℕ → ∀ m, Measure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : UltravioletChain.ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R I θh ε Dset s τ Ωr)
    (h0 : ∀ x, u 0 x = x)
    (hC : ∀ k, ContinuousOn (u (k + 1)) {x | ∀ j ≤ k, ustar ≤ u j x})
    (t : ℝ) (ht : ustar ≤ t) (n : ℕ) :
    ∃ x : ℝ, t + b / 2 * n ≤ x ∧ x ≤ t + 3 * b / 2 * n ∧ u n x = t ∧
      ∀ k ≤ n, t ≤ u k x :=
  WeakUltravioletExistence.exists_bare_inverse_coupling u b ustar t n H.steps.hb h0
    (UltravioletChain.chain_to_hypotheses H).1 hC ht

/-- Glue for (H-reg): the chain's conclusion fits directly into the field `ObservableHypotheses.equicontinuous`. -/
theorem glue_observable {X : Type*} [MetricSpace X]
    {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]
    {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    {ν : ℕ → ∀ m, Measure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : UltravioletChain.ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R I θh ε Dset s τ Ωr)
    (Bd : ℝ) {G : Type*} (act : G → X → X) (εb : G → ℕ → X → ℝ)
    (P : Set (Σ m : ℕ, (Fin m → Fin m → X) × (Fin m → ℝ)))
    (hcount : Dset.Countable) (hdense : Dense Dset) (hbd : ∀ n, ∀ d ∈ Dset, |s n d| ≤ Bd)
    (hac : ∀ g, Continuous (act g)) (ham : ∀ g, ∀ d ∈ Dset, act g d ∈ Dset)
    (hbr : ∀ g n, ∀ d ∈ Dset, |s n (act g d) - s n d| ≤ εb g n d)
    (hbv : ∀ g, ∀ d ∈ Dset, Tendsto (fun n => εb g n d) atTop (𝓝 0))
    (hpos : ∀ p ∈ P, (∀ a b, p.2.1 a b ∈ Dset) ∧
      ∀ᶠ n in atTop, 0 ≤ ∑ a, ∑ b, p.2.2 a * p.2.2 b * s n (p.2.1 a b)) :
    WeakUltravioletExistence.ObservableHypotheses Dset s Bd act εb P :=
  { countable := hcount, dense := hdense, bounded := hbd,
    equicontinuous := (UltravioletChain.chain_to_hypotheses H).2.2,
    act_continuous := hac, act_maps := ham, breaking := hbr, breaking_vanishes := hbv,
    positivity_on_lattice := hpos }

/-- Glue for (H-sf): for a sequence of probability measures, the chain's conclusion has the form of
`BlockHypotheses.small_field_mass` (small-field event defined by the invariant, lower bound `1 − |R| ε`). -/
theorem glue_small_field {X : Type*} [PseudoMetricSpace X]
    {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]
    {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    {νP : ℕ → ∀ m, ProbabilityMeasure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : UltravioletChain.ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar
      (fun n m => (νP n m : Measure (E m))) R I θh ε Dset s τ Ωr) :
    ∀ m, ∀ᶠ n in atTop, (1 - (R m).card * ε m) ≤
      (νP n m : Measure (E m)) {ω | ∀ i ∈ R m, I m i ω ≤ θh m} :=
  (UltravioletChain.chain_to_hypotheses H).2.1

end UltravioletGlue

#print axioms WeakUltravioletExistence.exists_bare_inverse_coupling
#print axioms WeakUltravioletExistence.exists_subseq_tendsto_probabilityMeasure
#print axioms WeakUltravioletExistence.exists_common_subseq
#print axioms WeakUltravioletExistence.limit_consistent
#print axioms WeakUltravioletExistence.reflection_positivity_limit
#print axioms WeakUltravioletExistence.approx_invariance_limit
#print axioms WeakUltravioletExistence.closed_mass_lower_limit
#print axioms WeakUltravioletExistence.exists_subseq_tendsto_on_countable
#print axioms WeakUltravioletExistence.continuous_extension_of_tendsto
#print axioms WeakUltravioletExistence.exists_subseq_continuous_limit
#print axioms WeakUltravioletExistence.invariance_of_limit
#print axioms WeakUltravioletExistence.quadratic_positivity_limit
#print axioms WeakUltravioletExistence.invariance_extends_by_density
#print axioms WeakUltravioletExistence.tendsto_of_summable_increments
#print axioms WeakUltravioletExistence.subseq_limit_eq
#print axioms WeakUltravioletExistence.weak_uv_block_skeleton
#print axioms WeakUltravioletExistence.weak_uv_observable_skeleton
#print axioms WeakUltravioletExistence.weak_uv_observable_full
#print axioms WeakUltravioletExistence.weak_uv_skeleton
#print axioms UltravioletChain.activity_le
#print axioms UltravioletChain.hbeta_of_steps
#print axioms UltravioletChain.small_field_mass_of_rarity
#print axioms UltravioletChain.small_field_mass_invariant
#print axioms UltravioletChain.expectation_diff_le
#print axioms UltravioletChain.split_small_field
#print axioms UltravioletChain.gauge_choice
#print axioms UltravioletChain.equicontinuous_of_split
#print axioms UltravioletChain.vanishing_add
#print axioms UltravioletChain.vanishing_linear
#print axioms UltravioletChain.chain_to_hypotheses
#print axioms UltravioletGlue.glue_bare_coupling
#print axioms UltravioletGlue.glue_observable
#print axioms UltravioletGlue.glue_small_field
