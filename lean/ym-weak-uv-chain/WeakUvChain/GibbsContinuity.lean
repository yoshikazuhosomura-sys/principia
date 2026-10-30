/-
Continuity (C) in the bare coupling: Gibbs expectations on a compact configuration space are continuous in the inverse coupling x.
If the effective coupling is a continuous function of finitely many expectations, it is continuous on the domain (the (C) form of the bare-coupling lemma (W0)).
Single file; checks with `import Mathlib` only.

  §1 Z_f(x) = ∫ f e^{−x S} dμ is continuous in x (S, f continuous, Ω compact, μ finite)
  §2 Z(x) = ∫ e^{−x S} dμ > 0 (μ nonzero), and the expectation E_x[f] = Z_f(x)/Z(x) is continuous
  §3 If the effective inverse coupling u(x) = G(E_x[f₁], …, E_x[f_p]) with G continuous on a set containing the image of the domain,
     then u is continuous on the domain
  §4 #print axioms

The finite-lattice configuration space SU(2)^{links} is a compact metric space and the Wilson action is continuous, so the premises of
§1 and §2 hold (this application is on paper). That the effective coupling is a continuous function of expectations (the definition of
the renormalised coupling) is a premise on the definition side.
-/
import Mathlib

namespace GibbsContinuity

open MeasureTheory Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  [SecondCountableTopology Ω]

/-- §1: `x ↦ ∫ f(ω) e^{−x S(ω)} dμ` is continuous. -/
theorem continuous_weighted_integral (μ : Measure Ω) [IsFiniteMeasure μ] (S f : Ω → ℝ)
    (hS : Continuous S) (hf : Continuous f) :
    Continuous fun x : ℝ => ∫ ω, f ω * Real.exp (-(x * S ω)) ∂μ := by
  have hcont : Continuous (Function.uncurry fun (x : ℝ) (ω : Ω) => f ω * Real.exp (-(x * S ω))) := by
    apply Continuous.mul (hf.comp continuous_snd)
    apply Real.continuous_exp.comp
    exact ((continuous_fst).mul (hS.comp continuous_snd)).neg
  have := continuous_parametric_integral_of_continuous (μ := μ) hcont isCompact_univ
  simpa [Measure.restrict_univ] using this

/-- §2: the partition function is positive. -/
theorem partition_pos (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (S : Ω → ℝ)
    (hS : Continuous S) (x : ℝ) : 0 < ∫ ω, Real.exp (-(x * S ω)) ∂μ := by
  have hint : Integrable (fun ω => Real.exp (-(x * S ω))) μ := by
    have hc : Continuous fun ω => Real.exp (-(x * S ω)) :=
      Real.continuous_exp.comp ((continuous_const.mul hS).neg)
    obtain ⟨C, hC⟩ := (isCompact_univ.image hc).isBounded.exists_norm_le
    refine Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => ?_)
    exact hC _ ⟨ω, Set.mem_univ _, rfl⟩
  rw [integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) hint]
  have : Function.support (fun ω => Real.exp (-(x * S ω))) = Set.univ := by
    ext ω; simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [this]
  exact pos_iff_ne_zero.mpr (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ))

/-- §2: the Gibbs expectation `E_x[f] = Z_f(x)/Z(x)` is continuous in `x`. -/
theorem continuous_gibbs_expectation (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ]
    (S f : Ω → ℝ) (hS : Continuous S) (hf : Continuous f) :
    Continuous fun x : ℝ =>
      (∫ ω, f ω * Real.exp (-(x * S ω)) ∂μ) / ∫ ω, Real.exp (-(x * S ω)) ∂μ := by
  have h1 := continuous_weighted_integral μ S f hS hf
  have h2 : Continuous fun x : ℝ => ∫ ω, Real.exp (-(x * S ω)) ∂μ := by
    have := continuous_weighted_integral μ S (fun _ => (1 : ℝ)) hS continuous_const
    simpa using this
  exact h1.div h2 (fun x => (partition_pos μ S hS x).ne')

/-- §3: if the effective inverse coupling can be written `u = G ∘ e` on the domain `dom`, with finitely many
continuous quantities `e : ℝ → (Fin p → ℝ)` and `G` continuous on a set `K` containing the image of `e`,
then `u` is continuous on `dom` (form (C) of the bare-coupling lemma (W0)). -/
theorem continuousOn_effective_coupling {p : ℕ} (e : ℝ → (Fin p → ℝ)) (he : Continuous e)
    (G : (Fin p → ℝ) → ℝ) (K : Set (Fin p → ℝ)) (hG : ContinuousOn G K)
    (dom : Set ℝ) (hmaps : Set.MapsTo e dom K) (u : ℝ → ℝ) (hu : ∀ x ∈ dom, u x = G (e x)) :
    ContinuousOn u dom := by
  have : ContinuousOn (G ∘ e) dom := hG.comp he.continuousOn hmaps
  exact this.congr (fun x hx => hu x hx)

/-- Part of §3: the map collecting finitely many Gibbs expectations is continuous. -/
theorem continuous_expectation_vector (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] {p : ℕ}
    (S : Ω → ℝ) (f : Fin p → Ω → ℝ) (hS : Continuous S) (hf : ∀ i, Continuous (f i)) :
    Continuous fun x : ℝ => fun i =>
      (∫ ω, f i ω * Real.exp (-(x * S ω)) ∂μ) / ∫ ω, Real.exp (-(x * S ω)) ∂μ :=
  continuous_pi fun i => continuous_gibbs_expectation μ S (f i) hS (hf i)

#print axioms continuous_weighted_integral
#print axioms partition_pos
#print axioms continuous_gibbs_expectation
#print axioms continuousOn_effective_coupling
#print axioms continuous_expectation_vector

end GibbsContinuity
