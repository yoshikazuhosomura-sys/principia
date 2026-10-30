/-
The two definitions of the effective coupling (premise 6) fall under the same type: the coupling extracted from the large-field difference
  r(x) = (log Z_θ(x) − log Z_0(x))/(cV), Z_θ(x) = ∫ e^{−x S_θ} dμ
is continuous in the bare inverse coupling x (using copies of §1 and §2 of GibbsContinuity). So continuity on the domain in (C)
follows from the same lemma whichever difference definition is chosen. That the gas Z equals the ratio of lattice partition functions (exactness of the expansion) is on paper.
Single file; checks with `import Mathlib` only.
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

/-- The difference coupling is continuous in x. -/
theorem continuous_difference_coupling (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ]
    (Sθ S0 : Ω → ℝ) (hθ : Continuous Sθ) (h0 : Continuous S0) (c V : ℝ) :
    Continuous fun x : ℝ =>
      (Real.log (∫ ω, Real.exp (-(x * Sθ ω)) ∂μ) - Real.log (∫ ω, Real.exp (-(x * S0 ω)) ∂μ)) /
        (c * V) := by
  have hZ : ∀ S : Ω → ℝ, Continuous S → Continuous fun x : ℝ => ∫ ω, Real.exp (-(x * S ω)) ∂μ := by
    intro S hS
    have := continuous_weighted_integral μ S (fun _ => (1 : ℝ)) hS continuous_const
    simpa using this
  have hl : ∀ S : Ω → ℝ, Continuous S →
      Continuous fun x : ℝ => Real.log (∫ ω, Real.exp (-(x * S ω)) ∂μ) := by
    intro S hS
    exact (hZ S hS).log (fun x => (partition_pos μ S hS x).ne')
  exact ((hl Sθ hθ).sub (hl S0 h0)).div_const _

#print axioms continuous_weighted_integral
#print axioms partition_pos
#print axioms continuous_gibbs_expectation
#print axioms continuous_difference_coupling

end GibbsContinuity
