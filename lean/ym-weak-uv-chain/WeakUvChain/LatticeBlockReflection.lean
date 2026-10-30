/-
Finite-lattice step: continuity, gauge covariance and composition of an example block map (average of path products
plus radial retraction), and coarse reflection positivity derived from site-reflection positivity (a reflection-invariant
positive weight and functions determined by a half-space). Single file; checks with `import Mathlib` only.

  §1 Radial retraction ρ_{r₀}(q) = q / max(‖q‖, r₀): continuous, norm ≤ 1, agrees with normalisation on the
     small field, commutes with left and right multiplication by unit quaternions
  §2 Gauge covariance: preserved by path products, weighted averages and retraction; composition of equivariant
     maps and pull-back of gauge-invariant observables
  §3 Continuity: preserved by path products, averages, retraction and composition
  §4 Site-reflection positivity: configurations (c, a, b) (c on the reflection plane, a on the negative side, b on the
     positive side identified via the reflection), weight k(c) h(c,a) h(c,b), and for a positive-side function φ(c,b),
     ∫ φ(c,a) φ(c,b) ρ ≥ 0
  §5 Push-forward: positivity survives push-forward by a map that commutes with the reflection and pulls positive-side
     functions back to positive-side functions; bridge to the fields of the Theorem W structure
     (consistency, reflection positivity, symmetry)
  §6 #print axioms

The lattice geometry (which links lie on which side), Haar measure and the explicit Wilson action are not here.
They enter as premises: "the weight factors as k(c) h(c,a) h(c,b)" and "the map commutes with the reflection and
preserves the positive side" (for site reflection of the Wilson action the weight factors, since every plaquette lies on
one side or on the plane).
-/
import Mathlib

namespace LatticeBlockReflection

open MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

local notation "ℍr" => Quaternion ℝ

/-! ## 1. Radial retraction -/

/-- Radial retraction. -/
noncomputable def retract (r₀ : ℝ) (q : ℍr) : ℍr := (max ‖q‖ r₀)⁻¹ • q

theorem continuous_retract {r₀ : ℝ} (hr : 0 < r₀) : Continuous (retract r₀) := by
  unfold retract
  have hmax : Continuous fun q : ℍr => max ‖q‖ r₀ := continuous_norm.max continuous_const
  exact (hmax.inv₀ (fun q => ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _)))).smul continuous_id

theorem norm_retract_le {r₀ : ℝ} (hr : 0 < r₀) (q : ℍr) : ‖retract r₀ q‖ ≤ 1 := by
  unfold retract
  have hpos : 0 < max ‖q‖ r₀ := lt_of_lt_of_le hr (le_max_right _ _)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos, mul_one]
  exact le_max_left _ _

/-- On the small-field event `‖q‖ ≥ r₀`, the retraction agrees with the normalisation `q/‖q‖`, and its value is a
unit quaternion. -/
theorem retract_of_le {r₀ : ℝ} (hr : 0 < r₀) {q : ℍr} (hq : r₀ ≤ ‖q‖) :
    retract r₀ q = ‖q‖⁻¹ • q ∧ ‖retract r₀ q‖ = 1 := by
  have hmax : max ‖q‖ r₀ = ‖q‖ := max_eq_left hq
  have hpos : 0 < ‖q‖ := lt_of_lt_of_le hr hq
  refine ⟨by simp [retract, hmax], ?_⟩
  simp only [retract, hmax, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  exact inv_mul_cancel₀ hpos.ne'

/-- Commutes with left and right multiplication by unit quaternions (gauge transformations). -/
theorem retract_mul_unit (r₀ : ℝ) (u v q : ℍr) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    retract r₀ (u * q * v) = u * retract r₀ q * v := by
  unfold retract
  have hn : ‖u * q * v‖ = ‖q‖ := by rw [norm_mul, norm_mul, hu, hv, one_mul, mul_one]
  rw [hn, mul_smul_comm, smul_mul_assoc]

/-! ## 2. Gauge covariance -/

section Covariance

variable {Λ G S : Type*}

/-- A map `T` (from link-variable configurations to quaternions) is covariant as a transport from site `x` to `y`.
`act g U` is the gauge transformation; `gs g z` is the value at site `z`. -/
def Covariant (act : G → (Λ → ℍr) → (Λ → ℍr)) (gs : G → S → ℍr) (x y : S)
    (T : (Λ → ℍr) → ℍr) : Prop :=
  ∀ g U, T (act g U) = gs g x * T U * star (gs g y)

variable (act : G → (Λ → ℍr) → (Λ → ℍr)) (gs : G → S → ℍr)

/-- Concatenating paths: the gauge at the intermediate site cancels, since it is a unit quaternion. -/
theorem covariant_mul (hunit : ∀ g z, star (gs g z) * gs g z = 1) {x y z : S}
    {T₁ T₂ : (Λ → ℍr) → ℍr} (h₁ : Covariant act gs x y T₁) (h₂ : Covariant act gs y z T₂) :
    Covariant act gs x z (fun U => T₁ U * T₂ U) := by
  intro g U
  simp only
  rw [h₁ g U, h₂ g U]
  have e : gs g x * T₁ U * star (gs g y) * (gs g y * T₂ U * star (gs g z)) =
      gs g x * T₁ U * (star (gs g y) * gs g y) * T₂ U * star (gs g z) := by
    simp only [mul_assoc]
  rw [e, hunit g y, mul_one, mul_assoc (gs g x)]

/-- For unit quaternions, `q * star q = 1` also holds. -/
theorem mul_star_of_star_mul {q : ℍr} (h : star q * q = 1) : q * star q = 1 := by
  have hne : q ≠ 0 := by
    intro h0; rw [h0, star_zero, zero_mul] at h; exact zero_ne_one h
  have e : star q = q⁻¹ := by
    rw [← mul_one (star q), ← mul_inv_cancel₀ hne, ← mul_assoc, h, one_mul]
  rw [e, mul_inv_cancel₀ hne]

/-- A path: a list of steps (endpoint, map), each a covariant transport from the previous endpoint to its own. -/
def PathOK : S → List (S × ((Λ → ℍr) → ℍr)) → S → Prop
  | x, [], y => x = y
  | x, s :: rest, y => Covariant act gs x s.1 s.2 ∧ PathOK s.1 rest y

/-- The path product is covariant as a transport from start to end. -/
theorem covariant_path (hunit : ∀ g z, star (gs g z) * gs g z = 1) :
    ∀ (steps : List (S × ((Λ → ℍr) → ℍr))) (x y : S), PathOK act gs x steps y →
      Covariant act gs x y (fun U => (steps.map fun s => s.2 U).prod) := by
  intro steps
  induction steps with
  | nil =>
    intro x y h g U
    simp only [PathOK] at h
    subst h
    simp only [List.map_nil, List.prod_nil, mul_one]
    exact (mul_star_of_star_mul (hunit g x)).symm
  | cons s rest ih =>
    intro x y h
    simp only [PathOK] at h
    have hm := covariant_mul act gs hunit h.1 (ih s.1 y h.2)
    intro g U
    simpa only [List.map_cons, List.prod_cons] using hm g U

/-- A weighted average of covariant transports with the same endpoints is covariant (real weights, finitely many). -/
theorem covariant_average {ι : Type*} (t : Finset ι) (w : ι → ℝ) {x y : S}
    (T : ι → (Λ → ℍr) → ℍr) (hT : ∀ i ∈ t, Covariant act gs x y (T i)) :
    Covariant act gs x y (fun U => ∑ i ∈ t, w i • T i U) := by
  intro g U
  simp only
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hT i hi g U, mul_smul_comm, smul_mul_assoc]

/-- Retraction preserves covariance (when the gauge values are unit quaternions). -/
theorem covariant_retract (r₀ : ℝ) (hnorm : ∀ g z, ‖gs g z‖ = 1) {x y : S}
    {T : (Λ → ℍr) → ℍr} (hT : Covariant act gs x y T) :
    Covariant act gs x y (fun U => retract r₀ (T U)) := by
  intro g U
  simp only
  rw [hT g U]
  exact retract_mul_unit r₀ _ _ _ (hnorm g x) (by rw [norm_star]; exact hnorm g y)

end Covariance

/-! ### Equivariance and composition of block maps; pull-back of gauge-invariant observables -/

section Equivariance

variable {Λ Λc G S Sc : Type*}

/-- Gauge action on coarse configurations: sandwich by the values at the source `src b` and target `tgt b` of the
coarse link `b`. -/
noncomputable def coarseAct (src tgt : Λc → Sc) (h : Sc → ℍr) (V : Λc → ℍr) : Λc → ℍr :=
  fun b => h (src b) * V b * star (h (tgt b))

/-- If the value on each coarse link is a covariant transport between coarse sites (a subset `ι` of fine sites),
the block map is equivariant for the action given by restricting fine gauge transformations to coarse sites. -/
theorem blockmap_equivariant (act : G → (Λ → ℍr) → (Λ → ℍr)) (gs : G → S → ℍr)
    (ι : Sc → S) (src tgt : Λc → Sc) (T : Λc → (Λ → ℍr) → ℍr)
    (hT : ∀ b, Covariant act gs (ι (src b)) (ι (tgt b)) (T b)) :
    ∀ g U, (fun b => T b (act g U)) = coarseAct src tgt (fun z => gs g (ι z)) (fun b => T b U) := by
  intro g U
  funext b
  exact hT b g U

/-- A composition of equivariant maps is equivariant (composing the restrictions of the gauge group). Type (B5). -/
theorem equivariant_comp {A B C G₁ G₂ G₃ : Type*} (actA : G₁ → A → A) (actB : G₂ → B → B)
    (actC : G₃ → C → C) (r₁₂ : G₁ → G₂) (r₂₃ : G₂ → G₃) (V₁ : A → B) (V₂ : B → C)
    (h₁ : ∀ g a, V₁ (actA g a) = actB (r₁₂ g) (V₁ a))
    (h₂ : ∀ g b, V₂ (actB g b) = actC (r₂₃ g) (V₂ b)) :
    ∀ g a, V₂ (V₁ (actA g a)) = actC (r₂₃ (r₁₂ g)) (V₂ (V₁ a)) := by
  intro g a; rw [h₁, h₂]

/-- Pulling back a coarse gauge-invariant observable by an equivariant map gives a fine gauge-invariant observable. -/
theorem invariant_pullback {A B G₁ G₂ R : Type*} (actA : G₁ → A → A) (actB : G₂ → B → B)
    (r : G₁ → G₂) (V : A → B) (hV : ∀ g a, V (actA g a) = actB (r g) (V a))
    (F : B → R) (hF : ∀ g b, F (actB g b) = F b) :
    ∀ g a, F (V (actA g a)) = F (V a) := by
  intro g a; rw [hV, hF]

end Equivariance

/-! ## 3. Continuity -/

section Continuity

variable {Λ Λc : Type*}

/-- The product of a list of continuous maps (path product) is continuous. -/
theorem continuous_path_prod (steps : List ((Λ → ℍr) → ℍr)) (h : ∀ f ∈ steps, Continuous f) :
    Continuous (fun U => (steps.map fun f => f U).prod) := by
  induction steps with
  | nil => simpa using continuous_const
  | cons f rest ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih (fun f' hf' => h f' (by simp [hf'])))

/-- Reading off a link variable is continuous. -/
theorem continuous_link (ℓ : Λ) : Continuous (fun U : Λ → ℍr => U ℓ) := continuous_apply ℓ

/-- Example of a one-step block map: for each coarse link `b`, apply the retraction to the `w`-weighted average of
the products over the path family `paths b`. If each step is continuous, the map is continuous. -/
theorem continuous_blockmap {ι : Type*} (r₀ : ℝ) (hr : 0 < r₀) (t : Λc → Finset ι)
    (w : Λc → ι → ℝ) (paths : Λc → ι → List ((Λ → ℍr) → ℍr))
    (hstep : ∀ b i, ∀ f ∈ paths b i, Continuous f) :
    Continuous (fun U : Λ → ℍr => fun b : Λc =>
      retract r₀ (∑ i ∈ t b, w b i • ((paths b i).map fun f => f U).prod)) := by
  apply continuous_pi
  intro b
  apply (continuous_retract hr).comp
  apply continuous_finsetSum
  intro i _
  exact (continuous_path_prod _ (hstep b i)).const_smul (w b i)

end Continuity

/-! ## 4. Site-reflection positivity -/

section SiteReflection

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (ν : Measure X) (μ₀ : Measure Y) [IsFiniteMeasure ν] [IsFiniteMeasure μ₀]

/-- Reflection `Θ (c, (a, b)) = (c, (b, a))`. -/
def refl (p : Y × (X × X)) : Y × (X × X) := (p.1, (p.2.2, p.2.1))

theorem measurable_refl : Measurable (refl (X := X) (Y := Y)) :=
  measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)

/-- Site-reflection positivity (weight form): for weight `k(c) h(c,a) h(c,b)` (`k ≥ 0`) and a positive-side function
`f(c,(a,b)) = φ(c,b)`, `∫ f(Θp) f(p) ρ(p) ≥ 0`. Everything is bounded and measurable. -/
theorem site_reflection_positive (k : Y → ℝ) (h φ : Y × X → ℝ)
    (hk : Measurable k) (hh : Measurable h) (hφ : Measurable φ)
    (Ck Ch Cφ : ℝ) (bk : ∀ c, |k c| ≤ Ck) (bh : ∀ p, |h p| ≤ Ch) (bφ : ∀ p, |φ p| ≤ Cφ)
    (hk0 : ∀ c, 0 ≤ k c) :
    0 ≤ ∫ p, φ (p.1, p.2.1) * φ (p.1, p.2.2) *
        (k p.1 * h (p.1, p.2.1) * h (p.1, p.2.2)) ∂(μ₀.prod (ν.prod ν)) := by
  set g : Y × X → ℝ := fun q => φ q * h q with hg
  have hgm : Measurable g := hφ.mul hh
  have bg : ∀ q, |g q| ≤ Cφ * Ch := by
    intro q; rw [hg, abs_mul]
    exact mul_le_mul (bφ q) (bh q) (abs_nonneg _) (le_trans (abs_nonneg _) (bφ q))
  have hrw : ∀ p : Y × (X × X), φ (p.1, p.2.1) * φ (p.1, p.2.2) *
      (k p.1 * h (p.1, p.2.1) * h (p.1, p.2.2)) =
      k p.1 * (g (p.1, p.2.1) * g (p.1, p.2.2)) := by
    intro p; simp only [hg]; ring
  simp_rw [hrw]
  -- Integrability
  have hm1 : Measurable fun p : Y × (X × X) => (p.1, p.2.1) := measurable_fst.prodMk measurable_snd.fst
  have hm2 : Measurable fun p : Y × (X × X) => (p.1, p.2.2) := measurable_fst.prodMk measurable_snd.snd
  have hmeas : Measurable fun p : Y × (X × X) => k p.1 * (g (p.1, p.2.1) * g (p.1, p.2.2)) :=
    (hk.comp measurable_fst).mul ((hgm.comp hm1).mul (hgm.comp hm2))
  have hint : Integrable (fun p : Y × (X × X) => k p.1 * (g (p.1, p.2.1) * g (p.1, p.2.2)))
      (μ₀.prod (ν.prod ν)) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Ck * ((Cφ * Ch) * (Cφ * Ch))) ?_
    refine Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := bk p.1
    have h2 := bg (p.1, p.2.1)
    have h3 := bg (p.1, p.2.2)
    have h23 : |g (p.1, p.2.1)| * |g (p.1, p.2.2)| ≤ (Cφ * Ch) * (Cφ * Ch) :=
      mul_le_mul h2 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h2)
    exact mul_le_mul h1 h23 (by positivity) (le_trans (abs_nonneg _) h1)
  rw [integral_prod _ hint]
  apply integral_nonneg
  intro c
  simp only
  have e : ∫ y : X × X, k c * (g (c, y.1) * g (c, y.2)) ∂(ν.prod ν) =
      k c * ((∫ a, g (c, a) ∂ν) * (∫ b, g (c, b) ∂ν)) := by
    rw [integral_const_mul, integral_prod_mul (fun a => g (c, a)) (fun b => g (c, b))]
  rw [e]
  exact mul_nonneg (hk0 c) (mul_self_nonneg _)

/-- The same as an integral against a weighted measure (`withDensity`): reflection positivity
`∫ f(Θp) f(p) dμ ≥ 0`, `μ = (μ₀ ⊗ ν ⊗ ν).withDensity ρ`, `ρ = k h h ≥ 0`. -/
theorem site_reflection_positive_measure (k : Y → ℝ) (h φ : Y × X → ℝ)
    (hk : Measurable k) (hh : Measurable h) (hφ : Measurable φ)
    (Ck Ch Cφ : ℝ) (bk : ∀ c, |k c| ≤ Ck) (bh : ∀ p, |h p| ≤ Ch) (bφ : ∀ p, |φ p| ≤ Cφ)
    (hk0 : ∀ c, 0 ≤ k c) (hh0 : ∀ p, 0 ≤ h p) :
    let ρ : Y × (X × X) → NNReal := fun p =>
      ⟨k p.1 * h (p.1, p.2.1) * h (p.1, p.2.2),
        mul_nonneg (mul_nonneg (hk0 _) (hh0 _)) (hh0 _)⟩
    0 ≤ ∫ p, φ ((refl p).1, (refl p).2.2) * φ (p.1, p.2.2)
        ∂((μ₀.prod (ν.prod ν)).withDensity fun p => (ρ p : ENNReal)) := by
  intro ρ
  have hρ : Measurable ρ := by
    apply Measurable.subtype_mk
    exact ((hk.comp measurable_fst).mul (hh.comp (measurable_fst.prodMk measurable_snd.fst))).mul
      (hh.comp (measurable_fst.prodMk measurable_snd.snd))
  rw [integral_withDensity_eq_integral_smul hρ]
  have := site_reflection_positive ν μ₀ k h φ hk hh hφ Ck Ch Cφ bk bh bφ hk0
  have e : ∀ p : Y × (X × X), ρ p • (φ ((refl p).1, (refl p).2.2) * φ (p.1, p.2.2)) =
      φ (p.1, p.2.1) * φ (p.1, p.2.2) * (k p.1 * h (p.1, p.2.1) * h (p.1, p.2.2)) := by
    intro p
    simp only [refl]
    rw [NNReal.smul_def, smul_eq_mul]
    change (k p.1 * h (p.1, p.2.1) * h (p.1, p.2.2)) * (φ (p.1, p.2.1) * φ (p.1, p.2.2)) = _
    ring
  rw [integral_congr_ae (Eventually.of_forall e)]
  exact this

end SiteReflection

/-! ## 5. Push-forward: coarse reflection positivity from fine reflection positivity -/

section Pushforward

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- If reflection positivity holds on the fine side for a collection `A` of positive-side functions, the block map `V`
commutes with the reflection (`V ∘ Θ = Θ' ∘ V`), and the pull-back `F ∘ V` of each coarse positive-side function `F`
lies in `A`, then coarse reflection positivity holds for the push-forward measure. -/
theorem pushforward_reflection_positive (μ : Measure Ω) (Θ : Ω → Ω) (Θ' : E → E)
    (V : Ω → E) (hV : Measurable V) (hΘ' : Measurable Θ')
    (hcomm : ∀ ω, V (Θ ω) = Θ' (V ω))
    (A : Set (Ω → ℝ)) (hRP : ∀ f ∈ A, 0 ≤ ∫ ω, f (Θ ω) * f ω ∂μ)
    (F : E → ℝ) (hF : Measurable F) (hFA : (fun ω => F (V ω)) ∈ A) :
    0 ≤ ∫ e, F (Θ' e) * F e ∂(μ.map V) := by
  rw [integral_map (f := fun e => F (Θ' e) * F e) hV.aemeasurable
    ((hF.comp hΘ').mul hF).aestronglyMeasurable]
  have := hRP _ hFA
  simp only [hcomm] at this
  exact this

/-- Locality puts the pull-back on the positive side (abstract form): if `F ∘ V` factors through the positive-side
coordinates `πp`, it lies in `A = {f | f factors through πp}`. -/
theorem pullback_mem_positive {P : Type*} (πp : Ω → P) (V : Ω → E) (F : E → ℝ)
    (Vp : P → E) (hloc : ∀ ω, V ω = Vp (πp ω)) :
    (fun ω => F (V ω)) ∈ {f : Ω → ℝ | ∃ φ : P → ℝ, ∀ ω, f ω = φ (πp ω)} :=
  ⟨fun p => F (Vp p), fun ω => by simp [hloc ω]⟩

end Pushforward

/-! ### Bridge to the fields of the Theorem W structure -/

section Bridge

variable {Ω E E' : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace E']

/-- Consistency of type (B5): if `V_{n→m} = B ∘ V_{n→m+1}`, the push-forward probability measures are consistent
(the field `BlockHypotheses.consistent` of Theorem W). -/
theorem pushforward_consistent (μ : ProbabilityMeasure Ω) (V₁ : Ω → E') (B : E' → E)
    (V : Ω → E) (hV₁ : Measurable V₁) (hB : Measurable B) (hV : Measurable V)
    (hcomp : ∀ ω, V ω = B (V₁ ω)) :
    (μ.map hV₁.aemeasurable).map hB.aemeasurable = μ.map hV.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map, Measure.map_map hB hV₁]
  congr 1
  funext ω; exact (hcomp ω).symm

/-- Coarse reflection positivity for the push-forward probability measure (form of the field
`BlockHypotheses.reflection_positive` of Theorem W). -/
theorem pushforward_reflection_positive_prob (μ : ProbabilityMeasure Ω) (Θ : Ω → Ω) (Θ' : E → E)
    (V : Ω → E) (hV : Measurable V) (hΘ' : Measurable Θ')
    (hcomm : ∀ ω, V (Θ ω) = Θ' (V ω))
    (A : Set (Ω → ℝ)) (hRP : ∀ f ∈ A, 0 ≤ ∫ ω, f (Θ ω) * f ω ∂(μ : Measure Ω))
    (F : E → ℝ) (hF : Measurable F) (hFA : (fun ω => F (V ω)) ∈ A) :
    0 ≤ ∫ e, F (Θ' e) * F e ∂((μ.map hV.aemeasurable : ProbabilityMeasure E) : Measure E) := by
  rw [ProbabilityMeasure.toMeasure_map]
  exact pushforward_reflection_positive (μ : Measure Ω) Θ Θ' V hV hΘ' hcomm A hRP F hF hFA

/-- Push-forward of lattice symmetries: if `V ∘ σ = σ' ∘ V` and `μ` is `σ`-invariant, the push-forward is
`σ'`-invariant (the field `BlockHypotheses.symmetric` of Theorem W). -/
theorem pushforward_invariant (μ : Measure Ω) (σ : Ω → Ω) (σ' : E → E) (V : Ω → E)
    (hV : Measurable V) (hσ : Measurable σ) (hσ' : Measurable σ')
    (hμ : μ.map σ = μ) (hcomm : ∀ ω, V (σ ω) = σ' (V ω)) :
    (μ.map V).map σ' = μ.map V := by
  rw [Measure.map_map hσ' hV]
  have : σ' ∘ V = V ∘ σ := by funext ω; exact (hcomm ω).symm
  rw [this, ← Measure.map_map hV hσ, hμ]

end Bridge

/-! ## 6. Axiom check -/

#print axioms continuous_retract
#print axioms norm_retract_le
#print axioms retract_of_le
#print axioms retract_mul_unit
#print axioms covariant_mul
#print axioms mul_star_of_star_mul
#print axioms covariant_path
#print axioms covariant_average
#print axioms covariant_retract
#print axioms blockmap_equivariant
#print axioms equivariant_comp
#print axioms invariant_pullback
#print axioms continuous_path_prod
#print axioms continuous_link
#print axioms continuous_blockmap
#print axioms measurable_refl
#print axioms site_reflection_positive
#print axioms site_reflection_positive_measure
#print axioms pushforward_reflection_positive
#print axioms pullback_mem_positive
#print axioms pushforward_consistent
#print axioms pushforward_reflection_positive_prob
#print axioms pushforward_invariant

end LatticeBlockReflection
