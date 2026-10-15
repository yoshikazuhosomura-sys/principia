import Mathlib

/-!
# Coarse faces split into coarse-link curvatures and global flux tags (finite-dimensional)

Linear algebra behind the change of coarse variables on a periodic lattice:
`L` = coarse links, `F` = coarse faces, `C` = coarse cubes, `Dc : L → F` (face angle of a link field),
`d2 : F → C` (Bianchi: sum of the six faces of a cube), with `d2 ∘ Dc = 0`.
Then the Bianchi kernel splits orthogonally as `ker d2 = range Dc ⊕ tags`, where
`tags = ker d2 ⊓ ker Dcᵀ` (the harmonic faces: on a 3-torus these are the global fluxes).
A fine-field statement of the same shape: a plaquette background `b` with `Dᵀ b = 0`
adds no cross term, `‖D x + b‖² = ‖D x‖² + ‖b‖²`.
-/

set_option linter.unusedSectionVars false

open LinearMap Submodule

namespace CoarseFaceHodgeSplit

variable {L F C : Type*}
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]

/-- The global tags: Bianchi-closed faces orthogonal to every coarse-link curvature. -/
noncomputable def tags (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) : Submodule ℝ F :=
  LinearMap.ker d2 ⊓ LinearMap.ker (LinearMap.adjoint Dc)

theorem range_le_ker (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) (h : d2 ∘ₗ Dc = 0) :
    LinearMap.range Dc ≤ LinearMap.ker d2 := by
  rintro _ ⟨u, rfl⟩
  have := LinearMap.congr_fun h u
  simpa using this

/-- Spanning: every Bianchi-closed face field is a coarse-link curvature plus a tag. -/
theorem range_sup_tags (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) (h : d2 ∘ₗ Dc = 0) :
    LinearMap.range Dc ⊔ tags Dc d2 = LinearMap.ker d2 := by
  have key := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (range_le_ker Dc d2 h)
  rw [LinearMap.orthogonal_range] at key
  rw [tags, inf_comm]
  exact key

/-- The tags are orthogonal to every coarse-link curvature. -/
theorem tags_le_orthogonal (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) :
    tags Dc d2 ≤ (LinearMap.range Dc)ᗮ := by
  rw [LinearMap.orthogonal_range]
  exact inf_le_right

/-- Independence: the two pieces meet only in zero. -/
theorem disjoint_range_tags (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) :
    Disjoint (LinearMap.range Dc) (tags Dc d2) :=
  (Submodule.orthogonal_disjoint _).mono_right (tags_le_orthogonal Dc d2)

/-- Dimension count: `dim ker d2 = rank Dc + dim tags`. -/
theorem finrank_ker_eq (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) (h : d2 ∘ₗ Dc = 0) :
    Module.finrank ℝ (LinearMap.ker d2) =
      Module.finrank ℝ (LinearMap.range Dc) + Module.finrank ℝ (tags Dc d2) := by
  have e := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Dc) (tags Dc d2)
  rw [range_sup_tags Dc d2 h, (disjoint_range_tags Dc d2).eq_bot, finrank_bot] at e
  omega

/-- Uniqueness of the coordinates `(curvature, tag)`. -/
theorem decomp_unique (Dc : L →ₗ[ℝ] F) (d2 : F →ₗ[ℝ] C) {a a' t t' : F}
    (ha : a ∈ LinearMap.range Dc) (ha' : a' ∈ LinearMap.range Dc)
    (ht : t ∈ tags Dc d2) (ht' : t' ∈ tags Dc d2) (hsum : a + t = a' + t') :
    a = a' ∧ t = t' := by
  have h1 : a - a' = t' - t := by
    rw [sub_eq_sub_iff_add_eq_add, hsum]
    exact add_comm _ _
  have hm1 : a - a' ∈ LinearMap.range Dc := Submodule.sub_mem _ ha ha'
  have hm2 : a - a' ∈ tags Dc d2 := by rw [h1]; exact Submodule.sub_mem _ ht' ht
  have h0 : a - a' = 0 :=
    (Submodule.disjoint_def.mp (disjoint_range_tags Dc d2)) _ hm1 hm2
  refine ⟨sub_eq_zero.mp h0, ?_⟩
  rw [h0] at h1
  exact (sub_eq_zero.mp h1.symm).symm

/-- No cross term: a background `b` with `Dᵀ b = 0` adds `‖b‖²` and nothing else. -/
theorem norm_sq_add_harmonic {E P : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (D : E →ₗ[ℝ] P) (b : P) (hb : LinearMap.adjoint D b = 0) (x : E) :
    ‖D x + b‖ ^ 2 = ‖D x‖ ^ 2 + ‖b‖ ^ 2 := by
  have hi : inner ℝ (D x) b = 0 := by
    rw [← LinearMap.adjoint_inner_right, hb, inner_zero_right]
  rw [norm_add_sq_real, hi]
  ring

end CoarseFaceHodgeSplit

#print axioms CoarseFaceHodgeSplit.range_sup_tags
#print axioms CoarseFaceHodgeSplit.disjoint_range_tags
#print axioms CoarseFaceHodgeSplit.finrank_ker_eq
#print axioms CoarseFaceHodgeSplit.decomp_unique
#print axioms CoarseFaceHodgeSplit.norm_sq_add_harmonic
