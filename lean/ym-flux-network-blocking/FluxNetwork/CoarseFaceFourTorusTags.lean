import Mathlib

/-!
# Global flux tags on the coarse periodic 4-torus (finite linear algebra)

Coarse sites `Site n = Fin 4 → ZMod n` (a periodic 4-torus of side `n`), coarse links `Site n × Fin 4`,
coarse faces `Site n × Plane` (planes `μ < ν`, six of them), coarse cubes `Site n × Cube` (`a < b < c`).
`Dc` is the face angle of a link field, `d2` is the Bianchi map (signed boundary of a cube).
With the standard dot product, the tags are `ker d2 ∩ (range Dc)ᗮ` — the same subspace as
`CoarseFaceHodgeSplit.tags` (`ker d2 ⊓ ker Dc†`) for the Euclidean structure.

Proved here (for every side `n ≥ 1`):
* `bianchi` : `d2 ∘ Dc = 0`;
* `flux_mem_tags` : the six uniform fluxes (1 on every face of one plane) are tags;
* `flux_linearIndependent`, `six_le_finrank_tags` : they are independent, so `dim tags ≥ 6`;
* `finrank_ker_d2_ge` : `dim ker d2 ≥ rank Dc + 6` (curvatures and tags meet only in zero, both lie in `ker d2`).
The equality `dim tags = 6` is not proved here (it is the second Betti number of the 4-torus).
-/

set_option linter.unusedSectionVars false

open BigOperators

namespace CoarseFaceFourTorusTags

variable (n : ℕ) [NeZero n]

abbrev Site := Fin 4 → ZMod n
abbrev Plane := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev Cube := {t : Fin 4 × Fin 4 × Fin 4 // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

/-- Unit step along the axis `μ`. -/
def e (μ : Fin 4) : Site n := Pi.single μ 1

def pab (t : Cube) : Plane := ⟨(t.1.1, t.1.2.1), t.2.1⟩
def pac (t : Cube) : Plane := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
def pbc (t : Cube) : Plane := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩

/-- Face angle of a coarse link field. -/
def Dc : ((Site n × Fin 4) → ℝ) →ₗ[ℝ] ((Site n × Plane) → ℝ) where
  toFun u := fun x => u (x.1, x.2.1.1) + u (x.1 + e n x.2.1.1, x.2.1.2)
    - u (x.1 + e n x.2.1.2, x.2.1.1) - u (x.1, x.2.1.2)
  map_add' := by intro u v; funext x; simp only [Pi.add_apply]; ring
  map_smul' := by intro c u; funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Bianchi map: signed boundary of the cube `(a,b,c)`. -/
def d2 : ((Site n × Plane) → ℝ) →ₗ[ℝ] ((Site n × Cube) → ℝ) where
  toFun b := fun y =>
    (b (y.1 + e n y.2.1.2.2, pab y.2) - b (y.1, pab y.2))
    - (b (y.1 + e n y.2.1.2.1, pac y.2) - b (y.1, pac y.2))
    + (b (y.1 + e n y.2.1.1, pbc y.2) - b (y.1, pbc y.2))
  map_add' := by intro u v; funext x; simp only [Pi.add_apply]; ring
  map_smul' := by intro c u; funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The standard dot product on a finite coordinate space. -/
def dot {ι : Type*} [Fintype ι] (f g : ι → ℝ) : ℝ := ∑ i, f i * g i

theorem bianchi (u : (Site n × Fin 4) → ℝ) : d2 n (Dc n u) = 0 := by
  funext y
  obtain ⟨X, ⟨⟨a, b, c⟩, hab, hbc⟩⟩ := y
  simp only [d2, Dc, pab, pac, pbc, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  have h1 : X + e n c + e n a = X + e n a + e n c := by abel
  have h2 : X + e n c + e n b = X + e n b + e n c := by abel
  have h3 : X + e n b + e n a = X + e n a + e n b := by abel
  rw [h1, h2, h3]
  ring

/-- The tags: Bianchi-closed faces orthogonal to every coarse-link curvature. -/
def tags : Submodule ℝ ((Site n × Plane) → ℝ) where
  carrier := {b | d2 n b = 0 ∧ ∀ u, dot (Dc n u) b = 0}
  add_mem' := by
    rintro b b' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨by rw [map_add, h1, h1', add_zero], fun u => ?_⟩
    have := h2 u; have := h2' u
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    linarith
  zero_mem' := ⟨map_zero _, fun u => by simp [dot]⟩
  smul_mem' := by
    rintro c b ⟨h1, h2⟩
    refine ⟨by rw [map_smul, h1, smul_zero], fun u => ?_⟩
    have := h2 u
    simp only [dot, Pi.smul_apply, smul_eq_mul] at *
    rw [show (∑ i, Dc n u i * (c * b i)) = c * ∑ i, Dc n u i * b i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring), this, mul_zero]

/-- The uniform flux through the plane `p`: 1 on every coarse face of that plane. -/
def flux (p : Plane) : (Site n × Plane) → ℝ := fun x => if x.2 = p then 1 else 0

lemma sum_shift (f : Site n → ℝ) (a : Site n) : ∑ X, f (X + a) = ∑ X, f X :=
  Equiv.sum_comp (Equiv.addRight a) f

theorem d2_flux (p : Plane) : d2 n (flux n p) = 0 := by
  funext y
  simp [d2, flux]

theorem dot_Dc_flux (u : (Site n × Fin 4) → ℝ) (p : Plane) : dot (Dc n u) (flux n p) = 0 := by
  unfold dot flux
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Dc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_shift n (fun X => u (X, p.1.2)) (e n p.1.1), sum_shift n (fun X => u (X, p.1.1)) (e n p.1.2)]
  ring

theorem flux_mem_tags (p : Plane) : flux n p ∈ tags n :=
  ⟨d2_flux n p, fun u => dot_Dc_flux n u p⟩

theorem flux_linearIndependent : LinearIndependent ℝ (flux n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrFun hg (0, q)
  simpa [flux, Finset.sum_apply] using h

theorem card_plane : Fintype.card Plane = 6 := by decide

theorem six_le_finrank_tags : 6 ≤ Module.finrank ℝ (tags n) := by
  have hspan : Submodule.span ℝ (Set.range (flux n)) ≤ tags n :=
    Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact flux_mem_tags n p)
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card (flux_linearIndependent n), card_plane] at h1
  exact h1

theorem range_le_ker : LinearMap.range (Dc n) ≤ LinearMap.ker (d2 n) := by
  rintro _ ⟨u, rfl⟩
  exact bianchi n u

theorem tags_le_ker : tags n ≤ LinearMap.ker (d2 n) := fun _ hb => hb.1

theorem disjoint_range_tags : Disjoint (LinearMap.range (Dc n)) (tags n) := by
  rw [Submodule.disjoint_def]
  rintro b ⟨u, rfl⟩ hb
  have h0 : dot (Dc n u) (Dc n u) = 0 := hb.2 u
  unfold dot at h0
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (Dc n u i))).mp h0
  funext i
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

/-- `dim ker d2 ≥ rank Dc + 6` on the coarse periodic 4-torus of any side. -/
theorem finrank_ker_d2_ge :
    Module.finrank ℝ (LinearMap.range (Dc n)) + 6 ≤ Module.finrank ℝ (LinearMap.ker (d2 n)) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (Dc n)) (tags n)
  rw [(disjoint_range_tags n).eq_bot, finrank_bot] at e1
  have h2 := Submodule.finrank_mono (sup_le (range_le_ker n) (tags_le_ker n))
  have h3 := six_le_finrank_tags n
  omega

end CoarseFaceFourTorusTags

#print axioms CoarseFaceFourTorusTags.bianchi
#print axioms CoarseFaceFourTorusTags.flux_mem_tags
#print axioms CoarseFaceFourTorusTags.flux_linearIndependent
#print axioms CoarseFaceFourTorusTags.six_le_finrank_tags
#print axioms CoarseFaceFourTorusTags.disjoint_range_tags
#print axioms CoarseFaceFourTorusTags.finrank_ker_d2_ge
