import Mathlib

/-!
# Bounding the box-level KP per-site sum by fibre sums over plaquette configurations

Let `img X` be the box image of a plaquette configuration `X` (a finite set of plaquettes). If the activity `zB B` of a set of boxes `B` is
at most the sum of weights `Σ_{X : img X = B} w X` of plaquette configurations with image `B`, then

  `Σ_{B ∋ b} |zB B| e^{2|B|} ≤ Σ_{X : b ∈ img X} w X e^{2|img X|} ≤ Σ_{X : b ∈ img X} w X e^{2|X|}`

(the right inequality uses `|img X| ≤ |X|`). The left one is just re-summing over fibres.
`w X` is meant to be `(c ε_G(X))^{|X|}` from (H-sum); the values of `w` are supplied from outside (floating-point computation).
-/

namespace BoxFiberSiteSum

open Finset

variable {F Bx : Type*} [DecidableEq F] [DecidableEq Bx]

/-- Exchanging fibre sums: `Σ_{B ∈ S} Σ_{X ∈ U, img X = B} g X = Σ_{X ∈ U, img X ∈ S} g X`. -/
theorem fiber_swap (img : Finset F → Finset Bx) (U : Finset (Finset F)) (S : Finset (Finset Bx))
    (g : Finset F → ℝ) :
    ∑ B ∈ S, ∑ X ∈ U.filter (fun X => img X = B), g X
      = ∑ X ∈ U.filter (fun X => img X ∈ S), g X := by
  have hmaps : ∀ X ∈ U.filter (fun X => img X ∈ S), img X ∈ S := by
    intro X hX; exact (mem_filter.1 hX).2
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro B hB
  rw [filter_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext X
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; exact hB, h2⟩
  · rintro ⟨h1, _, h2⟩
    exact ⟨h1, h2⟩

/-- Box-level per-site sum ≤ fibre sum over plaquette configurations (exponential weight in box units). -/
theorem box_site_le_fiber (img : Finset F → Finset Bx) (UX : Finset (Finset F))
    (UB : Finset (Finset Bx)) (zB : Finset Bx → ℝ) (w : Finset F → ℝ) (b : Bx)
    (hzB : ∀ B ∈ UB, |zB B| ≤ ∑ X ∈ UX.filter (fun X => img X = B), w X) :
    ∑ B ∈ UB.filter (fun B => b ∈ B), |zB B| * Real.exp (2 * B.card)
      ≤ ∑ X ∈ UX.filter (fun X => img X ∈ UB.filter (fun B => b ∈ B)),
          w X * Real.exp (2 * (img X).card) := by
  calc ∑ B ∈ UB.filter (fun B => b ∈ B), |zB B| * Real.exp (2 * B.card)
      ≤ ∑ B ∈ UB.filter (fun B => b ∈ B),
          (∑ X ∈ UX.filter (fun X => img X = B), w X) * Real.exp (2 * B.card) := by
        apply sum_le_sum
        intro B hB
        exact mul_le_mul_of_nonneg_right (hzB B (mem_filter.1 hB).1) (Real.exp_pos _).le
    _ = ∑ B ∈ UB.filter (fun B => b ∈ B),
          ∑ X ∈ UX.filter (fun X => img X = B), w X * Real.exp (2 * (img X).card) := by
        apply sum_congr rfl
        intro B _
        rw [sum_mul]
        apply sum_congr rfl
        intro X hX
        rw [(mem_filter.1 hX).2]
    _ = ∑ X ∈ UX.filter (fun X => img X ∈ UB.filter (fun B => b ∈ B)),
          w X * Real.exp (2 * (img X).card) :=
        fiber_swap img UX _ (fun X => w X * Real.exp (2 * (img X).card))

/-- If the image is no larger than the configuration, the box-unit weight may be replaced by the plaquette-unit weight (`w ≥ 0`). -/
theorem box_site_le_face_weight (img : Finset F → Finset Bx) (UX : Finset (Finset F))
    (UB : Finset (Finset Bx)) (zB : Finset Bx → ℝ) (w : Finset F → ℝ) (b : Bx)
    (hw : ∀ X ∈ UX, 0 ≤ w X) (hcard : ∀ X ∈ UX, (img X).card ≤ X.card)
    (hzB : ∀ B ∈ UB, |zB B| ≤ ∑ X ∈ UX.filter (fun X => img X = B), w X) :
    ∑ B ∈ UB.filter (fun B => b ∈ B), |zB B| * Real.exp (2 * B.card)
      ≤ ∑ X ∈ UX.filter (fun X => b ∈ img X), w X * Real.exp (2 * X.card) := by
  refine le_trans (box_site_le_fiber img UX UB zB w b hzB) ?_
  calc ∑ X ∈ UX.filter (fun X => img X ∈ UB.filter (fun B => b ∈ B)),
          w X * Real.exp (2 * (img X).card)
      ≤ ∑ X ∈ UX.filter (fun X => img X ∈ UB.filter (fun B => b ∈ B)),
          w X * Real.exp (2 * X.card) := by
        apply sum_le_sum
        intro X hX
        have hX' := (mem_filter.1 hX).1
        apply mul_le_mul_of_nonneg_left _ (hw X hX')
        apply Real.exp_le_exp.2
        have : ((img X).card : ℝ) ≤ X.card := by exact_mod_cast hcard X hX'
        linarith
    _ ≤ ∑ X ∈ UX.filter (fun X => b ∈ img X), w X * Real.exp (2 * X.card) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro X hX
          rw [mem_filter] at hX ⊢
          exact ⟨hX.1, (mem_filter.1 hX.2).2⟩
        · intro X hX _
          exact mul_nonneg (hw X (mem_filter.1 hX).1) (Real.exp_pos _).le

/-- Box hsite form: if the right-hand sum is ≤ 1, the box-level KP per-site sum is ≤ 1 for every box b. -/
theorem box_hsite_of_fiber (img : Finset F → Finset Bx) (UX : Finset (Finset F))
    (UB : Finset (Finset Bx)) (zB : Finset Bx → ℝ) (w : Finset F → ℝ)
    (hzB : ∀ B ∈ UB, |zB B| ≤ ∑ X ∈ UX.filter (fun X => img X = B), w X)
    (hone : ∀ b, ∑ X ∈ UX.filter (fun X => img X ∈ UB.filter (fun B => b ∈ B)),
          w X * Real.exp (2 * (img X).card) ≤ 1) :
    ∀ b, ∑ B ∈ UB.filter (fun B => b ∈ B), |zB B| * Real.exp (2 * B.card) ≤ 1 := fun b =>
  le_trans (box_site_le_fiber img UX UB zB w b hzB) (hone b)

end BoxFiberSiteSum

#print axioms BoxFiberSiteSum.fiber_swap
#print axioms BoxFiberSiteSum.box_site_le_fiber
#print axioms BoxFiberSiteSum.box_site_le_face_weight
#print axioms BoxFiberSiteSum.box_hsite_of_fiber
