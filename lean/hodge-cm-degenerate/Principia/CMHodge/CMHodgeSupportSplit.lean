/-
  Finite-dimensional linear algebra and exact arithmetic behind the vanishing test for a
  degree-two class restricted to the complement of a codimension-two subset of a reducible
  divisor.  No geometry, no sheaves and no local cohomology appear: the geometric inputs
  (the local-cohomology exact sequence, the decomposition of the supported classes into
  pieces, and the injectivity of restriction to one component) enter as hypotheses.
  Nothing about the Hodge conjecture, algebraicity or semiregularity is asserted.

  Contents.
  1. Killing by an injective restriction: a map whose composite with an injective map is
     zero is zero; a supremum of subspaces each killed by an injective map is zero.
  2. Route A: if the kernel of a restriction map is the range of a map whose range lies in
     such a supremum, the restriction map is injective.
  3. Route B: two classes lying in disjoint subspaces that agree are both zero; if a further
     linear map sends the first to a nonzero vector, they cannot agree.
  4. Bookkeeping of the design (components, pieces, class sum, shared pairs) and the
     Koszul counts on double and triple intersections in the smallest case.
-/
import Mathlib

namespace SupportSplit

variable {K : Type*} [Field K]

/-! ### 1. Killing by an injective restriction -/

/-- If `r` is injective and `r ∘ ι = 0`, then `ι = 0`. -/
theorem eq_zero_of_comp_eq_zero {L V W : Type*}
    [AddCommGroup L] [Module K L] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (ι : L →ₗ[K] V) (r : V →ₗ[K] W) (hr : Function.Injective r)
    (h : r.comp ι = 0) : ι = 0 := by
  refine LinearMap.ext fun x => hr ?_
  have h1 := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1
  simp only [LinearMap.zero_apply, map_zero]
  exact h1

/-- A subspace contained in the kernel of an injective map is zero. -/
theorem eq_bot_of_le_ker {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K V) (r : V →ₗ[K] W) (hr : Function.Injective r)
    (hS : S ≤ LinearMap.ker r) : S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 := hS hx
  rw [LinearMap.mem_ker] at h1
  rw [Submodule.mem_bot]
  exact hr (by rw [h1, map_zero])

/-- A supremum of subspaces, each killed by some injective map, is zero. -/
theorem iSup_eq_bot_of_killed {ιt V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : ιt → Submodule K V) (r : ιt → V →ₗ[K] W)
    (hr : ∀ j, Function.Injective (r j)) (hS : ∀ j, S j ≤ LinearMap.ker (r j)) :
    (⨆ j, S j) = ⊥ := by
  have h0 : ∀ j, S j = ⊥ := fun j => eq_bot_of_le_ker (S j) (r j) (hr j) (hS j)
  simp [h0]

/-! ### 2. Route A -/

/-- The kernel of the restriction `rU` is the range of `T` (supported classes); that range
lies in the supremum of the pieces `S j`; each piece is killed by an injective restriction
`r j` to a component.  Then `rU` is injective. -/
theorem restriction_injective {ιt V VU W L : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup VU] [Module K VU]
    [AddCommGroup W] [Module K W] [AddCommGroup L] [Module K L]
    (rU : V →ₗ[K] VU) (T : L →ₗ[K] V)
    (hker : LinearMap.ker rU = LinearMap.range T)
    (S : ιt → Submodule K V) (hT : LinearMap.range T ≤ ⨆ j, S j)
    (r : ιt → V →ₗ[K] W) (hr : ∀ j, Function.Injective (r j))
    (hS : ∀ j, S j ≤ LinearMap.ker (r j)) :
    Function.Injective rU := by
  apply LinearMap.ker_eq_bot.mp
  rw [hker, eq_bot_iff]
  exact hT.trans (iSup_eq_bot_of_killed S r hr hS).le

/-- Consequently a nonzero class survives the restriction. -/
theorem survives {ιt V VU W L : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup VU] [Module K VU]
    [AddCommGroup W] [Module K W] [AddCommGroup L] [Module K L]
    (rU : V →ₗ[K] VU) (T : L →ₗ[K] V)
    (hker : LinearMap.ker rU = LinearMap.range T)
    (S : ιt → Submodule K V) (hT : LinearMap.range T ≤ ⨆ j, S j)
    (r : ιt → V →ₗ[K] W) (hr : ∀ j, Function.Injective (r j))
    (hS : ∀ j, S j ≤ LinearMap.ker (r j)) (β : V) (hβ : β ≠ 0) :
    rU β ≠ 0 := by
  intro h
  apply hβ
  apply restriction_injective rU T hker S hT r hr hS
  rw [h, map_zero]

/-! ### 3. Route B -/

/-- Two vectors in disjoint subspaces that agree are both zero. -/
theorem eq_zero_of_disjoint {M : Type*} [AddCommGroup M] [Module K M]
    (A B : Submodule K M) (hAB : Disjoint A B) (a b : M)
    (ha : a ∈ A) (hb : b ∈ B) (h : a = b) : a = 0 ∧ b = 0 := by
  have hbA : b ∈ A := by rw [← h]; exact ha
  have hm : b ∈ A ⊓ B := Submodule.mem_inf.mpr ⟨hbA, hb⟩
  rw [hAB.eq_bot, Submodule.mem_bot] at hm
  exact ⟨by rw [h, hm], hm⟩

/-- If a linear map `p` sends the first vector to a nonzero vector, the two local lifts
cannot be glued. -/
theorem no_gluing {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (A B : Submodule K M) (hAB : Disjoint A B) (p : M →ₗ[K] N) (a b : M)
    (ha : a ∈ A) (hb : b ∈ B) (hpa : p a ≠ 0) : a ≠ b := by
  intro h
  apply hpa
  rw [(eq_zero_of_disjoint A B hAB a b ha hb h).1, map_zero]

/-! ### 4. Bookkeeping and Koszul counts -/

/-- The trace form on `Z[θ]`, `θ³ + θ² − 6θ − 7 = 0`: `Tr(a + bθ + cθ²) = 3a − b + 13c`. -/
def tr (a b c : ℤ) : ℤ := 3 * a - b + 13 * c

theorem chosen_traces : tr 119 (-11) (-9) = 251 ∧ tr 12 4 2 = 58 := by
  unfold tr; norm_num

/-- Components: 3 conjugates × 2 copies, 3 conjugates × 3 copies, two rational ones and
one theta divisor per conjugacy class. -/
theorem components_count : 3 * 2 + 3 * 3 + 1 + 1 + 3 = 20 := by norm_num

/-- Three-dimensional pieces: the same, with the absorbing boxes (5 + 1 + 1 per class). -/
theorem pieces_count : 3 * 2 + 3 * 3 + 3 * (5 + 1 + 1) + 1 + 1 = 38 := by norm_num

/-- The class sum of the chosen components is exactly `g = 7560` (no residual). -/
theorem class_sum : 2 * tr 119 (-11) (-9) + 3 * tr 12 4 2 + 2798 + 4083 + 3 = 7560 := by
  unfold tr; norm_num

/-- Pairs of pieces sharing a divisor: the seven pieces on one theta divisor, per class. -/
theorem shared_pairs : 3 * Nat.choose 7 2 = 63 := by decide

/-- Each piece lies in exactly one component, so 19 components do not contain it. -/
theorem free_components : 20 - 1 = 19 := by norm_num

/-- `66 = C(12,2)`, and a kernel inside the 9-dimensional part forces rank `≥ 57 > 54`. -/
theorem rank_count : Nat.choose 12 2 = 66 ∧ 66 - 9 = 57 ∧ 54 < 57 := by decide

/-- Lefschetz range on a double intersection (dimension 4): `h⁰..h³ = 1, 6, 15, 20`. -/
theorem lefschetz_double :
    Nat.choose 6 0 = 1 ∧ Nat.choose 6 1 = 6 ∧ Nat.choose 6 2 = 15 ∧ Nat.choose 6 3 = 20 ∧
    (1 : ℤ) - 6 + 15 - 20 = -10 := by decide

/-- Smallest double intersection (two theta translates): `χ = 2⁶ − 1 − 1 = 62`, `h⁴ = 72`. -/
theorem chi_double_theta : (2 : ℤ) ^ 6 - 1 - 1 = 62 ∧ (62 : ℤ) + 10 = 72 := by norm_num

/-- Smallest triple intersection (three theta translates):
`χ = −3 + 3·2⁶ − 3⁶ = −540`, `h³ = 10 − χ = 550`. -/
theorem chi_triple_theta :
    -(3 : ℤ) + 3 * 2 ^ 6 - 3 ^ 6 = -540 ∧ (10 : ℤ) - (-540) = 550 := by norm_num

end SupportSplit

#print axioms SupportSplit.eq_zero_of_comp_eq_zero
#print axioms SupportSplit.eq_bot_of_le_ker
#print axioms SupportSplit.iSup_eq_bot_of_killed
#print axioms SupportSplit.restriction_injective
#print axioms SupportSplit.survives
#print axioms SupportSplit.eq_zero_of_disjoint
#print axioms SupportSplit.no_gluing
#print axioms SupportSplit.chosen_traces
#print axioms SupportSplit.components_count
#print axioms SupportSplit.pieces_count
#print axioms SupportSplit.class_sum
#print axioms SupportSplit.shared_pairs
#print axioms SupportSplit.free_components
#print axioms SupportSplit.rank_count
#print axioms SupportSplit.lefschetz_double
#print axioms SupportSplit.chi_double_theta
#print axioms SupportSplit.chi_triple_theta
