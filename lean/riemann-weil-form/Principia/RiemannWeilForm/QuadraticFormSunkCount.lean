import Mathlib

/-!
# Counting the eigenvalues of a symmetric form that lie below a threshold

This is the piece of linear algebra behind the following kind of argument.  One wants to
show that a symmetric quadratic form `W` on an `n`-dimensional space has many small
eigenvalues.  One produces a subspace `U` of codimension at most `k` (typically: the span
of a large family of near-band-limited vectors, cut down by `k` linear conditions) on which
`⟪x, W x⟫ ≤ ε‖x‖²`.  The conclusion is that at least `n - k` of the `n` eigenvalues of `W`
are `≤ ε`.

This is a corollary of the Courant–Fischer min–max principle, but no min–max principle is
needed for it: the span `V` of the eigenvectors whose eigenvalue exceeds `ε` carries a form
that is `> ε‖x‖²` off the origin, so `U ⊓ V = ⊥`, so `dim V ≤ k`.

* `SunkCount.card_le_of_form_le` — for an operator given with an orthonormal eigenbasis;
* `SunkCount.card_eigenvalues_le` — the same for `LinearMap.IsSymmetric.eigenvalues`.
-/

open Module Submodule Finset
local notation "⟪" x ", " y "⟫_ℝ" => inner ℝ x y

namespace SunkCount

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {T : E →ₗ[ℝ] E}

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Expansion of the quadratic form of a symmetric operator in an orthonormal eigenbasis. -/
theorem inner_apply_eq_sum (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ i, T (b i) = lam i • b i) (x : E) :
    ⟪x, T x⟫_ℝ = ∑ i, lam i * ⟪x, b i⟫_ℝ ^ 2 := by
  rw [← b.sum_inner_mul_inner x (T x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪b i, T x⟫_ℝ = ⟪T (b i), x⟫_ℝ := (hT (b i) x).symm
  rw [h1, hb i, real_inner_smul_left, real_inner_comm]
  ring

omit [DecidableEq ι] in
/-- Parseval, in the form used below. -/
theorem norm_sq_eq_sum (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm]
  ring

omit [DecidableEq ι] in
/-- A vector in the span of `b '' S` has no component along `b j` for `j ∉ S`. -/
theorem inner_eq_zero_of_mem_span (b : OrthonormalBasis ι ℝ E) (S : Finset ι) {j : ι}
    (hj : j ∉ S) {x : E} (hx : x ∈ Submodule.span ℝ ((⇑b) '' (↑S : Set ι))) :
    ⟪x, b j⟫_ℝ = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hiS, rfl⟩ := hy
      exact b.orthonormal.2 (fun h => hj (h ▸ hiS))
  | zero => simp
  | add u v _ _ hu hv => simp [inner_add_left, hu, hv]
  | smul c u _ hu => simp [real_inner_smul_left, hu]

/-- On the span of the eigenvectors indexed by `S`, all of whose eigenvalues exceed `ε`,
the quadratic form is strictly larger than `ε‖x‖²` away from the origin. -/
theorem lt_inner_of_mem_span (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ i, T (b i) = lam i • b i) (ε : ℝ) (S : Finset ι)
    (hS : ∀ i ∈ S, ε < lam i) {x : E}
    (hx : x ∈ Submodule.span ℝ ((⇑b) '' (↑S : Set ι))) (hx0 : x ≠ 0) :
    ε * ‖x‖ ^ 2 < ⟪x, T x⟫_ℝ := by
  classical
  have hzero : ∀ j : ι, j ∉ S → ⟪x, b j⟫_ℝ = 0 :=
    fun j hj => inner_eq_zero_of_mem_span b S hj hx
  rw [inner_apply_eq_sum hT b lam hb x, norm_sq_eq_sum b x, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ?_
  · by_cases hi : i ∈ S
    · exact mul_le_mul_of_nonneg_right (le_of_lt (hS i hi)) (sq_nonneg _)
    · rw [hzero i hi]; simp
  · have hex : ∃ i, ⟪x, b i⟫_ℝ ≠ 0 := by
      by_contra hcn
      have hc : ∀ i, ⟪x, b i⟫_ℝ = 0 := fun i => not_not.mp fun h => hcn ⟨i, h⟩
      apply hx0
      have h0 : ‖x‖ ^ 2 = 0 := by rw [norm_sq_eq_sum b x]; simp [hc]
      have h1 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
      exact norm_eq_zero.mp h1
    obtain ⟨i, hi⟩ := hex
    have hiS : i ∈ S := by
      by_contra h
      exact hi (hzero i h)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hpos : (0 : ℝ) < ⟪x, b i⟫_ℝ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
    exact mul_lt_mul_of_pos_right (hS i hiS) hpos

/-- If the quadratic form is `≤ ε‖x‖²` on a subspace `U` of codimension at most `k`, then any
set `S` of indices whose eigenvalues all exceed `ε` has at most `k` elements. -/
theorem card_le_of_form_le_aux [FiniteDimensional ℝ E]
    (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ i, T (b i) = lam i • b i) (ε : ℝ) (k : ℕ) (U : Submodule ℝ E)
    (hUdim : Fintype.card ι ≤ finrank ℝ U + k)
    (hUle : ∀ x ∈ U, ⟪x, T x⟫_ℝ ≤ ε * ‖x‖ ^ 2)
    (S : Finset ι) (hS : ∀ i ∈ S, ε < lam i) :
    #S ≤ k := by
  classical
  by_contra hcon0
  have hcon : k < #S := not_le.mp hcon0
  have hdimE : finrank ℝ E = Fintype.card ι := Module.finrank_eq_card_basis b.toBasis
  have hli : LinearIndependent ℝ (fun x : (↑S : Set ι) => b x) :=
    (b.orthonormal.linearIndependent).comp _ Subtype.val_injective
  have hVdim : finrank ℝ ↥(Submodule.span ℝ ((⇑b) '' (↑S : Set ι))) = #S := by
    rw [Set.image_eq_range, finrank_span_eq_card hli]
    simp
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U
    (Submodule.span ℝ ((⇑b) '' (↑S : Set ι)))
  have hle : finrank ℝ ↥(U ⊔ Submodule.span ℝ ((⇑b) '' (↑S : Set ι))) ≤ Fintype.card ι := by
    rw [← hdimE]; exact Submodule.finrank_le _
  have hpos : 0 < finrank ℝ ↥(U ⊓ Submodule.span ℝ ((⇑b) '' (↑S : Set ι))) := by omega
  have hne : (U ⊓ Submodule.span ℝ ((⇑b) '' (↑S : Set ι))) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  have h1 : ⟪x, T x⟫_ℝ ≤ ε * ‖x‖ ^ 2 := hUle x (Submodule.mem_inf.mp hxmem).1
  have h2 : ε * ‖x‖ ^ 2 < ⟪x, T x⟫_ℝ :=
    lt_inner_of_mem_span hT b lam hb ε S hS (Submodule.mem_inf.mp hxmem).2 hx0
  linarith

/-- **Counting the sunk eigenvalues.**  If `T` is symmetric with orthonormal eigenbasis `b`
and eigenvalues `lam`, and if `U` is a subspace of codimension at most `k` on which the
quadratic form of `T` is at most `ε‖x‖²`, then at least `(card ι) - k` of the eigenvalues
are `≤ ε`. -/
theorem card_le_of_form_le [FiniteDimensional ℝ E]
    (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ i, T (b i) = lam i • b i) (ε : ℝ) (k : ℕ) (U : Submodule ℝ E)
    (hUdim : Fintype.card ι ≤ finrank ℝ U + k)
    (hUle : ∀ x ∈ U, ⟪x, T x⟫_ℝ ≤ ε * ‖x‖ ^ 2) :
    Fintype.card ι ≤ #{i | lam i ≤ ε} + k := by
  classical
  have h := card_le_of_form_le_aux hT b lam hb ε k U hUdim hUle
    {i | ε < lam i} (fun i hi => (Finset.mem_filter.mp hi).2)
  have hcard : #{i | lam i ≤ ε} + #{i | ε < lam i} = Fintype.card ι := by
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun i => lam i ≤ ε)
    simpa [not_le, Finset.card_univ] using h2
  omega

end Basis

/-- The same statement for the sorted eigenvalues produced by Mathlib's spectral theorem. -/
theorem card_eigenvalues_le [FiniteDimensional ℝ E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (ε : ℝ) (k : ℕ) (U : Submodule ℝ E)
    (hUdim : n ≤ finrank ℝ U + k)
    (hUle : ∀ x ∈ U, ⟪x, T x⟫_ℝ ≤ ε * ‖x‖ ^ 2) :
    n ≤ #{i | hT.eigenvalues hn i ≤ ε} + k := by
  classical
  have hb : ∀ i, T (hT.eigenvectorBasis hn i) =
      hT.eigenvalues hn i • hT.eigenvectorBasis hn i := by
    intro i
    simp
  have h := card_le_of_form_le hT (hT.eigenvectorBasis hn) (hT.eigenvalues hn) hb ε k U
    (by simpa using hUdim) hUle
  simpa using h

end SunkCount

#print axioms SunkCount.card_le_of_form_le
#print axioms SunkCount.card_eigenvalues_le
