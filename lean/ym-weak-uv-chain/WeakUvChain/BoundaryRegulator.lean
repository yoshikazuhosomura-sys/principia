/-
Regulator for large sets: split the points of the image into "full blocks" and "partial blocks", and bound the number of partial
blocks by the number of block-internal boundary edges. Single file; checks with `import Mathlib` only.

  Points S, block map β : S → S′, blocks blk x′ = {x ∈ Sfin | β x = x′} (each with ≥ L_d points),
  edge set Edges ⊆ S × S. Internal boundary edges of a support A: ∂A = {(x, y) ∈ Edges | x ∈ A, y ∉ A, β x = β y}.
  (Connectivity) every partial block (meeting A but not contained in A) has at least one internal boundary edge
  (true if blocks are connected for the adjacency: a premise).
  ⇒ |β(A)| · L_d ≤ |A| + L_d · |∂A|, i.e. |β(A)| ≤ |A|/L_d + |∂A|.
  Size condition: for weights including the boundary, a|A| + c|∂A|, if a′/L_d ≤ a − b′ and a′ ≤ c then
  a′|β(A)| ≤ (a − b′)|A| + c|∂A| (gaining b′|A| ≥ b′ of the volume weight).
-/
import Mathlib

namespace BoundaryRegulator

open Finset

set_option linter.unusedSectionVars false

variable {S S' : Type*} [DecidableEq S] [DecidableEq S']

/-- Upper bound on the number of image points, with boundary term. -/
theorem image_card_boundary (β : S → S') (Sfin A : Finset S)
    (Edges : Finset (S × S)) (Ld : ℕ)
    (hblk : ∀ x', Ld ≤ (Sfin.filter (fun x => β x = x')).card)
    (hconn : ∀ x' ∈ A.image β, ¬ (Sfin.filter (fun x => β x = x') ⊆ A) →
      ∃ p ∈ Edges, p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2 ∧ β p.1 = x') :
    (A.image β).card * Ld ≤
      A.card + Ld * (Edges.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2)).card := by
  set Full := (A.image β).filter (fun x' => Sfin.filter (fun x => β x = x') ⊆ A) with hFull
  set Part := (A.image β).filter (fun x' => ¬ (Sfin.filter (fun x => β x = x') ⊆ A)) with hPart
  set Bd := Edges.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2) with hBd
  have hsplit : (A.image β).card = Full.card + Part.card := by
    rw [hFull, hPart]; exact (card_filter_add_card_filter_not _).symm
  -- full blocks: pairwise disjoint subsets of A, each with ≥ Ld points
  have hfull : Full.card * Ld ≤ A.card := by
    have hdisj : Set.PairwiseDisjoint (Full : Set S') (fun x' => Sfin.filter (fun x => β x = x')) := by
      intro x' _ y' _ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro x hx hy
      exact hne ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
    have hsub : Full.biUnion (fun x' => Sfin.filter (fun x => β x = x')) ⊆ A := by
      intro x hx
      obtain ⟨x', hx', hxx'⟩ := mem_biUnion.mp hx
      exact (mem_filter.mp hx').2 hxx'
    have hc := card_le_card hsub
    rw [card_biUnion hdisj] at hc
    calc Full.card * Ld = ∑ _x' ∈ Full, Ld := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x' ∈ Full, (Sfin.filter (fun x => β x = x')).card := sum_le_sum fun x' _ => hblk x'
      _ ≤ A.card := hc
  -- partial blocks: lie in the image of the boundary edges
  have hpart : Part.card ≤ Bd.card := by
    have hsub : Part ⊆ Bd.image (fun p => β p.1) := by
      intro x' hx'
      rw [hPart, mem_filter] at hx'
      obtain ⟨p, hp, h1, h2, h3, h4⟩ := hconn x' hx'.1 hx'.2
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, h1, h2, h3⟩, h4⟩
    exact le_trans (card_le_card hsub) card_image_le
  rw [hsplit]
  calc (Full.card + Part.card) * Ld = Full.card * Ld + Ld * Part.card := by ring
    _ ≤ A.card + Ld * Bd.card := Nat.add_le_add hfull (Nat.mul_le_mul_left Ld hpart)

/-- Real form: `|β(A)| ≤ |A|/Ld + |∂A|`. -/
theorem image_card_boundary_real (nB nA nBd : ℕ) (Ld : ℕ) (hLd : 1 ≤ Ld)
    (h : nB * Ld ≤ nA + Ld * nBd) : (nB : ℝ) ≤ nA / Ld + nBd := by
  have hL : (0 : ℝ) < Ld := by exact_mod_cast hLd
  have h' : (nB : ℝ) * Ld ≤ nA + Ld * nBd := by exact_mod_cast h
  rw [← mul_le_mul_iff_of_pos_right hL]
  have e : ((nA : ℝ) / Ld + nBd) * Ld = nA + Ld * nBd := by field_simp
  rw [e]; exact h'

/-- Size condition (weight including the boundary): if `|β(A)| ≤ |A|/Ld + |∂A|`, `0 ≤ a′`, `a′/Ld ≤ a − b′`, `a′ ≤ c`,
`|A|, |∂A| ≥ 0`, then `a′|β(A)| ≤ (a − b′)|A| + c|∂A|`. -/
theorem size_condition_boundary (nB nA nBd Ld a a' b' c : ℝ) (ha' : 0 ≤ a') (hL : 0 < Ld)
    (hnA : 0 ≤ nA) (hnBd : 0 ≤ nBd) (himg : nB ≤ nA / Ld + nBd)
    (h1 : a' / Ld ≤ a - b') (h2 : a' ≤ c) :
    a' * nB ≤ (a - b') * nA + c * nBd := by
  have e : a' * (nA / Ld + nBd) = (a' / Ld) * nA + a' * nBd := by field_simp
  have := mul_le_mul_of_nonneg_left himg ha'
  rw [e] at this
  have h3 : (a' / Ld) * nA ≤ (a - b') * nA := mul_le_mul_of_nonneg_right h1 hnA
  have h4 : a' * nBd ≤ c * nBd := mul_le_mul_of_nonneg_right h2 hnBd
  linarith

#print axioms image_card_boundary
#print axioms image_card_boundary_real
#print axioms size_condition_boundary

end BoundaryRegulator
