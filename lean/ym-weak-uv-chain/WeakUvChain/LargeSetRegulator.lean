/-
Basic form of the large-set regulator (remaining part of premise 3). Single file; checks with `import Mathlib` only.

  If a polymer support A splits into a union F of full blocks and a remainder R (A ⊆ F ∪ R), where every block of F is
  full (F is a union of fibres of β, each with exactly L_d sites), then |β(A)| ≤ |F|/L_d + |R|.
  If the boundary fraction satisfies |R| ≤ θ|A|, then |β(A)| ≤ (1/L_d + θ)|A|.
  The size condition a′|β(A)| ≤ a|A| − b holds with b = a − a′(1/L_d + θ) (when |A| ≥ 1 and the coefficient is nonnegative).
  If θ is small and a′(1/L_d + θ) < a − d ln L, a contraction ρ < 1 is obtained while keeping the weight (even a′ = a).
-/
import Mathlib

namespace LargeSetRegulator

open Finset

set_option linter.unusedSectionVars false

variable {S S' : Type*} [DecidableEq S] [DecidableEq S']

/-- Union of full blocks: if `F` is the union of the fibres over `β(F)`, each with `Ld` sites, then `|F| = Ld · |β(F)|`. -/
theorem full_blocks_card (β : S → S') (F : Finset S) (Ld : ℕ)
    (hfull : ∀ x' ∈ F.image β, (F.filter (fun x => β x = x')).card = Ld) :
    F.card = Ld * (F.image β).card := by
  rw [card_eq_sum_card_image β F]
  rw [sum_congr rfl hfull, sum_const, smul_eq_mul, mul_comm]

/-- Size of the image: if `A ⊆ F ∪ R` and `F` is a union of full blocks, then `|β(A)| · Ld ≤ |F| + Ld · |R|`. -/
theorem image_card_regulated (β : S → S') (A F R : Finset S) (Ld : ℕ)
    (hsub : A ⊆ F ∪ R)
    (hfull : ∀ x' ∈ F.image β, (F.filter (fun x => β x = x')).card = Ld) :
    (A.image β).card * Ld ≤ F.card + Ld * R.card := by
  have h1 : A.image β ⊆ F.image β ∪ R.image β := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rcases mem_union.mp (hsub hx) with h | h
    · exact mem_union_left _ (mem_image_of_mem β h)
    · exact mem_union_right _ (mem_image_of_mem β h)
  have h2 : (A.image β).card ≤ (F.image β).card + (R.image β).card :=
    le_trans (card_le_card h1) (card_union_le _ _)
  have h3 : (R.image β).card ≤ R.card := card_image_le
  have h4 := full_blocks_card β F Ld hfull
  calc (A.image β).card * Ld ≤ ((F.image β).card + (R.image β).card) * Ld :=
        Nat.mul_le_mul_right Ld h2
    _ = Ld * (F.image β).card + Ld * (R.image β).card := by ring
    _ ≤ F.card + Ld * R.card := by rw [← h4]; exact Nat.add_le_add_left (Nat.mul_le_mul_left Ld h3) _

/-- In terms of the boundary fraction: if `|F| ≤ |A|`, `|R| ≤ θ|A|`, `Ld ≥ 1` then `|β(A)| ≤ (1/Ld + θ)|A|`. -/
theorem image_card_fraction (β : S → S') (A F R : Finset S) (Ld : ℕ) (hLd : 1 ≤ Ld) (θ : ℝ)
    (hsub : A ⊆ F ∪ R)
    (hfull : ∀ x' ∈ F.image β, (F.filter (fun x => β x = x')).card = Ld)
    (hF : F.card ≤ A.card) (hR : (R.card : ℝ) ≤ θ * A.card) :
    ((A.image β).card : ℝ) ≤ (1 / Ld + θ) * A.card := by
  have h := image_card_regulated β A F R Ld hsub hfull
  have hL : (0 : ℝ) < Ld := by exact_mod_cast hLd
  have h' : ((A.image β).card : ℝ) * Ld ≤ F.card + Ld * R.card := by exact_mod_cast h
  have hF' : (F.card : ℝ) ≤ A.card := by exact_mod_cast hF
  rw [← mul_le_mul_iff_of_pos_right hL]
  have e : (1 / (Ld : ℝ) + θ) * A.card * Ld = A.card + θ * A.card * Ld := by field_simp
  rw [e]
  nlinarith

/-- Size condition: if `|β(A)| ≤ κ|A|` (κ = 1/Ld + θ), `a′ ≥ 0`, `a − a′κ ≥ 0`, `|A| ≥ 1`, then with
`b = a − a′κ`, `a′|β(A)| ≤ a|A| − b`. -/
theorem size_condition_regulated (nA nB a a' κ : ℝ) (ha' : 0 ≤ a') (hb : 0 ≤ a - a' * κ)
    (hA : 1 ≤ nA) (himg : nB ≤ κ * nA) :
    a' * nB ≤ a * nA - (a - a' * κ) := by
  have h1 : a' * nB ≤ a' * (κ * nA) := mul_le_mul_of_nonneg_left himg ha'
  nlinarith

/-- Contraction keeping the weight: if `a′ = a`, `κ = 1/Ld + θ`, `a(1 − κ) > d ln L` then `L^d e^{−a(1−κ)} < 1`. -/
theorem weight_preserving_contraction (a κ L : ℝ) (d : ℕ) (hL : 1 ≤ L)
    (h : (d : ℝ) * Real.log L < a * (1 - κ)) : L ^ d * Real.exp (-(a - a * κ)) < 1 := by
  have hLp : 0 < L := by linarith
  have e : L ^ d = Real.exp ((d : ℝ) * Real.log L) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hLp d)]
  rw [e, ← Real.exp_add, ← Real.exp_zero, Real.exp_lt_exp]
  nlinarith

#print axioms full_blocks_card
#print axioms image_card_regulated
#print axioms image_card_fraction
#print axioms size_condition_regulated
#print axioms weight_preserving_contraction

end LargeSetRegulator
