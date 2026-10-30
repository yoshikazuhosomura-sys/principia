/-
Arithmetic of the merging term (the B z_k² term of the activity recursion): per-point sum of products over pairs of
polygons with intersecting supports. Single file; checks with `import Mathlib` only.

  For a nonnegative weight f with per-point sums Σ_{γ∋x} f(γ) ≤ ε and Σ_{γ∋x} f(γ)|γ| ≤ ε′,
  the sum of products over pairs (γ₁, γ₂) with intersecting supports, one of which contains x, is ≤ 2 ε ε′.
  (Assuming the merged polygon's activity is ≤ the product of the two activities, the contribution to the
  per-point sum of the coarse gas is of size z².)
-/
import Mathlib

namespace PolymerMerge

open Finset

set_option linter.unusedSectionVars false

variable {P S : Type*} [DecidableEq P] [DecidableEq S]

/-- Sum over polygons meeting the support `A` ≤ sum over points of `A` of the sum over polygons containing that point (nonnegative weights). -/
theorem intersect_sum_le' (supp : P → Finset S) (V : Finset P) (A : Finset S) (f : P → ℝ)
    (hf : ∀ γ, 0 ≤ f γ) :
    ∑ γ ∈ V, (if (A ∩ supp γ).Nonempty then f γ else 0) ≤
      ∑ x ∈ A, ∑ γ ∈ V.filter (fun s => x ∈ supp s), f γ := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro γ _
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    rw [mem_inter] at hx
    have hle : (if x ∈ supp γ then f γ else 0) ≤ ∑ y ∈ A, if y ∈ supp γ then f γ else 0 :=
      single_le_sum (f := fun y => if y ∈ supp γ then f γ else 0)
        (fun y _ => by split_ifs <;> simp [hf]) hx.1
    simpa [hx.2] using hle
  · exact sum_nonneg fun y _ => by split_ifs <;> simp [hf]

/-- One side: the sum of products over pairs with intersecting supports and `x ∈ supp γ₁` is ≤ ε ε′. -/
theorem one_side_le (supp : P → Finset S) (f : P → ℝ) (hf : ∀ γ, 0 ≤ f γ) (U : Finset P)
    (ε ε' : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ x, ∑ γ ∈ U.filter (fun s => x ∈ supp s), f γ ≤ ε)
    (h2 : ∀ x, ∑ γ ∈ U.filter (fun s => x ∈ supp s), f γ * (supp γ).card ≤ ε') (x : S) :
    ∑ γ₁ ∈ U.filter (fun s => x ∈ supp s),
      f γ₁ * ∑ γ₂ ∈ U, (if (supp γ₁ ∩ supp γ₂).Nonempty then f γ₂ else 0) ≤ ε * ε' := by
  have hinner : ∀ γ₁, ∑ γ₂ ∈ U, (if (supp γ₁ ∩ supp γ₂).Nonempty then f γ₂ else 0) ≤
      (supp γ₁).card * ε := by
    intro γ₁
    refine le_trans (intersect_sum_le' supp U (supp γ₁) f hf) ?_
    calc ∑ y ∈ supp γ₁, ∑ γ ∈ U.filter (fun s => y ∈ supp s), f γ ≤ ∑ _y ∈ supp γ₁, ε :=
          sum_le_sum fun y _ => h1 y
      _ = (supp γ₁).card * ε := by simp
  calc ∑ γ₁ ∈ U.filter (fun s => x ∈ supp s),
        f γ₁ * ∑ γ₂ ∈ U, (if (supp γ₁ ∩ supp γ₂).Nonempty then f γ₂ else 0)
      ≤ ∑ γ₁ ∈ U.filter (fun s => x ∈ supp s), f γ₁ * ((supp γ₁).card * ε) :=
        sum_le_sum fun γ₁ _ => mul_le_mul_of_nonneg_left (hinner γ₁) (hf γ₁)
    _ = ε * ∑ γ₁ ∈ U.filter (fun s => x ∈ supp s), f γ₁ * (supp γ₁).card := by
        rw [mul_sum]; refine sum_congr rfl fun γ₁ _ => ?_; ring
    _ ≤ ε * ε' := mul_le_mul_of_nonneg_left (h2 x) hε

/-- Merging term: the sum of products over pairs with intersecting supports, one containing `x`, is ≤ 2 ε ε′. -/
theorem merge_pairs_le (supp : P → Finset S) (f : P → ℝ) (hf : ∀ γ, 0 ≤ f γ) (U : Finset P)
    (ε ε' : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ x, ∑ γ ∈ U.filter (fun s => x ∈ supp s), f γ ≤ ε)
    (h2 : ∀ x, ∑ γ ∈ U.filter (fun s => x ∈ supp s), f γ * (supp γ).card ≤ ε') (x : S) :
    ∑ p ∈ (U ×ˢ U).filter (fun p => (supp p.1 ∩ supp p.2).Nonempty ∧
        (x ∈ supp p.1 ∨ x ∈ supp p.2)), f p.1 * f p.2 ≤ 2 * ε * ε' := by
  -- Bound the pair sum by the part with x ∈ supp p.1 plus the part with x ∈ supp p.2
  have hsplit : ∀ p : P × P, (if (supp p.1 ∩ supp p.2).Nonempty ∧ (x ∈ supp p.1 ∨ x ∈ supp p.2)
      then f p.1 * f p.2 else 0) ≤
      (if x ∈ supp p.1 then f p.1 * (if (supp p.1 ∩ supp p.2).Nonempty then f p.2 else 0) else 0) +
      (if x ∈ supp p.2 then f p.2 * (if (supp p.2 ∩ supp p.1).Nonempty then f p.1 else 0) else 0) := by
    intro p
    have h12 := hf p.1; have h22 := hf p.2
    have hcomm : (supp p.2 ∩ supp p.1).Nonempty ↔ (supp p.1 ∩ supp p.2).Nonempty := by
      rw [inter_comm]
    by_cases hI : (supp p.1 ∩ supp p.2).Nonempty <;> by_cases ha : x ∈ supp p.1 <;>
      by_cases hb : x ∈ supp p.2 <;> simp [hI, ha, hb, hcomm] <;> nlinarith [mul_nonneg h12 h22]
  rw [sum_filter, sum_product]
  have hA : ∑ γ₁ ∈ U, ∑ γ₂ ∈ U,
      (if x ∈ supp γ₁ then f γ₁ * (if (supp γ₁ ∩ supp γ₂).Nonempty then f γ₂ else 0) else 0) ≤
      ε * ε' := by
    have := one_side_le supp f hf U ε ε' hε h1 h2 x
    rw [sum_filter] at this
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl fun γ₁ _ => ?_
    split_ifs with h
    · rw [mul_sum]
    · simp
  have hB : ∑ γ₁ ∈ U, ∑ γ₂ ∈ U,
      (if x ∈ supp γ₂ then f γ₂ * (if (supp γ₂ ∩ supp γ₁).Nonempty then f γ₁ else 0) else 0) ≤
      ε * ε' := by
    rw [sum_comm]
    have := one_side_le supp f hf U ε ε' hε h1 h2 x
    rw [sum_filter] at this
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl fun γ₂ _ => ?_
    split_ifs with h
    · rw [mul_sum]
    · simp
  calc ∑ γ₁ ∈ U, ∑ γ₂ ∈ U, (if (supp (γ₁, γ₂).1 ∩ supp (γ₁, γ₂).2).Nonempty ∧
          (x ∈ supp (γ₁, γ₂).1 ∨ x ∈ supp (γ₁, γ₂).2) then f (γ₁, γ₂).1 * f (γ₁, γ₂).2 else 0)
      ≤ ∑ γ₁ ∈ U, ∑ γ₂ ∈ U,
          ((if x ∈ supp γ₁ then f γ₁ * (if (supp γ₁ ∩ supp γ₂).Nonempty then f γ₂ else 0) else 0) +
          (if x ∈ supp γ₂ then f γ₂ * (if (supp γ₂ ∩ supp γ₁).Nonempty then f γ₁ else 0) else 0)) :=
        sum_le_sum fun γ₁ _ => sum_le_sum fun γ₂ _ => hsplit (γ₁, γ₂)
    _ = _ := by simp_rw [sum_add_distrib]
    _ ≤ ε * ε' + ε * ε' := add_le_add hA hB
    _ = 2 * ε * ε' := by ring

#print axioms intersect_sum_le'
#print axioms one_side_le
#print axioms merge_pairs_le

end PolymerMerge
