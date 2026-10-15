import Mathlib

/-!
# Quartic triangle inequality and row-class splitting (finite sums)

Finite-dimensional facts used to assemble an `ℓ⁴ → ℓ⁴` bound from pieces:
* two-term Titu (Cauchy–Schwarz) `(p + q)^2 ≤ (a + b) (p^2 / a + q^2 / b)` for `a, b > 0`;
* its quartic iterate `(x + y)^4 ≤ (a + b)^3 (x^4 / a^3 + y^4 / b^3)`;
* quartic triangle inequality without roots: if `∑ x^4 ≤ a^4 S` and `∑ y^4 ≤ b^4 S`
  (`a, b > 0`) then `∑ (x + y)^4 ≤ (a + b)^4 S` (the near / tail split of an operator);
* row-class splitting: if the rows are split into classes and each class satisfies
  `∑_{q ∈ class c} φ_q^4 ≤ M_c S`, then `∑_q φ_q^4 ≤ (∑_c M_c) S`.
No lattice, group or interpolation theorem is formalised here.
-/

namespace LatticeGauge.QuarticSplit

open Finset

variable {ι κ : Type*}

theorem titu_two (p q a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (p + q) ^ 2 ≤ (a + b) * (p ^ 2 / a + q ^ 2 / b) := by
  rw [div_add_div _ _ ha.ne' hb.ne', mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (b * p - a * q), mul_pos ha hb]

theorem quartic_two (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (x + y) ^ 4 ≤ (a + b) ^ 3 * (x ^ 4 / a ^ 3 + y ^ 4 / b ^ 3) := by
  have h1 := titu_two x y a b ha hb
  have h2 := titu_two (x ^ 2 / a) (y ^ 2 / b) a b ha hb
  have e2 : (x ^ 2 / a) ^ 2 / a + (y ^ 2 / b) ^ 2 / b = x ^ 4 / a ^ 3 + y ^ 4 / b ^ 3 := by
    field_simp
  rw [e2] at h2
  have hab : 0 < a + b := by linarith
  have hn : 0 ≤ x ^ 2 / a + y ^ 2 / b := by positivity
  have h1' : ((x + y) ^ 2) ^ 2 ≤ ((a + b) * (x ^ 2 / a + y ^ 2 / b)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  calc (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
    _ ≤ ((a + b) * (x ^ 2 / a + y ^ 2 / b)) ^ 2 := h1'
    _ = (a + b) ^ 2 * (x ^ 2 / a + y ^ 2 / b) ^ 2 := by ring
    _ ≤ (a + b) ^ 2 * ((a + b) * (x ^ 4 / a ^ 3 + y ^ 4 / b ^ 3)) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (a + b) ^ 3 * (x ^ 4 / a ^ 3 + y ^ 4 / b ^ 3) := by ring

theorem quartic_triangle (s : Finset ι) (x y : ι → ℝ) (a b S : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : ∑ i ∈ s, x i ^ 4 ≤ a ^ 4 * S) (hy : ∑ i ∈ s, y i ^ 4 ≤ b ^ 4 * S) :
    ∑ i ∈ s, (x i + y i) ^ 4 ≤ (a + b) ^ 4 * S := by
  have hpt : ∀ i ∈ s, (x i + y i) ^ 4 ≤ (a + b) ^ 3 * (x i ^ 4 / a ^ 3 + y i ^ 4 / b ^ 3) :=
    fun i _ => quartic_two (x i) (y i) a b ha hb
  have ha3 : 0 < a ^ 3 := by positivity
  have hb3 : 0 < b ^ 3 := by positivity
  have hsx : (∑ i ∈ s, x i ^ 4) / a ^ 3 ≤ a * S := by
    rw [div_le_iff₀ ha3]; nlinarith
  have hsy : (∑ i ∈ s, y i ^ 4) / b ^ 3 ≤ b * S := by
    rw [div_le_iff₀ hb3]; nlinarith
  calc ∑ i ∈ s, (x i + y i) ^ 4
      ≤ ∑ i ∈ s, (a + b) ^ 3 * (x i ^ 4 / a ^ 3 + y i ^ 4 / b ^ 3) := sum_le_sum hpt
    _ = (a + b) ^ 3 * ((∑ i ∈ s, x i ^ 4) / a ^ 3 + (∑ i ∈ s, y i ^ 4) / b ^ 3) := by
        rw [← mul_sum, sum_add_distrib, sum_div, sum_div]
    _ ≤ (a + b) ^ 3 * (a * S + b * S) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hsx hsy) (by positivity)
    _ = (a + b) ^ 4 * S := by ring

theorem class_split [DecidableEq κ] (s : Finset ι) (t : Finset κ) (cls : ι → κ)
    (hmap : ∀ i ∈ s, cls i ∈ t) (φ : ι → ℝ) (M : κ → ℝ) (S : ℝ)
    (hc : ∀ c ∈ t, ∑ i ∈ s.filter (fun i => cls i = c), φ i ^ 4 ≤ M c * S) :
    ∑ i ∈ s, φ i ^ 4 ≤ (∑ c ∈ t, M c) * S := by
  rw [← sum_fiberwise_of_maps_to hmap, sum_mul]
  exact sum_le_sum hc

end LatticeGauge.QuarticSplit

#print axioms LatticeGauge.QuarticSplit.titu_two
#print axioms LatticeGauge.QuarticSplit.quartic_two
#print axioms LatticeGauge.QuarticSplit.quartic_triangle
#print axioms LatticeGauge.QuarticSplit.class_split
