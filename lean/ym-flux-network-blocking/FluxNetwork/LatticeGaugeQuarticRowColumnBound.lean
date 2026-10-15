import Mathlib

/-!
# Quartic row-column bound and the composition of quartic cones (finite sums)

Finite-dimensional facts used for the tree-level blocking step:
* weighted Cauchy-Schwarz and its quartic iterate `(∑ a x)^4 ≤ (∑ a)^3 ∑ a x^4` for `a ≥ 0`;
* the row-column (Schur) bound `∑_q (∑_P K q P θ P)^4 ≤ A^3 C ∑_P θ P^4`
  when every row has `∑_P |K q P| ≤ A` and every column has `∑_q |K q P| ≤ C`;
* a representative `K` that agrees with `F` on a set `S` transfers this bound to `F` on `S`;
* composition of quartic cones: if `|Qf φ| ≤ c ∑ φ^4` and `∑ (F θ)^4 ≤ M ∑ θ^4` on `S`,
  then `|Qf (F θ)| ≤ (c M) ∑ θ^4` on `S`.
No lattice, group or minimisation is formalised here.
-/

namespace LatticeGauge.QuarticRowColumn

open Finset

variable {ι : Type*}

theorem weighted_cs (s : Finset ι) (a x : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * x i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * x i ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul s ha
  · intro i hi; exact mul_nonneg (ha i hi) (sq_nonneg _)
  · intro i hi; nlinarith [sq_nonneg (a i * x i)]

theorem weighted_quartic (s : Finset ι) (a x : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * x i) ^ 4 ≤ (∑ i ∈ s, a i) ^ 3 * ∑ i ∈ s, a i * x i ^ 4 := by
  have h1 := weighted_cs s a x ha
  have h2 := weighted_cs s a (fun i => x i ^ 2) ha
  have hA : 0 ≤ ∑ i ∈ s, a i := sum_nonneg ha
  have hB : 0 ≤ ∑ i ∈ s, a i * x i ^ 2 := sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)
  have h2' : (∑ i ∈ s, a i * x i ^ 2) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * x i ^ 4 := by
    have : ∀ i ∈ s, a i * (x i ^ 2) ^ 2 = a i * x i ^ 4 := fun i _ => by ring
    simpa [sum_congr rfl this] using h2
  have hsq : ((∑ i ∈ s, a i * x i) ^ 2) ^ 2 ≤ ((∑ i ∈ s, a i) * ∑ i ∈ s, a i * x i ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  calc (∑ i ∈ s, a i * x i) ^ 4 = ((∑ i ∈ s, a i * x i) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ s, a i) * ∑ i ∈ s, a i * x i ^ 2) ^ 2 := hsq
    _ = (∑ i ∈ s, a i) ^ 2 * (∑ i ∈ s, a i * x i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i ∈ s, a i) ^ 2 * ((∑ i ∈ s, a i) * ∑ i ∈ s, a i * x i ^ 4) :=
        mul_le_mul_of_nonneg_left h2' (pow_nonneg hA 2)
    _ = (∑ i ∈ s, a i) ^ 3 * ∑ i ∈ s, a i * x i ^ 4 := by ring

variable {Q P : Type*} [Fintype Q] [Fintype P]

/-- one row: `(∑_P K θ)^4 ≤ A^3 ∑_P |K| θ^4` when `∑_P |K| ≤ A`. -/
theorem row_quartic (k θ : P → ℝ) (A : ℝ) (hrow : ∑ p, |k p| ≤ A) :
    (∑ p, k p * θ p) ^ 4 ≤ A ^ 3 * ∑ p, |k p| * θ p ^ 4 := by
  have habs : |∑ p, k p * θ p| ≤ ∑ p, |k p| * |θ p| := by
    calc |∑ p, k p * θ p| ≤ ∑ p, |k p * θ p| := abs_sum_le_sum_abs _ _
      _ = ∑ p, |k p| * |θ p| := by simp [abs_mul]
  have hw := weighted_quartic univ (fun p => |k p|) (fun p => |θ p|) (fun p _ => abs_nonneg _)
  have h0 : 0 ≤ ∑ p, |k p| := sum_nonneg fun p _ => abs_nonneg _
  have h4 : ∀ p, |θ p| ^ 4 = θ p ^ 4 := fun p => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hS : 0 ≤ ∑ p, |k p| * θ p ^ 4 :=
    sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (by positivity)
  calc (∑ p, k p * θ p) ^ 4 = |∑ p, k p * θ p| ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    _ ≤ (∑ p, |k p| * |θ p|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
    _ ≤ (∑ p, |k p|) ^ 3 * ∑ p, |k p| * |θ p| ^ 4 := hw
    _ = (∑ p, |k p|) ^ 3 * ∑ p, |k p| * θ p ^ 4 := by simp [h4]
    _ ≤ A ^ 3 * ∑ p, |k p| * θ p ^ 4 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hrow 3) hS

/-- row-column (Schur) bound in `ℓ⁴`. -/
theorem schur_quartic (K : Q → P → ℝ) (θ : P → ℝ) (A C : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ q, ∑ p, |K q p| ≤ A) (hcol : ∀ p, ∑ q, |K q p| ≤ C) :
    ∑ q, (∑ p, K q p * θ p) ^ 4 ≤ A ^ 3 * C * ∑ p, θ p ^ 4 := by
  have h1 : ∑ q, (∑ p, K q p * θ p) ^ 4 ≤ ∑ q, A ^ 3 * ∑ p, |K q p| * θ p ^ 4 :=
    sum_le_sum fun q _ => row_quartic (K q) θ A (hrow q)
  have h2 : ∑ q, A ^ 3 * ∑ p, |K q p| * θ p ^ 4 = A ^ 3 * ∑ p, θ p ^ 4 * ∑ q, |K q p| := by
    rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun q _ => by ring
  have h3 : ∑ p, θ p ^ 4 * ∑ q, |K q p| ≤ ∑ p, θ p ^ 4 * C :=
    sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hcol p) (by positivity)
  calc ∑ q, (∑ p, K q p * θ p) ^ 4 ≤ A ^ 3 * ∑ p, θ p ^ 4 * ∑ q, |K q p| := h1.trans_eq h2
    _ ≤ A ^ 3 * ∑ p, θ p ^ 4 * C := mul_le_mul_of_nonneg_left h3 (pow_nonneg hA 3)
    _ = A ^ 3 * C * ∑ p, θ p ^ 4 := by rw [← sum_mul]; ring

/-- a representative `K` that agrees with `F` on `S` carries the bound to `F` on `S`
(the finite form of "F_loc = F on im D_c"). -/
theorem representative_bound (F : (P → ℝ) → Q → ℝ) (S : Set (P → ℝ)) (K : Q → P → ℝ)
    (hagree : ∀ θ ∈ S, ∀ q, F θ q = ∑ p, K q p * θ p) (A C : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ q, ∑ p, |K q p| ≤ A) (hcol : ∀ p, ∑ q, |K q p| ≤ C) :
    ∀ θ ∈ S, ∑ q, F θ q ^ 4 ≤ A ^ 3 * C * ∑ p, θ p ^ 4 := by
  intro θ hθ
  have : ∑ q, F θ q ^ 4 = ∑ q, (∑ p, K q p * θ p) ^ 4 :=
    sum_congr rfl fun q _ => by rw [hagree θ hθ q]
  rw [this]; exact schur_quartic K θ A C hA hrow hcol

/-- composition of quartic cones: one step multiplies the cone constant by the `ℓ⁴` factor. -/
theorem cone_step (F : (P → ℝ) → Q → ℝ) (S : Set (P → ℝ)) (Qf : (Q → ℝ) → ℝ) (c M : ℝ)
    (hc : 0 ≤ c) (hQ : ∀ φ, |Qf φ| ≤ c * ∑ q, φ q ^ 4)
    (hM : ∀ θ ∈ S, ∑ q, F θ q ^ 4 ≤ M * ∑ p, θ p ^ 4) :
    ∀ θ ∈ S, |Qf (F θ)| ≤ (c * M) * ∑ p, θ p ^ 4 := by
  intro θ hθ
  calc |Qf (F θ)| ≤ c * ∑ q, F θ q ^ 4 := hQ _
    _ ≤ c * (M * ∑ p, θ p ^ 4) := mul_le_mul_of_nonneg_left (hM θ hθ) hc
    _ = (c * M) * ∑ p, θ p ^ 4 := by ring

/-- iterating the cone step along a chain of maps: constants multiply. -/
theorem cone_chain (n : ℕ) (c : ℝ) (M : ℕ → ℝ) (hc : 0 ≤ c) (hM : ∀ k, 0 ≤ M k)
    (x : ℕ → ℝ) (hx0 : |x 0| ≤ c) (hstep : ∀ k, |x (k + 1)| ≤ M k * |x k|) :
    |x n| ≤ c * ∏ k ∈ range n, M k := by
  induction n with
  | zero => simpa using hx0
  | succ n ih =>
    rw [prod_range_succ]
    calc |x (n + 1)| ≤ M n * |x n| := hstep n
      _ ≤ M n * (c * ∏ k ∈ range n, M k) := mul_le_mul_of_nonneg_left ih (hM n)
      _ = c * ((∏ k ∈ range n, M k) * M n) := by ring

end LatticeGauge.QuarticRowColumn

#print axioms LatticeGauge.QuarticRowColumn.weighted_quartic
#print axioms LatticeGauge.QuarticRowColumn.row_quartic
#print axioms LatticeGauge.QuarticRowColumn.schur_quartic
#print axioms LatticeGauge.QuarticRowColumn.representative_bound
#print axioms LatticeGauge.QuarticRowColumn.cone_step
#print axioms LatticeGauge.QuarticRowColumn.cone_chain
