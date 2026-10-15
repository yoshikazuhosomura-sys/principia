import Mathlib

/-!
# Finite algebra behind the fixed-N confinement bound (note 18, paper 3)

1. `signed_sum` / `unsigned_sum`: summing independent sheet signs over blocks factorises,
   so the twist-summed bias is the product of the column biases (Proposition 1 of note 18a).
2. `prod_expand`, `binomial_bound`: the good/bad reduction (Lemma 2 of note 18a):
   pointwise `∏ ((1-η) + η x_t)` expands over subsets, and a chessboard bound `a S ≤ p^|S|`
   on the subset expectations gives `(1 - η + η p)^n`.
3. `exp_bound`: `(1 - y)^n ≤ exp (-(n*y))` for `0 ≤ y ≤ 1`.
-/

namespace ColumnChessboard

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sign-weighted sum over sheet configurations factorises into `∏ (Z⁺ - Z⁻)`. -/
theorem signed_sum (zp zm : ι → ℝ) :
    (∑ s : ι → Bool, (∏ i, (if s i then (1:ℝ) else -1)) * ∏ i, (if s i then zp i else zm i))
      = ∏ i, (zp i - zm i) := by
  have h : ∀ i, zp i - zm i = ∑ b : Bool, (if b then zp i else -zm i) := by
    intro i; simp [sub_eq_add_neg]
  rw [Finset.prod_congr rfl (fun i _ => h i), Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hs : s i <;> simp [hs]

/-- Unsigned sum over sheet configurations factorises into `∏ (Z⁺ + Z⁻)`. -/
theorem unsigned_sum (zp zm : ι → ℝ) :
    (∑ s : ι → Bool, ∏ i, (if s i then zp i else zm i)) = ∏ i, (zp i + zm i) := by
  have h : ∀ i, zp i + zm i = ∑ b : Bool, (if b then zp i else zm i) := by
    intro i; simp
  rw [Finset.prod_congr rfl (fun i _ => h i), Fintype.prod_sum]

omit [Fintype ι] in
/-- Pointwise expansion of `∏_{t∈s} ((1-η) + η x_t)` over subsets. -/
theorem prod_expand (s : Finset ι) (η : ℝ) (x : ι → ℝ) :
    ∏ t ∈ s, ((1 - η) + η * x t)
      = ∑ S ∈ s.powerset, η ^ S.card * (∏ t ∈ S, x t) * (1 - η) ^ (s.card - S.card) := by
  rw [show (fun t => (1 - η) + η * x t) = (fun t => η * x t + (1 - η)) from by
        funext t; ring]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.mem_powerset] at hS
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hS]

omit [Fintype ι] [DecidableEq ι] in
/-- Chessboard input `0 ≤ a S ≤ p ^ |S|` gives the binomial bound `(1 - η + η p) ^ |s|`. -/
theorem binomial_bound (s : Finset ι) (η p : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (a : Finset ι → ℝ) (ha : ∀ S ∈ s.powerset, a S ≤ p ^ S.card) :
    ∑ S ∈ s.powerset, η ^ S.card * a S * (1 - η) ^ (s.card - S.card)
      ≤ (1 - η + η * p) ^ s.card := by
  have h1 : 0 ≤ 1 - η := by linarith
  calc ∑ S ∈ s.powerset, η ^ S.card * a S * (1 - η) ^ (s.card - S.card)
      ≤ ∑ S ∈ s.powerset, (η * p) ^ S.card * (1 - η) ^ (s.card - S.card) := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        rw [mul_pow]
        have := ha S hS
        have hηp : 0 ≤ η ^ S.card := pow_nonneg hη0 _
        have hq : 0 ≤ (1 - η) ^ (s.card - S.card) := pow_nonneg h1 _
        have : η ^ S.card * a S ≤ η ^ S.card * p ^ S.card := mul_le_mul_of_nonneg_left this hηp
        exact mul_le_mul_of_nonneg_right this hq
    _ = (η * p + (1 - η)) ^ s.card := Finset.sum_pow_mul_eq_add_pow _ _ _
    _ = (1 - η + η * p) ^ s.card := by ring

/-- `(1 - y)^n ≤ exp (-(n*y))` for `0 ≤ y ≤ 1`. -/
theorem exp_bound (y : ℝ) (n : ℕ) (hy1 : y ≤ 1) :
    (1 - y) ^ n ≤ Real.exp (-(n * y)) := by
  have h0 : 0 ≤ 1 - y := by linarith
  have h1 : 1 - y ≤ Real.exp (-y) := by
    have := Real.add_one_le_exp (-y); linarith
  calc (1 - y) ^ n ≤ (Real.exp (-y)) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-(n * y)) := by rw [← Real.exp_nat_mul]; ring_nf

end ColumnChessboard

#print axioms ColumnChessboard.signed_sum
#print axioms ColumnChessboard.unsigned_sum
#print axioms ColumnChessboard.prod_expand
#print axioms ColumnChessboard.binomial_bound
#print axioms ColumnChessboard.exp_bound
