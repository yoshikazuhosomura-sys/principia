import Mathlib

/-!
# 三種の尾（平ら・指数・冪）の距離の重みつき和の有界性の分類（有限の帳簿）

非局所の重み q : ℕ → ℝ（距離 r の係数）について、距離の重みつきの部分和 Σ_{r<R} r·|q r| が
R（＝体積）に一様に有界かどうかを、尾の型ごとに述べる。格子・群・測度は入っていない。

* 平ら：q r = c（距離に依らない）なら 2·Σ_{r<R} r·c = R(R−1)c。c > 0 なら上に有界でない。
* 指数：|q r| ≤ C ρ^r（0 ≤ ρ < 1）なら Σ_{r<R} r|q r| ≤ C ρ/(1−ρ)²（R に依らない）。
* 冪：|q n| ≤ C (n^s)⁻¹ で s > 1 なら Σ_{n<R} |q n| ≤ C Σ' (n^s)⁻¹（R に依らない）。
  s ≤ 1 なら Σ_{n<R} (n^s)⁻¹ は上に有界でない。
  （d 次元の格子の殻の重複度 r^{d−1} と距離の重み r を掛けた r^{−p} の尾は s = p − d に当たる：紙。）
-/

namespace LatticeGaugeTailTypeClassification

open Finset

/-- 平ら：距離に依らない係数の重みつき和は R(R−1)c/2。 -/
theorem flat_weighted_sum (c : ℝ) (R : ℕ) :
    2 * ∑ r ∈ range R, (r : ℝ) * c = (R : ℝ) * ((R : ℝ) - 1) * c := by
  induction R with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- 平ら：c > 0 なら重みつき和は上に有界でない。 -/
theorem flat_weighted_unbounded {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∃ R : ℕ, M < ∑ r ∈ range R, (r : ℝ) * c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (2 * M / c) + 1)
  refine ⟨n, ?_⟩
  have h := flat_weighted_sum c n
  have hn1 : (1 : ℝ) < n := by
    have : (0 : ℝ) ≤ max 0 (2 * M / c) := le_max_left _ _
    linarith
  have hn2 : 2 * M / c < (n : ℝ) - 1 := by
    have : 2 * M / c ≤ max 0 (2 * M / c) := le_max_right _ _
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have key : 2 * M < (n : ℝ) * ((n : ℝ) - 1) * c := by
    have h1 : 2 * M < ((n : ℝ) - 1) * c := by
      rw [div_lt_iff₀ hc] at hn2
      linarith
    have h2 : ((n : ℝ) - 1) * c ≤ (n : ℝ) * ((n : ℝ) - 1) * c := by
      have : 0 ≤ ((n : ℝ) - 1) * c := by positivity
      nlinarith
    linarith
  linarith

/-- 指数：|q r| ≤ C ρ^r なら重みつき和は ρ/(1−ρ)² で一様に押さえられる。 -/
theorem exp_weighted_le {q : ℕ → ℝ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hq : ∀ r, |q r| ≤ C * ρ ^ r) (R : ℕ) :
    ∑ r ∈ range R, (r : ℝ) * |q r| ≤ C * (ρ / (1 - ρ) ^ 2) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hs : HasSum (fun n : ℕ => (n : ℝ) * ρ ^ n) (ρ / (1 - ρ) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h1 : ∑ r ∈ range R, (r : ℝ) * ρ ^ r ≤ ρ / (1 - ρ) ^ 2 :=
    sum_le_hasSum (range R) (fun i _ => by positivity) hs
  calc ∑ r ∈ range R, (r : ℝ) * |q r|
      ≤ ∑ r ∈ range R, (r : ℝ) * (C * ρ ^ r) := by
        apply sum_le_sum; intro r _
        exact mul_le_mul_of_nonneg_left (hq r) (Nat.cast_nonneg r)
    _ = C * ∑ r ∈ range R, (r : ℝ) * ρ ^ r := by
        rw [mul_sum]; apply sum_congr rfl; intro r _; ring
    _ ≤ C * (ρ / (1 - ρ) ^ 2) := mul_le_mul_of_nonneg_left h1 hC

/-- 冪（s > 1）：|q n| ≤ C (n^s)⁻¹ なら部分和は R に依らず C Σ' (n^s)⁻¹ で押さえられる。 -/
theorem power_sum_uniform {q : ℕ → ℝ} {C s : ℝ} (hC : 0 ≤ C) (hs : 1 < s)
    (hq : ∀ n, |q n| ≤ C * ((n : ℝ) ^ s)⁻¹) (R : ℕ) :
    ∑ n ∈ range R, |q n| ≤ C * ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) := Real.summable_nat_rpow_inv.mpr hs
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) ^ s)⁻¹ := fun n => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  have h1 : ∑ n ∈ range R, ((n : ℝ) ^ s)⁻¹ ≤ ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ :=
    hsum.sum_le_tsum (range R) (fun i _ => hnn i)
  calc ∑ n ∈ range R, |q n| ≤ ∑ n ∈ range R, C * ((n : ℝ) ^ s)⁻¹ := sum_le_sum (fun n _ => hq n)
    _ = C * ∑ n ∈ range R, ((n : ℝ) ^ s)⁻¹ := by rw [mul_sum]
    _ ≤ C * ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ := mul_le_mul_of_nonneg_left h1 hC

/-- 冪（s ≤ 1）：部分和 Σ_{n<R} (n^s)⁻¹ は上に有界でない。 -/
theorem power_sum_unbounded {s : ℝ} (hs : s ≤ 1) (M : ℝ) :
    ∃ R : ℕ, M < ∑ n ∈ range R, ((n : ℝ) ^ s)⁻¹ := by
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) ^ s)⁻¹ := fun n => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  have hns : ¬ Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) := by
    rw [Real.summable_nat_rpow_inv]; linarith
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hns
  obtain ⟨R, hR⟩ := (Filter.tendsto_atTop.mp ht (M + 1)).exists
  exact ⟨R, by linarith⟩

/-- 冪の境（s = 1、例えば三次元の r^{−3} の尾に距離の重み r と殻 r² を掛けたもの）は有界でない。 -/
theorem power_sum_unbounded_borderline (M : ℝ) :
    ∃ R : ℕ, M < ∑ n ∈ range R, ((n : ℝ) ^ (1 : ℝ))⁻¹ :=
  power_sum_unbounded le_rfl M

end LatticeGaugeTailTypeClassification

#print axioms LatticeGaugeTailTypeClassification.flat_weighted_sum
#print axioms LatticeGaugeTailTypeClassification.flat_weighted_unbounded
#print axioms LatticeGaugeTailTypeClassification.exp_weighted_le
#print axioms LatticeGaugeTailTypeClassification.power_sum_uniform
#print axioms LatticeGaugeTailTypeClassification.power_sum_unbounded
#print axioms LatticeGaugeTailTypeClassification.power_sum_unbounded_borderline
