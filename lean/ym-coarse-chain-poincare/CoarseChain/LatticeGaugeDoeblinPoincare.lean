/-
  一次元の鎖の Poincaré 定数を、ブロックの熱浴の Kantorovich 縮小（Dobrushin–Shlosman の体積平均の判定）と
  ブロックの Poincaré 定数から出す議論の、有限次元の代数の部分。
  (1) 経路結合の一歩の期待値の評価、(2) 縮小率 κ = (L/N)(1-δ) と比較からの C_B/(1-δ)、
  (3) スペクトルの段：λ^{2n} の重みが (1-κ)^{2n} で押さえられるなら、その重みは 0。
  解析の部分（FKG・単調な結合・Lipschitz 関数の稠密性・スペクトル定理）は含まない。
-/
import Mathlib

namespace LatticeGauge.DoeblinPoincare

open Finset

/-- 経路結合の一歩：一サイトだけ差 d の二つの配置。ブロックは N 個、そのうち L 個がサイトを含み（差が消える）、
境界に持つブロックの影響の和は Jsum ≤ δ L。期待値の差は (1 - (L/N)(1-δ)) d 以下。 -/
theorem path_coupling_step (N L δ d Jsum : ℝ) (hN : 0 < N) (hd : 0 ≤ d) (hJ : Jsum ≤ δ * L) :
    (1 - L / N) * d + Jsum * d / N ≤ (1 - (L / N) * (1 - δ)) * d := by
  have h1 : Jsum * d / N ≤ δ * L * d / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    exact mul_le_mul_of_nonneg_right hJ hd
  have h2 : (1 - (L / N) * (1 - δ)) * d = (1 - L / N) * d + δ * L * d / N := by
    field_simp
    ring
  rw [h2]
  linarith

/-- 比較の段：Var ≤ (1/κ)·(1/N)Σ_B v_B、v_B ≤ C e_B、Σ_B e_B = L·E、κ = (L/N)(1-δ) なら Var ≤ C/(1-δ)·E。
N は消える（鎖の長さに一様）。 -/
theorem poincare_of_block_contraction {ι : Type*} (s : Finset ι) (v e : ι → ℝ)
    (N L C δ Var E : ℝ) (hN : 0 < N) (hL : 0 < L) (hδ : δ < 1) (hC : 0 ≤ C)
    (hgap : (L / N) * (1 - δ) * Var ≤ (1 / N) * ∑ B ∈ s, v B)
    (hv : ∀ B ∈ s, v B ≤ C * e B) (he : ∑ B ∈ s, e B = L * E) :
    Var ≤ C / (1 - δ) * E := by
  have hsum : ∑ B ∈ s, v B ≤ C * (L * E) := by
    rw [← he, Finset.mul_sum]
    exact Finset.sum_le_sum hv
  have h1 : 0 < 1 - δ := by linarith
  have key : (L / N) * (1 - δ) * Var ≤ (1 / N) * (C * (L * E)) := by
    calc (L / N) * (1 - δ) * Var ≤ (1 / N) * ∑ B ∈ s, v B := hgap
      _ ≤ (1 / N) * (C * (L * E)) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
  have key2 : L * ((1 - δ) * Var) ≤ L * (C * E) := by
    have h3 : (L / N) * (1 - δ) * Var = (L * ((1 - δ) * Var)) / N := by ring
    have h4 : (1 / N) * (C * (L * E)) = (L * (C * E)) / N := by ring
    rw [h3, h4] at key
    exact (div_le_div_iff_of_pos_right hN).mp key
  have key3 : (1 - δ) * Var ≤ C * E := le_of_mul_le_mul_left key2 hL
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  linarith

/-- スペクトルの段の核：0 ≤ r < λ、σ ≥ 0 で、全ての n について σ λ^{2n} ≤ c r^{2n} なら σ = 0。
（固有値 λ > 1-κ の成分の重み σ は、縮小 (1-κ)^n と両立しない。） -/
theorem spectral_weight_zero (σ c r lam : ℝ) (hσ : 0 ≤ σ) (hr : 0 ≤ r) (hrl : r < lam)
    (h : ∀ n : ℕ, σ * lam ^ (2 * n) ≤ c * r ^ (2 * n)) : σ = 0 := by
  by_contra hne
  have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hne)
  have hlam : 0 < lam := lt_of_le_of_lt hr hrl
  rcases eq_or_lt_of_le hr with h0 | hrp
  · -- r = 0：n = 1 で σ λ² ≤ 0
    have := h 1
    rw [← h0] at this
    simp at this
    have : 0 < σ * lam ^ 2 := by positivity
    linarith
  · have hq : 1 < (lam / r) ^ 2 := by
      have : 1 < lam / r := (one_lt_div hrp).mpr hrl
      nlinarith
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c / σ) hq
    have hn' : c < σ * ((lam / r) ^ 2) ^ n := by
      rw [div_lt_iff₀ hσp] at hn
      linarith
    have hrpow : 0 < r ^ (2 * n) := by positivity
    have heq : σ * ((lam / r) ^ 2) ^ n * r ^ (2 * n) = σ * lam ^ (2 * n) := by
      rw [← pow_mul, div_pow]
      field_simp
    have := h n
    have : σ * ((lam / r) ^ 2) ^ n * r ^ (2 * n) ≤ c * r ^ (2 * n) := by rw [heq]; exact this
    have := le_of_mul_le_mul_right this hrpow
    linarith

/-- 定理 B の代数の合成：縮小率 κ = (L/N)(1-δ) > 0（δ < 1）。 -/
theorem contraction_rate_pos (N L δ : ℝ) (hN : 0 < N) (hL : 0 < L) (hδ : δ < 1) :
    0 < (L / N) * (1 - δ) := by
  have : 0 < 1 - δ := by linarith
  positivity

end LatticeGauge.DoeblinPoincare

#print axioms LatticeGauge.DoeblinPoincare.path_coupling_step
#print axioms LatticeGauge.DoeblinPoincare.poincare_of_block_contraction
#print axioms LatticeGauge.DoeblinPoincare.spectral_weight_zero
#print axioms LatticeGauge.DoeblinPoincare.contraction_rate_pos
