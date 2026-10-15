/-
  一次元の共分散 Cov(X, φ(X)) の核の表示と、その評価の有限版。
  (1) 離散の Hoeffding の核の恒等式：Σ_{i<k} p_i p_k (x_k−x_i)(φ_k−φ_i) = Σ_j (φ_{j+1}−φ_j)·H_j、
      H_j = Σ_{i≤j<k} p_i p_k (x_k−x_i)。
  (2) 核の大きさ：x の差が L 以下なら H_j ≤ L·(Σ_{i≤j} p_i)(Σ_{k>j} p_k)。
  (3) 核の二分割の評価、(4) 重みつきの二重和の Cauchy–Schwarz、(5) Chebyshev の順序の二重和の形、
  (6) 大きい ħ の範囲の数値の一行。
  解析の部分（連続の核の表示・微分の式・比較の補題の積分・FKG）は含まない。
-/
import Mathlib

namespace LatticeGauge.CenterCovariance

open Finset

/-- 望遠鏡の和：i ≤ k ≤ n なら Σ_{j<n, i≤j<k} (φ(j+1) − φ j) = φ k − φ i。 -/
theorem telescope_ite (n i k : ℕ) (φ : ℕ → ℝ) (hk : k ≤ n) (hik : i ≤ k) :
    ∑ j ∈ range n, (if i ≤ j ∧ j < k then φ (j + 1) - φ j else 0) = φ k - φ i := by
  induction k, hik using Nat.le_induction with
  | base =>
    simp only [sub_self]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    omega
  | succ m him ih =>
    have hm : m ≤ n := by omega
    have hsplit : ∀ j ∈ range n,
        (if i ≤ j ∧ j < m + 1 then φ (j + 1) - φ j else 0) =
        (if i ≤ j ∧ j < m then φ (j + 1) - φ j else 0) +
        (if j = m then φ (j + 1) - φ j else 0) := by
      intro j _
      by_cases h1 : i ≤ j ∧ j < m
      · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; ring
      · by_cases h2 : j = m
        · rw [if_pos (by omega), if_neg h1, if_pos h2]; ring
        · rw [if_neg (by omega), if_neg h1, if_neg h2]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ih hm, Finset.sum_ite_eq']
    have hmem : m ∈ range n := Finset.mem_range.mpr (by omega)
    rw [if_pos hmem]
    ring

/-- 離散の Hoeffding の核の恒等式。 -/
theorem hoeffding_kernel (n : ℕ) (p x φ : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ k ∈ range n,
        (if i < k then p i * p k * (x k - x i) * (φ k - φ i) else 0) =
      ∑ j ∈ range n, (φ (j + 1) - φ j) *
        ∑ i ∈ range n, ∑ k ∈ range n,
          (if i ≤ j ∧ j < k then p i * p k * (x k - x i) else 0) := by
  have hpt : ∀ i ∈ range n, ∀ k ∈ range n,
      (if i < k then p i * p k * (x k - x i) * (φ k - φ i) else 0) =
      ∑ j ∈ range n,
        (if i ≤ j ∧ j < k then p i * p k * (x k - x i) * (φ (j + 1) - φ j) else 0) := by
    intro i _ k hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    by_cases hik : i < k
    · rw [if_pos hik, ← telescope_ite n i k φ hkn (le_of_lt hik), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    · rw [if_neg hik]
      symm
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      omega
  calc
    ∑ i ∈ range n, ∑ k ∈ range n,
        (if i < k then p i * p k * (x k - x i) * (φ k - φ i) else 0)
        = ∑ i ∈ range n, ∑ k ∈ range n, ∑ j ∈ range n,
          (if i ≤ j ∧ j < k then p i * p k * (x k - x i) * (φ (j + 1) - φ j) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          exact hpt i hi k hk
    _ = ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n,
          (if i ≤ j ∧ j < k then p i * p k * (x k - x i) * (φ (j + 1) - φ j) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ j ∈ range n, ∑ i ∈ range n, ∑ k ∈ range n,
          (if i ≤ j ∧ j < k then p i * p k * (x k - x i) * (φ (j + 1) - φ j) else 0) :=
          Finset.sum_comm
    _ = ∑ j ∈ range n, (φ (j + 1) - φ j) *
          ∑ i ∈ range n, ∑ k ∈ range n,
            (if i ≤ j ∧ j < k then p i * p k * (x k - x i) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          split_ifs <;> ring

/-- 核の大きさ：x_k − x_i ≤ L（i ≤ k）なら H_j ≤ L·(Σ_{i≤j} p_i)(Σ_{k>j} p_k)。 -/
theorem kernel_le_mass (n j : ℕ) (p x : ℕ → ℝ) (L : ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx : ∀ i k, i ≤ k → x k - x i ≤ L) :
    ∑ i ∈ range n, ∑ k ∈ range n,
        (if i ≤ j ∧ j < k then p i * p k * (x k - x i) else 0) ≤
      L * ((∑ i ∈ range n, if i ≤ j then p i else 0) *
        (∑ k ∈ range n, if j < k then p k else 0)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases h : i ≤ j ∧ j < k
  · rw [if_pos h, if_pos h.1, if_pos h.2]
    have hpp : 0 ≤ p i * p k := mul_nonneg (hp i) (hp k)
    have := mul_le_mul_of_nonneg_left (hx i k (by omega)) hpp
    linarith
  · rw [if_neg h]
    by_cases h1 : i ≤ j
    · have h2 : ¬ j < k := fun h2 => h ⟨h1, h2⟩
      rw [if_pos h1, if_neg h2]; simp
    · rw [if_neg h1]; simp

/-- 核の二分割：j < J では d_j ≤ c₁Δx_j、J ≤ j では d_j ≤ c₂Δx_j、H ≥ 0 なら
  Σ d_j H_j ≤ c₁ Σ_{j<J} Δx_j H_j + c₂ Σ_{j≥J} Δx_j H_j。 -/
theorem kernel_split (n J : ℕ) (d dx H : ℕ → ℝ) (c₁ c₂ : ℝ) (hH : ∀ j, 0 ≤ H j)
    (h₁ : ∀ j, j < J → d j ≤ c₁ * dx j) (h₂ : ∀ j, J ≤ j → d j ≤ c₂ * dx j) :
    ∑ j ∈ range n, d j * H j ≤
      c₁ * (∑ j ∈ range n, if j < J then dx j * H j else 0) +
      c₂ * (∑ j ∈ range n, if J ≤ j then dx j * H j else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < J
  · have hj' : ¬ J ≤ j := by omega
    rw [if_pos hj, if_neg hj']
    have := mul_le_mul_of_nonneg_right (h₁ j hj) (hH j)
    linarith
  · have hj' : J ≤ j := by omega
    rw [if_neg hj, if_pos hj']
    have := mul_le_mul_of_nonneg_right (h₂ j hj') (hH j)
    linarith

/-- 傾きの一様な上界：d_j ≤ c Δx_j・H ≥ 0 なら Σ d_j H_j ≤ c Σ Δx_j H_j（B2 の形）。 -/
theorem kernel_le_sup (n : ℕ) (d dx H : ℕ → ℝ) (c : ℝ) (hH : ∀ j, 0 ≤ H j)
    (hd : ∀ j, d j ≤ c * dx j) :
    ∑ j ∈ range n, d j * H j ≤ c * ∑ j ∈ range n, dx j * H j := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have := mul_le_mul_of_nonneg_right (hd j) (hH j)
  linarith

/-- 重みつきの二重和の Cauchy–Schwarz。 -/
theorem weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w : ι → ℝ) (u v : ι → ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, ∑ k ∈ s, w i * w k * (u i k * v i k)) ^ 2 ≤
      (∑ i ∈ s, ∑ k ∈ s, w i * w k * u i k ^ 2) *
        (∑ i ∈ s, ∑ k ∈ s, w i * w k * v i k ^ 2) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq (s ×ˢ s)
    (fun q => Real.sqrt (w q.1 * w q.2) * u q.1 q.2)
    (fun q => Real.sqrt (w q.1 * w q.2) * v q.1 q.2)
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product] at key
  have e1 : ∑ i ∈ s, ∑ k ∈ s,
      Real.sqrt (w i * w k) * u i k * (Real.sqrt (w i * w k) * v i k) =
      ∑ i ∈ s, ∑ k ∈ s, w i * w k * (u i k * v i k) := by
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro k hk
    have h := Real.mul_self_sqrt (mul_nonneg (hw i hi) (hw k hk))
    calc Real.sqrt (w i * w k) * u i k * (Real.sqrt (w i * w k) * v i k)
        = (Real.sqrt (w i * w k) * Real.sqrt (w i * w k)) * (u i k * v i k) := by ring
      _ = w i * w k * (u i k * v i k) := by rw [h]
  have e2 : ∀ g : ι → ι → ℝ, ∑ i ∈ s, ∑ k ∈ s, (Real.sqrt (w i * w k) * g i k) ^ 2 =
      ∑ i ∈ s, ∑ k ∈ s, w i * w k * g i k ^ 2 := by
    intro g
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro k hk
    have h := Real.mul_self_sqrt (mul_nonneg (hw i hi) (hw k hk))
    calc (Real.sqrt (w i * w k) * g i k) ^ 2
        = (Real.sqrt (w i * w k) * Real.sqrt (w i * w k)) * g i k ^ 2 := by ring
      _ = w i * w k * g i k ^ 2 := by rw [h]
  simp only at key
  rw [e1, e2 u, e2 v] at key
  exact key

/-- Chebyshev の順序の二重和の形：f と u が逆向き（(f_i−f_k)(u_i−u_k) ≤ 0）なら二重和は ≤ 0、
  かつ二重和は 2[(Σν)(Σνfu) − (Σνf)(Σνu)] に等しい。 -/
theorem chebyshev_double {ι : Type*} (s : Finset ι) (ν f u : ι → ℝ)
    (hν : ∀ i ∈ s, 0 ≤ ν i) (hanti : ∀ i ∈ s, ∀ k ∈ s, (f i - f k) * (u i - u k) ≤ 0) :
    ∑ i ∈ s, ∑ k ∈ s, ν i * ν k * ((f i - f k) * (u i - u k)) ≤ 0 ∧
    ∑ i ∈ s, ∑ k ∈ s, ν i * ν k * ((f i - f k) * (u i - u k)) =
      2 * ((∑ i ∈ s, ν i) * (∑ i ∈ s, ν i * f i * u i) -
        (∑ i ∈ s, ν i * f i) * (∑ i ∈ s, ν i * u i)) := by
  constructor
  · apply Finset.sum_nonpos; intro i hi
    apply Finset.sum_nonpos; intro k hk
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hν i hi) (hν k hk)) (hanti i hi k hk)
  · have hpt : ∀ i k, ν i * ν k * ((f i - f k) * (u i - u k)) =
        (ν i * f i * u i) * ν k + ν i * (ν k * f k * u k) -
        (ν i * f i) * (ν k * u k) - (ν i * u i) * (ν k * f k) := by
      intro i k; ring
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
    ring

/-- 大きい ħ の範囲の数値の一行：ħ ≥ 0.27・V ≤ 0.0884・φ′ ≤ V/(εħ)・ρ ≤ φ′·V/(εħ)（ε = 1/2）なら
  2ρ < 0.86。 -/
theorem large_hbar_column (V h phi rho : ℝ) (hh : 27 / 100 ≤ h) (hV0 : 0 ≤ V)
    (hV : V ≤ 221 / 2500) (hphi : phi ≤ V / ((1 / 2) * h))
    (hrho : rho ≤ phi * (V / ((1 / 2) * h))) : 2 * rho < 86 / 100 := by
  have hpos : 0 < (1 / 2) * h := by linarith
  have hq : V / ((1 / 2) * h) ≤ 442 / 675 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have hq0 : 0 ≤ V / ((1 / 2) * h) := div_nonneg hV0 hpos.le
  have h1 : phi * (V / ((1 / 2) * h)) ≤ (442 / 675) * (442 / 675) :=
    mul_le_mul (le_trans hphi hq) hq hq0 (by norm_num)
  nlinarith

#print axioms telescope_ite
#print axioms hoeffding_kernel
#print axioms kernel_le_mass
#print axioms kernel_split
#print axioms kernel_le_sup
#print axioms weighted_cauchy_schwarz
#print axioms chebyshev_double
#print axioms large_hbar_column

end LatticeGauge.CenterCovariance
