import Mathlib

/-!
# `(ND)` の非退化性——導分 `D` による還元と、節での数え上げの算術

`p ≥ 5` 良通常・異常・分裂の楕円曲線で `T` を `p` 等分点とする。これまでに
`(ND) ⟺ S₁(x(T̄)) ≢ 0 (mod p)`（`S₁ = (φ_p − 4u(ψ_p′/p)²)/ψ_p`）まで落ちていた。
今回は `S₁ = 2·Dψ_p`（草稿 §3.12 の命題 15。`D = −6a₆∂_{a₄} + (4/3)a₄²∂_{a₆}` は
Serre 微分の `−1` 倍——符号の規約は草稿に合わせる）という恒等式によって
`(ND) ⟺ Res_X(∂Ψ,Ψ) ≠ 0` になり、Tate 曲線（節）で `ord` を数え切ることで閉じた。
本ファイルはその議論の**算術の段**を記帳する。幾何（除法多項式・Verschiebung・
Tate 曲線・モジュラー形式）は Mathlib に無いので仮定として入り、
**主定理は Lean の定理ではない**。

* `serre_deriv_disc_zero` : 分母を払った `D`（＝Serre 微分の `−1` 倍。`a₄ ↦ −18a₆`, `a₆ ↦ 4a₄²`）は
  `Δ₀ = 4a₄³+27a₆²` を殺す。これが「`Res/Δ₀^m` が定数」と両立する理由。
* `min_sum_closed`, `gauss_sum_closed`, `cusp_ord_total` : 節での
  `Σ_{i≤n} ord(Dξ_i) + Σ_{i≠j} ord(ξ_i−ξ_j) = Σ i + 2Σ_{i<j} min(i,j)` が
  ちょうど `p(p²−1)/24`（`p = 2n+1`）になること。
* `resultant_weight_dPsi` : `Res_X(∂Ψ,Ψ)` の重みが `12·p(p²−1)/24`。
* `m_S_eq` : `m_S = p·(p(p²−1)/24)`（`Res_x = Res_X^p` の指数の勘定）。
* `weight_two_p_vanishes` : 重み `2p` は標数 `p` で消える（`Dξ = θξ` の理由）。
* `pow_card_self`, `cS_ne_zero` : `c_S = (2^nγ)^p = 2^nγ ≠ 0`。
* `deriv_one`, `deriv_pow_succ`, `deriv_eval_chain` : 導分の連鎖律。
  `f(ξ) = 0` なら `Σ d(c_k)ξ^k = −f′(ξ)·dξ`。これが
  `∂Ψ(ξ_i) = −A·(Dξ_i)·∏_{j≠i}(ξ_i−ξ_j)` の中身である。
-/

namespace PadicHeight

/-! ## §1 導分 `D`（Serre 微分の `−1` 倍）は判別式を殺す -/

theorem serre_deriv_disc_zero {R : Type*} [CommRing R] (a4 a6 : R) :
    (12 * a4 ^ 2) * (-18 * a6) + (54 * a6) * (4 * a4 ^ 2) = 0 := by
  ring

/-! ## §2 節での ord の数え上げ -/

theorem gauss_sum_closed (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), (i : ℤ) = (n : ℤ) * ((n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith [ih]

theorem min_sum_closed (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), (i : ℤ) * ((n : ℤ) - i)
      = (n : ℤ) * ((n : ℤ) ^ 2 - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : ∑ i ∈ Finset.range (m + 1), (i : ℤ) * (((m : ℤ) + 1) - i)
        = (∑ i ∈ Finset.range (m + 1), (i : ℤ) * ((m : ℤ) - i))
          + ∑ i ∈ Finset.range (m + 1), (i : ℤ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hg := gauss_sum_closed m
    rw [Finset.sum_range_succ]
    push_cast
    rw [hsplit]
    linear_combination ih + 3 * hg

theorem cusp_ord_total (n : ℤ) :
    12 * (n * (n + 1)) + 8 * (n * (n ^ 2 - 1)) = (2 * n + 1) * ((2 * n + 1) ^ 2 - 1) := by
  ring

/-! ## §3 重み勘定 -/

theorem resultant_weight_dPsi (n : ℤ) :
    2 * (n * ((2 * n + 1) ^ 2 + 1) + n * ((2 * n + 1) ^ 2 - 1) - 2 * (2 * n + 1) * n ^ 2)
      = (2 * n + 1) * ((2 * n + 1) ^ 2 - 1) := by
  ring

theorem m_S_eq (p M : ℕ) (h : 24 * M = p * (p ^ 2 - 1)) :
    24 * (p * M) = p ^ 2 * (p ^ 2 - 1) := by
  calc 24 * (p * M) = p * (24 * M) := by ring
    _ = p * (p * (p ^ 2 - 1)) := by rw [h]
    _ = p ^ 2 * (p ^ 2 - 1) := by ring

/-! ## §4 重み `2p` は標数 `p` で消える -/

theorem weight_two_p_vanishes (p : ℕ) : ((2 * p : ℕ) : ZMod p) = 0 := by
  push_cast
  simp

/-! ## §5 `c_S ≠ 0` -/

theorem pow_card_self (p : ℕ) [Fact p.Prime] (x : ZMod p) : x ^ p = x := ZMod.pow_card x

theorem cS_ne_zero (p : ℕ) [Fact p.Prime] (hp : (2 : ZMod p) ≠ 0) (n : ℕ) (γ : ZMod p)
    (hγ : γ ≠ 0) : ((2 : ZMod p) ^ n * γ) ^ p = (2 : ZMod p) ^ n * γ
      ∧ ((2 : ZMod p) ^ n * γ) ^ p ≠ 0 := by
  refine ⟨ZMod.pow_card _, ?_⟩
  rw [ZMod.pow_card]
  exact mul_ne_zero (pow_ne_zero _ hp) hγ

/-! ## §6 導分の連鎖律——`∂Ψ(ξ) = −Ψ′(ξ)·Dξ` -/

section Derivation
variable {R : Type*} [CommRing R] (d : R → R)
variable (hadd : ∀ a b, d (a + b) = d a + d b)
variable (hmul : ∀ a b, d (a * b) = d a * b + a * d b)

include hadd in
theorem deriv_zero : d 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  have h2 : d 0 + 0 = d 0 + d 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

include hmul in
theorem deriv_one : d 1 = 0 := by
  have h := hmul 1 1
  simp only [mul_one, one_mul] at h
  have h2 : d 1 + 0 = d 1 + d 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

include hadd in
theorem deriv_sum (s : Finset ℕ) (g : ℕ → R) :
    d (∑ i ∈ s, g i) = ∑ i ∈ s, d (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using deriv_zero d hadd
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

include hmul in
theorem deriv_pow_succ (ξ : R) (k : ℕ) :
    d (ξ ^ (k + 1)) = ((k + 1 : ℕ) : R) * ξ ^ k * d ξ := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hp : ξ ^ (m + 1 + 1) = ξ * ξ ^ (m + 1) := by ring
    rw [hp, hmul, ih]
    push_cast
    ring

include hadd hmul in
/-- `f = Σ_{k≤N} c_k X^k` と `f(ξ) = 0` なら
`Σ_k d(c_k) ξ^k = −f′(ξ)·d ξ`（`f′(ξ) = Σ_{k<N}(k+1)c_{k+1}ξ^k`）。 -/
theorem deriv_eval_chain (N : ℕ) (c : ℕ → R) (ξ : R)
    (h0 : ∑ k ∈ Finset.range (N + 1), c k * ξ ^ k = 0) :
    (∑ k ∈ Finset.range (N + 1), d (c k) * ξ ^ k)
      = -(∑ k ∈ Finset.range N, ((k + 1 : ℕ) : R) * c (k + 1) * ξ ^ k) * d ξ := by
  have hd := congrArg d h0
  rw [deriv_sum d hadd, deriv_zero d hadd] at hd
  have hterm : ∀ k ∈ Finset.range (N + 1),
      d (c k * ξ ^ k)
        = d (c k) * ξ ^ k + (if k = 0 then 0 else ((k : ℕ) : R) * c k * ξ ^ (k - 1) * d ξ) := by
    intro k _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hmul, deriv_pow_succ d hmul]
      simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero j)]
      push_cast
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at hd
  have hshift : ∑ k ∈ Finset.range (N + 1),
      (if k = 0 then (0 : R) else ((k : ℕ) : R) * c k * ξ ^ (k - 1) * d ξ)
      = ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : R) * c (k + 1) * ξ ^ k * d ξ) := by
    rw [Finset.sum_range_succ' _ N]
    simp
  rw [hshift] at hd
  have hmul' : ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : R) * c (k + 1) * ξ ^ k * d ξ)
      = (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : R) * c (k + 1) * ξ ^ k) * d ξ :=
    (Finset.sum_mul _ _ _).symm
  rw [hmul'] at hd
  linear_combination hd

end Derivation

end PadicHeight

#print axioms PadicHeight.serre_deriv_disc_zero
#print axioms PadicHeight.gauss_sum_closed
#print axioms PadicHeight.min_sum_closed
#print axioms PadicHeight.cusp_ord_total
#print axioms PadicHeight.resultant_weight_dPsi
#print axioms PadicHeight.m_S_eq
#print axioms PadicHeight.weight_two_p_vanishes
#print axioms PadicHeight.pow_card_self
#print axioms PadicHeight.cS_ne_zero
#print axioms PadicHeight.deriv_zero
#print axioms PadicHeight.deriv_one
#print axioms PadicHeight.deriv_sum
#print axioms PadicHeight.deriv_pow_succ
#print axioms PadicHeight.deriv_eval_chain
