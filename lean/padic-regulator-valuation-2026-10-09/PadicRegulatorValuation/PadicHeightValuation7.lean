import Mathlib

/-!
# 尖点での留数の算術 —— `Res_X(ũ,g)` の `Δ` に沿う位数が「ちょうど」であることの算術部分

乗法的退化（Tate 曲線）の上で、`ker V ∖ {O}` の点 `β_j`（`j = 1,…,n`、`p = 2n+1`）における
`12ρ_j = (d/dt)log f(β_j) − f′(β_j)(dβ_j/dt)/f(β_j)` の二項は**どちらも一位の極**を持ち、
留数はそれぞれ `j(p−j) ≡ −j²` と `−2j²` である。差は `j² ≠ 0` だから極は消えない。
このファイルはその「打ち消しが起こらない」ことの算術と、`Σ_j (j(p−j) − 1) = m_p` の和、
および「二つの寄り添う根が合わせてちょうど一つ分」という恒等式
`(1−u)⁻¹ + (1−u⁻¹)⁻¹ = 1` を形式化する。

幾何（Tate 一意化・Vélu・除法多項式）は Lean に載せていない。
-/

namespace PadicHeight

open Finset

/-! ## 1. 二つの寄り添う根の寄与が合わせてちょうど 1 になること -/

/-- `β_j` から同じ距離にある二つの根 `α_j`, `α_{p−j}` の寄与の和。
`u ≠ 0, 1` なる体の元について `(1−u)⁻¹ + (1−u⁻¹)⁻¹ = 1`。 -/
theorem inv_one_sub_add_inv_one_sub_inv {K : Type*} [Field K] {u : K}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) : (1 - u)⁻¹ + (1 - u⁻¹)⁻¹ = 1 := by
  have h1 : (1 : K) - u ≠ 0 := sub_ne_zero.mpr fun h => hu1 h.symm
  have h2 : (1 : K) - u⁻¹ = (u - 1) / u := by field_simp
  have h3 : (1 : K) - u⁻¹ ≠ 0 := by
    rw [h2]; exact div_ne_zero (sub_ne_zero.mpr hu1) hu0
  rw [h2, inv_div]
  field_simp
  ring

/-- `12u = −(1−u)²` を満たす元は `1` ではない（`12 ≠ 0` の体で）。
`f` の付値 `0` の根 `α_0` が節点に落ちないこと（`ū_R ≠ 1`）の算術版。 -/
theorem nodal_root_ne_one {K : Type*} [Field K] {u : K} (h12 : (12 : K) ≠ 0)
    (hu : 12 * u = -(1 - u) ^ 2) : u ≠ 1 := by
  intro h
  apply h12
  rw [h] at hu
  simpa using hu

/-- `p ≥ 5` の素数では `12` は `ZMod p` で可逆。 -/
theorem twelve_ne_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : (12 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((12 : ℕ) : ZMod p) = 0 := by push_cast; exact h
  have hd : p ∣ 12 := (CharP.cast_eq_zero_iff (ZMod p) p 12).mp h'
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> revert hp hd <;> decide

/-! ## 2. 留数の非打ち消し -/

/-- 第一項の留数：`j(p−j) ≡ −j² (mod p)`。 -/
theorem first_term_residue (p j : ℕ) (hj : j ≤ p) :
    ((j * (p - j) : ℕ) : ZMod p) = -((j : ZMod p) ^ 2) := by
  have h : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
    rw [Nat.cast_sub hj, ZMod.natCast_self, zero_sub]
  rw [Nat.cast_mul, h]
  ring

/-- `1 ≤ j ≤ n`、`p = 2n+1` が素数なら `j` は `ZMod p` で可逆。 -/
theorem cast_ne_zero_of_le {p : ℕ} (_hp : p.Prime) {n j : ℕ} (hpn : p = 2 * n + 1)
    (hj : 1 ≤ j) (hjn : j ≤ n) : (j : ZMod p) ≠ 0 := by
  have hlt : j < p := by omega
  intro h
  have hd : p ∣ j := (CharP.cast_eq_zero_iff (ZMod p) p j).mp h
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- 第二項の先頭係数は `p − 2j ≡ −2j`：`j ≤ k ≤ p−j` の `p−2j+1` 個の根のうち、
両端の二つが合わせて一つ分になるので、係数の和は `(p−2j+1) − 1 = p−2j` である。
これが `0` にならないことが「傾き `−j` の辺の上で打ち消しが起こらない」ことに当たる。 -/
theorem second_term_leading_ne_zero {p : ℕ} (hp : p.Prime) {n j : ℕ} (hpn : p = 2 * n + 1)
    (hj : 1 ≤ j) (hjn : j ≤ n) : ((p - 2 * j : ℕ) : ZMod p) ≠ 0 := by
  have h : ((p - 2 * j : ℕ) : ZMod p) = -(2 * (j : ZMod p)) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_mul]
    push_cast
    ring
  rw [h, neg_ne_zero]
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) = 0 → p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp
    intro hc
    have := this (by push_cast; exact hc)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have : Fact p.Prime := ⟨hp⟩
  exact mul_ne_zero h2 (cast_ne_zero_of_le hp hpn hj hjn)

/-- **留数は打ち消さない**：第一項の留数 `j(p−j) ≡ −j²` と第二項の留数 `−2j²` の差は `j² ≠ 0`。
`12ρ_j` が `t` に沿ってちょうど一位の極を持つことの算術的な芯である。 -/
theorem residues_do_not_cancel {p : ℕ} (hp : p.Prime) {n j : ℕ} (hpn : p = 2 * n + 1)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    ((j * (p - j) : ℕ) : ZMod p) - (-(2 * (j : ZMod p) ^ 2)) = (j : ZMod p) ^ 2
    ∧ ((j : ZMod p) ^ 2 ≠ 0) := by
  have hjp : j ≤ p := by omega
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_⟩
  · rw [first_term_residue p j hjp]; ring
  · exact pow_ne_zero 2 (cast_ne_zero_of_le hp hpn hj hjn)

/-! ## 3. 尖点の和が `m_p` になること -/

theorem two_mul_sum_Icc_id (n : ℕ) : 2 * (∑ j ∈ Icc 1 n, (j : ℤ)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith

theorem six_mul_sum_Icc_sq (n : ℕ) :
    6 * (∑ j ∈ Icc 1 n, (j : ℤ) ^ 2) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    nlinarith [ih]

/-- `Σ_{j=1}^n (j(2n+1−j) − 1)` を二つの基本和で書き直す。 -/
theorem sum_cusp_split (n : ℕ) :
    (∑ j ∈ Icc 1 n, ((j : ℤ) * (2 * (n : ℤ) + 1 - j) - 1))
      = (2 * (n : ℤ) + 1) * (∑ j ∈ Icc 1 n, (j : ℤ)) - (∑ j ∈ Icc 1 n, (j : ℤ) ^ 2) - n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    have hk : (∑ j ∈ Icc 1 k, ((j : ℤ) * (2 * ((k : ℤ) + 1) + 1 - j) - 1))
        = (∑ j ∈ Icc 1 k, ((j : ℤ) * (2 * (k : ℤ) + 1 - j) - 1)) + 2 * (∑ j ∈ Icc 1 k, (j : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    push_cast
    rw [hk, ih]
    ring

/-- **尖点の位数の和**：`Σ_{j=1}^n (j(p−j) − 1) = m_p`（`p = 2n+1`、`12 m_p = (p−1)(p−2)(p+3)`）。 -/
theorem twelve_mul_sum_cusp_orders (n : ℕ) :
    12 * (∑ j ∈ Icc 1 n, ((j : ℤ) * (2 * (n : ℤ) + 1 - j) - 1))
      = (2 * (n : ℤ)) * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) + 4) := by
  rw [sum_cusp_split n]
  have h1 := two_mul_sum_Icc_id n
  have h2 := six_mul_sum_Icc_sq n
  linear_combination (6 * (2 * (n : ℤ) + 1)) * h1 - 2 * h2

/-! ## 4. 下界が和で等号になれば各項で等号になること -/

/-- 各項で `b i ≤ a i` が分かっていて、和が `Σ a ≤ Σ b` なら、各項で等号。
`v(ũ(β_j)) ≥ j(p−j) − 1`（Newton 多角形）と `Σ_j v(ũ(β_j)) = m_p` から
各 `j` で等号が従うこと（数値検証の論拠）。 -/
theorem eq_of_le_of_sum_le {ι : Type*} {s : Finset ι} {a b : ι → ℤ}
    (hab : ∀ i ∈ s, b i ≤ a i) (h : ∑ i ∈ s, a i ≤ ∑ i ∈ s, b i) :
    ∀ i ∈ s, a i = b i := by
  have hs : ∑ i ∈ s, b i = ∑ i ∈ s, a i := le_antisymm (Finset.sum_le_sum hab) h
  intro i hi
  exact ((Finset.sum_eq_sum_iff_of_le hab).mp hs i hi).symm

/-- `j ≤ k ≤ p−j` の格子点の個数は `p−2j+1`（うち一つ分が両端の二つの合流で消える）。 -/
theorem card_Icc_cusp (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    (Icc j (2 * n + 1 - j)).card = 2 * n + 2 - 2 * j := by
  rw [Nat.card_Icc]
  omega

end PadicHeight

#print axioms PadicHeight.inv_one_sub_add_inv_one_sub_inv
#print axioms PadicHeight.nodal_root_ne_one
#print axioms PadicHeight.twelve_ne_zero
#print axioms PadicHeight.first_term_residue
#print axioms PadicHeight.cast_ne_zero_of_le
#print axioms PadicHeight.second_term_leading_ne_zero
#print axioms PadicHeight.residues_do_not_cancel
#print axioms PadicHeight.two_mul_sum_Icc_id
#print axioms PadicHeight.six_mul_sum_Icc_sq
#print axioms PadicHeight.sum_cusp_split
#print axioms PadicHeight.twelve_mul_sum_cusp_orders
#print axioms PadicHeight.eq_of_le_of_sum_le
#print axioms PadicHeight.card_Icc_cusp
