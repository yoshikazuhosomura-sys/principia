import Mathlib

/-!
# Tate 族での留数の勘定・平衡剰余系・`Res` の指数の閉形

それまでは `(R′)`（核多項式の根を導分 `D` で動かす式。`D` は Serre 微分の `−1` 倍）一本を残していた。ここではそれを Tate 族で閉じた。
証明に出てくる算術のうち Mathlib に載る部分を集める。幾何（Tate 曲線の一意化・theta の積表示・
除法多項式・Verschiebung・重みごとの q 展開の単射性）は Mathlib に無いので仮定として入り、
**主定理（草稿の命題 15・定理 S。以前に「定理 P」と呼んでいたもの）は Lean の定理ではない**。

* `D_eval_zero`・`D2_eval_zero`・`log_deriv_ratio` : 乗法的微分 `D = (1+s)d/ds` に対する
  `DH/H = 1/s + κ + …` と `D²H/DH|₀ = 2κ−1` の関係（§2.5 の局所展開）。
* `telescope_term`・`telescope_sum` : `Σ_{k<i}(q^k−1)/(1−q^k) = −i` の望遠鏡（§2.5 の `S = 1−i`）。
* `residue_value`・`residue_value_zmod` : `2(n+1−i)−1 = 2n+1−2i` と、標数 `p = 2n+1` で `≡ −2i`。
* `sign_flip_invariance` : `i ↦ p−i`（`η ↦ −η`）で両辺の符号が揃うこと。
* `balanced_repr` : `p = 2n+1` のとき `a ≥ −n` はすべて `a = pm+j`（`m ≥ 0`・`|j| ≤ n`）と書ける
  ——§2.3 の指数集合の並べ替えの核。
* `ordq_total`・`weight_ResK` : `n·n(n+1) + p·n(n²−1)/3 = m_K` と重みが `12m_K` になること。
* `mK_even`・`exponent_two_nsq`・`exponent_case_1mod4`・`exponent_case_3mod4`・`eps_cases` :
  `c_K = ε_p2^{m_K}` の指数を `p−1` で潰す算術と、`ε_p = −1 ⟺ p ≡ 3 (mod 8)`。
-/

namespace PadicHeight

open Polynomial

/-! ## §1 乗法的微分の局所展開（§2.5） -/

/-- 乗法的微分 `D = (1+s)·d/ds`（`s = W/W_i − 1` が局所パラメータ）。 -/
noncomputable def mulD {R : Type*} [CommRing R] (f : R[X]) : R[X] :=
  (1 + X) * derivative f

theorem D_eval_zero {R : Type*} [CommRing R] (H : R[X]) :
    (mulD H).eval 0 = H.coeff 1 := by
  have : (derivative H).eval 0 = H.coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp
  simp [mulD, this]

theorem D2_eval_zero {R : Type*} [CommRing R] (H : R[X]) :
    (mulD (mulD H)).eval 0 = H.coeff 1 + 2 * H.coeff 2 := by
  have h1 : (derivative H).eval 0 = H.coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]; simp
  have h2 : (derivative (derivative H)).eval 0 = 2 * H.coeff 2 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    ring
  simp [mulD, derivative_mul, h1, h2]

/-- `H = h₁s + h₂s² + …`・`L = DH/H = 1/s + κ + …`（すなわち `κh₁ = h₁+h₂`）のとき
`D²H/DH|₀ = 2κ−1`。§2.5 で `κ = n+1−i` を代入して `p−2i` が出る。 -/
theorem log_deriv_ratio {K : Type*} [Field K] (H : K[X]) (κ : K)
    (h1 : H.coeff 1 ≠ 0) (hκ : κ * H.coeff 1 = H.coeff 1 + H.coeff 2) :
    (mulD (mulD H)).eval 0 / (mulD H).eval 0 = 2 * κ - 1 := by
  rw [D2_eval_zero, D_eval_zero, div_eq_iff h1]
  linear_combination (-2 : K) * hκ

/-! ## §2 望遠鏡（§2.5 の `S = 1−i`） -/

theorem telescope_term {K : Type*} [Field K] (v : K) (hv : 1 - v ≠ 0) :
    (v - 1) / (1 - v) = -1 := by
  field_simp
  ring

/-- `Σ_{k=1}^{i−1}(q^k−1)/(1−q^k) = −(i−1)`。 -/
theorem telescope_sum {K : Type*} [Field K] (q : K) (i : ℕ)
    (h : ∀ k ∈ Finset.range i, 1 - q ^ (k + 1) ≠ 0) :
    (∑ k ∈ Finset.range i, (q ^ (k + 1) - 1) / (1 - q ^ (k + 1))) = -(i : K) := by
  have : ∀ k ∈ Finset.range i, (q ^ (k + 1) - 1) / (1 - q ^ (k + 1)) = -1 := by
    intro k hk
    exact telescope_term _ (h k hk)
  rw [Finset.sum_congr rfl this]
  simp

/-! ## §3 留数の値（§2.5・§2.6） -/

/-- `κ = n+1−i` を `2κ−1` に入れた形：`2(n+1−i)−1 = (2n+1)−2i`。 -/
theorem residue_value (n i : ℤ) : 2 * (n + 1 - i) - 1 = (2 * n + 1) - 2 * i := by ring

/-- 標数 `p = 2n+1` では `p−2i ≡ −2i`。 -/
theorem residue_value_zmod (n i : ℕ) :
    ((2 * n + 1 : ℕ) : ZMod (2 * n + 1)) - 2 * (i : ZMod (2 * n + 1))
      = -(2 * (i : ZMod (2 * n + 1))) := by
  simp

/-- `i ↦ p−i` で `ξ` は同じ・`η ↦ −η`・`i ↦ −i` だから `−2iη` は不変（§2.6 の整合）。 -/
theorem sign_flip_invariance {R : Type*} [CommRing R] (i η : R) :
    -2 * (-i) * (-η) = -(2 * i * η) := by ring

/-! ## §4 平衡剰余系（§2.3 の指数集合の並べ替え） -/

/-- `p = 2n+1` のとき、`a ≥ −n` はすべて `a = p·m + j`（`m ≥ 0`・`|j| ≤ n`）と一意に書ける。
`θ_Q(Wq^j)`（`|j| ≤ n`）の積の `(1−q^aW)` の因子が `a ≥ −n` を**ちょうど一度ずつ**
走ることが、`G(W) = c·W^nθ_q(W)` の理由である。 -/
theorem balanced_repr (n : ℕ) (a : ℤ) (ha : -(n : ℤ) ≤ a) :
    ∃ m : ℕ, ∃ j : ℤ, |j| ≤ (n : ℤ) ∧ a = (2 * (n : ℤ) + 1) * (m : ℤ) + j := by
  have hp : (0 : ℤ) < 2 * (n : ℤ) + 1 := by positivity
  set p : ℤ := 2 * (n : ℤ) + 1 with hpdef
  set b : ℤ := a + (n : ℤ) with hbdef
  have hb0 : 0 ≤ b := by omega
  have hq0 : 0 ≤ b / p := Int.ediv_nonneg hb0 (le_of_lt hp)
  refine ⟨(b / p).toNat, a - p * (b / p), ?_, ?_⟩
  · have h1 : 0 ≤ b % p := Int.emod_nonneg b (ne_of_gt hp)
    have h2 : b % p < p := Int.emod_lt_of_pos b hp
    have h3 : b % p = b - p * (b / p) := Int.emod_def b p
    have h4 : a - p * (b / p) = b % p - (n : ℤ) := by omega
    rw [h4, abs_le]
    constructor <;> omega
  · rw [Int.toNat_of_nonneg hq0]; ring

/-! ## §5 節の数え上げと重み（§5.2） -/

/-- `ord_q`：`n·n(n+1) + p·n(n²−1)/3 = m_K`（`24m_K = (p²−1)(p²−3)`・`p = 2n+1`）。
分母を払った形で書く。 -/
theorem ordq_total (n : ℤ) :
    8 * (3 * (n ^ 2 * (n + 1)) + (2 * n + 1) * (n * (n ^ 2 - 1)))
      = ((2 * n + 1) ^ 2 - 1) * ((2 * n + 1) ^ 2 - 3) := by ring

/-- 重み：`deg ψ_p·(w(K) − 2·deg K) + deg K·w(ψ_p) = 12m_K`。
`24m_K = (2j)(2k)`（`2j = p²−1`・`2k = p²−3`）なので、重みの和の 2 倍が `(2j)(2k)` になることを言えば
`= 12m_K` が出る。 -/
theorem weight_ResK (j k : ℤ) :
    (2 * j) * (2 * k) = 2 * (j * (2 * k - 2 * k) + k * (2 * j)) := by ring

/-! ## §6 `c_K = ε_p·2^{m_K}` の指数を `p−1` で潰す（§5.3） -/

/-- `m_K` は偶数：`p² = 24k+1`（`gcd(p,6) = 1`）なら `m_K = 2k(12k−1)`。 -/
theorem mK_even (k : ℤ) : (24 * k) * (24 * k - 2) = 24 * (2 * (k * (12 * k - 1))) := by ring

/-- `2n² = (p−1)·n`（`p = 2n+1`）だから `p−1 ∣ 2n²`——`2^{−2n²} = 1` の理由。 -/
theorem exponent_two_nsq (n : ℤ) : 2 * n ^ 2 = (2 * n + 1 - 1) * n := by ring

/-- `p = 4t+3` のとき `p−1 ∣ 3m_K`（`24m_K = (p²−1)(p²−3)`）。 -/
theorem exponent_case_3mod4 (t : ℤ) :
    ((4 * t + 3) ^ 2 - 1) * ((4 * t + 3) ^ 2 - 3)
      = 8 * ((4 * t + 2) * ((t + 1) * (8 * t ^ 2 + 12 * t + 3))) := by ring

/-- `p = 4t+1` のとき `3m_K ≡ (p−1)/2 (mod p−1)`：`3m_K − 2t = 4t·(…)`。 -/
theorem exponent_case_1mod4 (t : ℤ) :
    ((4 * t + 1) ^ 2 - 1) * ((4 * t + 1) ^ 2 - 3)
      = 8 * (2 * t + (4 * t) * (8 * t ^ 3 + 8 * t ^ 2 + t - 1)) := by ring

/-- 符号：`n(n+1)/2 = (p²−1)/8`（`p = 2n+1`）——`(−1)^{n(n+1)/2}` が第二補充法則の記号になる理由。 -/
theorem sign_exponent (n : ℤ) : 4 * (n * (n + 1)) = (2 * n + 1) ^ 2 - 1 := by ring

/-- `ε_p = χ·(p ≡ 1 mod 4 ならもう一度 χ)`（`χ = (2|p)`）を `p mod 8` で場合分けすると
`ε_p = −1 ⟺ p ≡ 3 (mod 8)`。 -/
theorem eps_cases (r : ℕ) (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) :
    (if r = 1 ∨ r = 7 then (1 : ℤ) else -1)
        * (if r % 4 = 1 then (if r = 1 ∨ r = 7 then (1 : ℤ) else -1) else 1)
      = (if r = 3 then (-1 : ℤ) else 1) := by
  rcases hr with h | h | h | h <;> subst h <;> norm_num

end PadicHeight

#print axioms PadicHeight.D_eval_zero
#print axioms PadicHeight.D2_eval_zero
#print axioms PadicHeight.log_deriv_ratio
#print axioms PadicHeight.telescope_term
#print axioms PadicHeight.telescope_sum
#print axioms PadicHeight.residue_value
#print axioms PadicHeight.residue_value_zmod
#print axioms PadicHeight.sign_flip_invariance
#print axioms PadicHeight.balanced_repr
#print axioms PadicHeight.ordq_total
#print axioms PadicHeight.weight_ResK
#print axioms PadicHeight.mK_even
#print axioms PadicHeight.exponent_two_nsq
#print axioms PadicHeight.exponent_case_3mod4
#print axioms PadicHeight.exponent_case_1mod4
#print axioms PadicHeight.sign_exponent
#print axioms PadicHeight.eps_cases
