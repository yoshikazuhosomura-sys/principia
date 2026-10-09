import Mathlib

/-!
# 分裂の異常素点：二次の Fermat 商は持ち上げについて**一次**であり、その傾きは局所量

前のファイル（`PadicHeightValuation10`）は分裂の場合に高さ行列の `mod p` が
`[[a, bᵗ],[b, 0]]` の形（階数 2 以下）になること、および定数 `a` が二次の Fermat 商
`λ⁽²⁾ = q⁽²⁾(φ_p(x₀))/2` で書けることの算術の段を載せた。そこで残ったのは

* `λ⁽²⁾` は持ち上げ `x₀ ↦ x₀ + pk` で**動く**（計算では例外なし）。その動きの式が無い、
* 非対角成分 `b` を局所化する道が無い、

の二点だった。本ファイルはその二点の**代数の核**を載せる。

## 何を載せたか

`φ_p` について紙にある事実は「`p ∣ φ_p′`」（補題 5：標数 `p` で `[p] = V∘F`）だけである。
これを `P.derivative = C p * G` という多項式の仮定に置き換えると、Taylor の三次までの
切り落とし（`eval_cube_dvd`）と `p ∣ G′` の段から

  `p³ ∣ P(r + pk) − P(r) − p²·k·G(r)`        (`eval_shift_of_deriv_eq`)

が出る。`k²` の項が `p³` に落ちるのが要点で、そこに `p` が奇であることを使う。
二項展開（`sq_dvd_pow_add_sub`）と合わせると

  `p³ ∣ v^{p−1} − u^{p−1} + p²·k·G(r)·u^{p−2}`   (`fermatQuot2_shift`)

すなわち `q⁽²⁾(v) = q⁽²⁾(u) − k·G(r)/u`、つまり **`λ⁽²⁾` は `k` について一次**で、
傾きは `s = −G(x̄)/(2·φ_p(x̄))`。`G mod p` は `F_p[a₄,a₆][x]` の元だから
傾きは `(Ē, x̄)` だけの関数——**局所量**である。

`s ≠ 0` のとき `k ↦ λ⁽²⁾` は全単射（`lambda2_lift_bijective`）で、`λ⁽²⁾ = 0` になる
持ち上げはちょうど一つ（`lambda2_unique_zero_lift`）。
最後に非対角成分の記帳 `b = s·κ/n²`（`b_eq_slope_mul_kappa`）を載せる。
これは `Λ_0` の元が `x` 座標を `mod p²` でどれだけ動かすかだけで `b` が決まることの記帳である。

幾何・`p` 進解析（`σ` 関数・除法多項式・Vélu・高さの対自身）は Lean に載っていない。
載っているのは**多項式の恒等式・合同の算術・`ZMod p` の記帳**である。
-/

namespace PadicHeight

open Polynomial

/-! ## 1. Taylor の三次までの切り落とし -/

/-- `Q` から `coeff 0, 1, 2` の部分を引くと `X^3` で割れる。 -/
theorem X_pow_three_dvd_sub_trunc (Q : Polynomial ℤ) :
    (X : Polynomial ℤ) ^ 3 ∣
      Q - (C (Q.coeff 0) + C (Q.coeff 1) * X + C (Q.coeff 2) * X ^ 2) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub]
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] <;> norm_num

/-- 評価版：`h^3 ∣ Q(h) − (Q₀ + Q₁h + Q₂h²)`。 -/
theorem eval_cube_dvd (Q : Polynomial ℤ) (h : ℤ) :
    h ^ 3 ∣ Q.eval h - (Q.coeff 0 + Q.coeff 1 * h + Q.coeff 2 * h ^ 2) := by
  obtain ⟨S, hS⟩ := X_pow_three_dvd_sub_trunc Q
  refine ⟨S.eval h, ?_⟩
  have := congrArg (Polynomial.eval h) hS
  simpa using this

/-! ## 2. `p ∣ P′` から出る二段目の合同 -/

/-- **本ファイルの心臓部。** `P′ = p·G` なら、`p` が 2 と互いに素であるかぎり

> `p³ ∣ P(r + pk) − P(r) − p²·k·G(r)`。

（適用：`P = φ_p`、`G = φ_p′/p`（補題 5 で整）、`r = x₀`。`k²` の項は `P″ = p·G′` から
`p³` に落ちる。これが `λ⁽²⁾` が `k` について一次である理由である。） -/
theorem eval_shift_of_deriv_eq {p : ℤ} (hcop : IsCoprime p 2)
    (P G : Polynomial ℤ) (hd : P.derivative = C p * G) (r k : ℤ) :
    p ^ 3 ∣ P.eval (r + p * k) - P.eval r - p ^ 2 * k * G.eval r := by
  set Q : Polynomial ℤ := P.comp (X + C r) with hQ
  -- Q の評価と最初の三つの係数
  have hev : ∀ h : ℤ, Q.eval h = P.eval (h + r) := by
    intro h; simp [hQ, eval_comp]
  have hQ0 : Q.coeff 0 = P.eval r := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev]; ring_nf
  have hdQ : Q.derivative = C p * (G.comp (X + C r)) := by
    rw [hQ, Polynomial.derivative_comp, hd]
    simp [Polynomial.mul_comp]
  have hQ1 : Q.coeff 1 = p * G.eval r := by
    have h0 : Q.derivative.coeff 0 = Q.coeff 1 := by
      simpa using (Polynomial.coeff_derivative Q 0)
    have h1 : Q.derivative.coeff 0 = p * G.eval r := by
      rw [hdQ]
      simp [Polynomial.coeff_zero_eq_eval_zero, eval_comp]
    rw [← h0, h1]
  have hQ2 : p ∣ Q.coeff 2 := by
    have h0 : Q.derivative.coeff 1 = Q.coeff 2 * 2 := by
      simpa using (Polynomial.coeff_derivative Q 1)
    have h1 : Q.derivative.coeff 1 = p * (G.comp (X + C r)).coeff 1 := by
      rw [hdQ]; simp
    have hc : Q.coeff 2 * 2 = p * (G.comp (X + C r)).coeff 1 := by rw [← h0, h1]
    obtain ⟨a, b, hab⟩ := hcop
    refine ⟨a * Q.coeff 2 + b * (G.comp (X + C r)).coeff 1, ?_⟩
    linear_combination (-(Q.coeff 2)) * hab + b * hc
  -- 三次の剰余
  obtain ⟨S, hS⟩ := eval_cube_dvd Q (p * k)
  obtain ⟨t, ht⟩ := hQ2
  refine ⟨k ^ 3 * S + t * k ^ 2, ?_⟩
  have hL : P.eval (r + p * k) = Q.eval (p * k) := by rw [hev]; ring_nf
  rw [hL]
  have hS' : Q.eval (p * k)
      = (Q.coeff 0 + Q.coeff 1 * (p * k) + Q.coeff 2 * (p * k) ^ 2) + (p * k) ^ 3 * S := by
    linear_combination hS
  rw [hS', hQ0, hQ1, ht]
  ring

/-! ## 3. 二項展開と `(p−1)` 乗 -/

/-- `t²` を法とした二項展開：`(u + t)^{n+1} ≡ u^{n+1} + (n+1)u^n t`。 -/
theorem sq_dvd_pow_add_sub (u t : ℤ) : ∀ n : ℕ,
    t ^ 2 ∣ (u + t) ^ (n + 1) - u ^ (n + 1) - (n + 1 : ℤ) * u ^ n * t
  | 0 => by simp
  | (n + 1) => by
      obtain ⟨c, hc⟩ := sq_dvd_pow_add_sub u t n
      refine ⟨c * (u + t) + ((n : ℤ) + 1) * u ^ n, ?_⟩
      have h : (u + t) ^ (n + 1) = u ^ (n + 1) + (n + 1 : ℤ) * u ^ n * t + t ^ 2 * c := by
        linear_combination hc
      calc (u + t) ^ (n + 1 + 1) - u ^ (n + 1 + 1) - (n + 1 + 1 : ℤ) * u ^ (n + 1) * t
          = ((u + t) ^ (n + 1)) * (u + t) - u ^ (n + 1 + 1) - (n + 1 + 1 : ℤ) * u ^ (n + 1) * t := by
            ring
        _ = t ^ 2 * (c * (u + t) + ((n : ℤ) + 1) * u ^ n) := by rw [h]; ring

/-- **二段目の Fermat 商の移り方。** `v ≡ u + p²m (mod p³)` かつ `p = n + 2` なら

> `p³ ∣ v^{p−1} − u^{p−1} + p²·m·u^{p−2}`,

すなわち `q⁽²⁾(v) = q⁽²⁾(u) − m·u^{−1}`（`u^{p−2} ≡ u^{−1}`）。 -/
theorem fermatQuot2_move {p : ℤ} {n : ℕ} (hpn : p = (n : ℤ) + 2) (u v m : ℤ)
    (h : p ^ 3 ∣ v - u - p ^ 2 * m) :
    p ^ 3 ∣ v ^ (n + 1) - u ^ (n + 1) + p ^ 2 * m * u ^ n := by
  have h1 : p ^ 3 ∣ v ^ (n + 1) - (u + p ^ 2 * m) ^ (n + 1) := by
    refine dvd_trans h ?_
    have : v - (u + p ^ 2 * m) = v - u - p ^ 2 * m := by ring
    rw [← this]
    exact sub_dvd_pow_sub_pow v (u + p ^ 2 * m) (n + 1)
  obtain ⟨c, hc⟩ := sq_dvd_pow_add_sub u (p ^ 2 * m) n
  obtain ⟨d, hd⟩ := h1
  refine ⟨d + p * m ^ 2 * c + m * u ^ n, ?_⟩
  have hp : ((n : ℤ) + 1) = p - 1 := by rw [hpn]; ring
  have hc' : (u + p ^ 2 * m) ^ (n + 1)
      = u ^ (n + 1) + ((n : ℤ) + 1) * u ^ n * (p ^ 2 * m) + (p ^ 2 * m) ^ 2 * c := by
    linear_combination hc
  have hd' : v ^ (n + 1) = (u + p ^ 2 * m) ^ (n + 1) + p ^ 3 * d := by linear_combination hd
  rw [hd', hc', hp]
  ring

/-! ## 4. `ZMod p` での記帳：傾き・全単射・`b` の局所化 -/

variable {q : ℕ}

/-- 傾きの定義の記帳：`q⁽²⁾(v) = q⁽²⁾(u) − k·g/u` なら
`λ⁽²⁾(v) = λ⁽²⁾(u) + k·s` で `s = −g/(2u)`。 -/
theorem lambda2_affine [Fact (Nat.Prime q)] (hq : (2 : ZMod q) ≠ 0)
    (u g k q2u q2v : ZMod q) (hu : u ≠ 0) (h : q2v = q2u - k * g / u) :
    q2v / 2 = q2u / 2 + k * (-(g / (2 * u))) := by
  rw [h]
  field_simp
  ring

/-- 傾きが 0 なら `λ⁽²⁾` は持ち上げに依らない（純局所的な障害の形）。 -/
theorem lambda2_const_of_slope_zero [Fact (Nat.Prime q)]
    (u g k q2u q2v : ZMod q) (_hu : u ≠ 0) (h : q2v = q2u - k * g / u) (hg : g = 0) :
    q2v = q2u := by
  rw [h, hg]; simp

/-- 傾きが 0 でなければ `k ↦ λ⁽²⁾(x₀ + pk)` は `F_p` の全単射。
ゆえに `p` 個の持ち上げは `λ⁽²⁾` の値を一度ずつ取る。 -/
theorem lambda2_lift_bijective [Fact (Nat.Prime q)] (l0 s : ZMod q) (hs : s ≠ 0) :
    Function.Bijective (fun k : ZMod q => l0 + k * s) := by
  constructor
  · intro a b hab
    simp only [add_right_inj] at hab
    exact mul_right_cancel₀ hs hab
  · intro y
    refine ⟨(y - l0) * s⁻¹, ?_⟩
    show l0 + ((y - l0) * s⁻¹) * s = y
    rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]
    ring

/-- `λ⁽²⁾ = 0` になる持ち上げはちょうど一つ（傾きが 0 でないとき）。
階数 1 の分裂枡で `v_p(Reg_p) ≥ 1` が「`p` 個に一つ」になる理由である。 -/
theorem lambda2_unique_zero_lift [Fact (Nat.Prime q)] (l0 s : ZMod q) (hs : s ≠ 0) :
    ∃! k : ZMod q, l0 + k * s = 0 := by
  obtain ⟨k0, hk0⟩ : ∃ k0 : ZMod q, k0 * s = -l0 :=
    ⟨(-l0) * s⁻¹, by rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩
  refine ⟨k0, by linear_combination hk0, ?_⟩
  intro y hy
  have hy' : y * s = k0 * s := by rw [hk0]; linear_combination hy
  exact mul_right_cancel₀ hs hy'

/-- **非対角成分の局所化の記帳。** `n²·(2b) = 2λ⁽²⁾(x_j) − 2λ⁽²⁾(x₀)` と
`λ⁽²⁾(x_j) = λ⁽²⁾(x₀) + κ·s` から `b = s·κ/n²`。
（前者は命題 R″_s を `e₁` と `e₁+e_j` に当てたもの、後者が本ファイルの `lambda2_affine`。） -/
theorem b_eq_slope_mul_kappa [Fact (Nat.Prime q)] (hq : (2 : ZMod q) ≠ 0)
    (n b s kap l2j l20 : ZMod q) (hn : n ≠ 0)
    (h : n ^ 2 * (2 * b) = 2 * l2j - 2 * l20) (haff : l2j = l20 + kap * s) :
    b = s * kap / n ^ 2 := by
  rw [haff] at h
  have h2 : 2 * (n ^ 2 * b - kap * s) = 0 := by linear_combination h
  have h3 : n ^ 2 * b - kap * s = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' hq
    · exact h'
  have hn2 : (n : ZMod q) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  rw [eq_div_iff hn2]
  linear_combination h3

end PadicHeight

#print axioms PadicHeight.X_pow_three_dvd_sub_trunc
#print axioms PadicHeight.eval_cube_dvd
#print axioms PadicHeight.eval_shift_of_deriv_eq
#print axioms PadicHeight.sq_dvd_pow_add_sub
#print axioms PadicHeight.fermatQuot2_move
#print axioms PadicHeight.lambda2_affine
#print axioms PadicHeight.lambda2_const_of_slope_zero
#print axioms PadicHeight.lambda2_lift_bijective
#print axioms PadicHeight.lambda2_unique_zero_lift
#print axioms PadicHeight.b_eq_slope_mul_kappa
