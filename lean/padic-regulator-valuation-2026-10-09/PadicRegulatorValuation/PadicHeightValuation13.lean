import Mathlib

/-!
# 分裂の異常素点：高さの**二桁目**と「悪い類」の層の構造

前のファイル（`PadicHeightValuation12`）は、`mod p` の高さ行列が二つの一次形式
`χ`（還元の層）と `γ`（形式群の第一層）だけで書けること（主公式）の代数を載せた。
自然に続く問いは「では `v_p(Reg_p) ≥ 2` は**第三の一次形式** `γ₂` で書けるのか」である。

本ファイルが載せるのはその問いへの算術の段である。中身は三つ。

## 1. Taylor の四次までの切り落としと二桁目（§1・§2）

`P′ = p·G`・`G′ = H` なら、`p` が 6 と素であるかぎり

  `p⁴ ∣ 2(P(r + pk) − P(r)) − 2p²·k·G(r) − p³·k²·H(r)`   (`eval_shift_second_digit`)

（`k³` の係数は `3·Q₃ = p·(…)` から `p` で割れる。これが「二桁目にだけ `k²` の項が出る」ことの理由）。
二項展開（`sq_dvd_pow_add_sub`）と合わせると、`t` が `p²` で割れるとき

  `p⁴ ∣ (u+t)^{n+1} − u^{n+1} − (n+1)u^n t`            (`fermatQuot_second_move`)

で、`n+1 = p−1` と取れば二次の Fermat 商 `Θ(x) = (φ_p(x)^{p−1} − 1)/p²` の
**持ち上げ `x₀ ↦ x₀ + pk` に関する二桁目の展開**（`k` の一次と `p·k²`）が出る。

## 2. 「悪い類」は層ごとにちょうど一つ——一つの `p` 進数への距離（§3）

`f = a + b·X + p·g`（`p ∤ b`）という形の多項式は、**どの層でも**次を満たす：

* 根 `d₀` があれば `f(d) = (d − d₀)·(b + p·q)` と因数分解でき（`root_factor`）、
  したがって **`p^j ∣ f(d) ⟺ p^j ∣ d − d₀`**（`dvd_iff_dvd_sub_root`）
  ——`v_p(f(d)) = v_p(d − d₀)`、すなわち**すべての層が一つの `p` 進数 `d₀` への距離で書ける**。
* 根を仮定しなくても、`p^j ∣ f(d₁)` と `p^j ∣ f(d₂)` なら `p^j ∣ d₁ − d₂`（`unique_bad_class`）。
* そして層ごとに解は存在する（`exists_bad_class`・手で書いた Hensel の一段）。

これが「層 `k` ごとに新しい準同型 `γ_k` を導入する」形**ではない**ことの記帳である：
必要なのは一つの局所 `p` 進数だけで、層は距離の目盛りにすぎない。

## 3. 二桁目の帳簿と `a₁` の項の相殺（§4・§5）

高さの二桁目が `N ≡ (1+p)T + 2pQ (mod p²)` の形に書けたとき、
`p ∣ N ⟺ p ∣ T`（`second_digit_zero_iff`）で、`T = pT₁` のもとで
**`p² ∣ N ⟺ p ∣ T₁ + 2Q`**（`second_digit_criterion`）。
`Q` が大域の量（点の分母の Fermat 商）であることは Lean の外の話だが、
判定の形はこの二行に尽きる。

最後に、`σ` 関数側の一次の項と Weierstrass 方程式側の `a₁` の項が相殺することの
整数の恒等式（`a1_correction_cancels`）を載せる。

幾何・`p` 進解析（`σ` 関数・除法多項式・Vélu・高さの対自身・形式群の級数）は Lean に載っていない。
載っているのは多項式の恒等式・整数の割り切れ・Hensel の一段である。
-/

namespace PadicHeight

open Polynomial

/-! ## 1. Taylor の四次までの切り落とし -/

/-- `Q` から四次未満の部分を引くと `X⁴` で割れる。 -/
theorem X_pow_four_dvd_sub_trunc (Q : Polynomial ℤ) :
    (X : Polynomial ℤ) ^ 4 ∣
      Q - (C (Q.coeff 0) + C (Q.coeff 1) * X + C (Q.coeff 2) * X ^ 2
            + C (Q.coeff 3) * X ^ 3) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub]
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow] <;> norm_num

/-- 評価版：`h⁴ ∣ Q(h) − (Q₀ + Q₁h + Q₂h² + Q₃h³)`。 -/
theorem eval_quartic_dvd (Q : Polynomial ℤ) (h : ℤ) :
    h ^ 4 ∣ Q.eval h - (Q.coeff 0 + Q.coeff 1 * h + Q.coeff 2 * h ^ 2 + Q.coeff 3 * h ^ 3) := by
  obtain ⟨S, hS⟩ := X_pow_four_dvd_sub_trunc Q
  refine ⟨S.eval h, ?_⟩
  have := congrArg (Polynomial.eval h) hS
  simpa using this

/-! ## 2. 二桁目の展開 -/

/-- **本ファイルの第一の要点。** `P′ = p·G`・`G′ = H` なら

> `p⁴ ∣ 2(P(r + pk) − P(r)) − 2p²·k·G(r) − p³·k²·H(r)`。

（適用：`P = φ_p`、`G = φ_p′/p`、`H = G′`、`r = x₀`。`k³` 以降は `p⁴` に落ちる。） -/
theorem eval_shift_second_digit {p : ℤ} (hcop : IsCoprime p 6)
    (P G H : Polynomial ℤ) (hd : P.derivative = C p * G) (hd2 : G.derivative = H)
    (r k : ℤ) :
    p ^ 4 ∣ 2 * (P.eval (r + p * k) - P.eval r) - 2 * p ^ 2 * k * G.eval r
              - p ^ 3 * k ^ 2 * H.eval r := by
  set Q : Polynomial ℤ := P.comp (X + C r) with hQ
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
      rw [hdQ]; simp [Polynomial.coeff_zero_eq_eval_zero, eval_comp]
    rw [← h0, h1]
  have hQ2 : 2 * Q.coeff 2 = p * H.eval r := by
    have h0 : Q.derivative.coeff 1 = Q.coeff 2 * 2 := by
      simpa using (Polynomial.coeff_derivative Q 1)
    have h1 : Q.derivative.coeff 1 = p * (G.comp (X + C r)).coeff 1 := by
      rw [hdQ]; simp
    have h2 : (G.comp (X + C r)).coeff 1 = H.eval r := by
      have h3 : (G.comp (X + C r)).derivative.coeff 0 = (G.comp (X + C r)).coeff 1 := by
        simpa using (Polynomial.coeff_derivative (G.comp (X + C r)) 0)
      have h4 : (G.comp (X + C r)).derivative = H.comp (X + C r) := by
        rw [Polynomial.derivative_comp, hd2]; simp
      rw [← h3, h4, Polynomial.coeff_zero_eq_eval_zero, eval_comp]
      simp
    rw [h0] at h1
    rw [h2] at h1
    linarith [h1]
  have hQ3 : p ∣ Q.coeff 3 := by
    have h0 : Q.derivative.coeff 2 = Q.coeff 3 * 3 := by
      simpa using (Polynomial.coeff_derivative Q 2)
    have h1 : Q.derivative.coeff 2 = p * (G.comp (X + C r)).coeff 2 := by
      rw [hdQ]; simp
    have h2 : p ∣ Q.coeff 3 * 3 := by rw [h0] at h1; exact ⟨_, h1⟩
    have h3 : IsCoprime p 3 := by
      have : (3 : ℤ) ∣ 6 := by norm_num
      exact IsCoprime.of_isCoprime_of_dvd_right hcop this
    exact (IsCoprime.dvd_of_dvd_mul_right h3) h2
  obtain ⟨S, hS⟩ := eval_quartic_dvd Q (p * k)
  have hval : P.eval (r + p * k) = Q.eval (p * k) := by rw [hev]; ring_nf
  obtain ⟨c2, hc2⟩ : ∃ c2, Q.coeff 3 = p * c2 := hQ3
  rw [hQ0, hQ1, hc2] at hS
  refine ⟨2 * k ^ 4 * S + 2 * c2 * k ^ 3, ?_⟩
  rw [hval]
  linear_combination 2 * hS + p ^ 2 * k ^ 2 * hQ2

/-- 二項展開：`t² ∣ (u+t)^{n+1} − u^{n+1} − (n+1)u^n t`。 -/
theorem sq_dvd_pow_add_sub (u t : ℤ) : ∀ n : ℕ,
    t ^ 2 ∣ (u + t) ^ (n + 1) - u ^ (n + 1) - (n + 1 : ℤ) * u ^ n * t
  | 0 => by simp
  | (n + 1) => by
      obtain ⟨c, hc⟩ := sq_dvd_pow_add_sub u t n
      refine ⟨c * (u + t) + (n + 1 : ℤ) * u ^ n, ?_⟩
      push_cast
      linear_combination (u + t) * hc

/-- **二桁目の Fermat 商の移り方。** `p² ∣ t` なら
`p⁴ ∣ (u+t)^{n+1} − u^{n+1} − (n+1)u^n t`。 -/
theorem fermatQuot_second_move {p t : ℤ} (ht : p ^ 2 ∣ t) (u : ℤ) (n : ℕ) :
    p ^ 4 ∣ (u + t) ^ (n + 1) - u ^ (n + 1) - (n + 1 : ℤ) * u ^ n * t := by
  obtain ⟨c, hc⟩ := sq_dvd_pow_add_sub u t n
  obtain ⟨m, hm⟩ := ht
  refine ⟨m ^ 2 * c, ?_⟩
  rw [hc, hm]; ring

/-! ## 3. 「悪い類」は層ごとにちょうど一つ -/

section Layers

variable {p a b : ℤ} {g : Polynomial ℤ}

/-- `f := a + b·X + p·g` の形。 -/
noncomputable def layerPoly (a b p : ℤ) (g : Polynomial ℤ) : Polynomial ℤ :=
  C a + C b * X + C p * g

@[simp] theorem layerPoly_eval (a b p : ℤ) (g : Polynomial ℤ) (d : ℤ) :
    (layerPoly a b p g).eval d = a + b * d + p * g.eval d := by
  simp [layerPoly]

/-- **根を持つときの因数分解。** `f(d₀) = 0` なら `f(d) = (d − d₀)(b + p·q)`。 -/
theorem root_factor (a b p : ℤ) (g : Polynomial ℤ) (d₀ d : ℤ)
    (h0 : (layerPoly a b p g).eval d₀ = 0) :
    ∃ q : ℤ, (layerPoly a b p g).eval d = (d - d₀) * (b + p * q) := by
  obtain ⟨q, hq⟩ : (d - d₀) ∣ g.eval d - g.eval d₀ := sub_dvd_eval_sub d d₀ g
  refine ⟨q, ?_⟩
  have h1 : (layerPoly a b p g).eval d - (layerPoly a b p g).eval d₀
      = b * (d - d₀) + p * (g.eval d - g.eval d₀) := by
    simp [layerPoly_eval]; ring
  rw [h0, sub_zero] at h1
  rw [h1, hq]; ring

/-- **本ファイルの第二の要点（層の帰納の形）。** `p ∤ b` で `f(d₀) = 0` なら、
すべての `j` で `p^j ∣ f(d) ⟺ p^j ∣ d − d₀`。すなわち `v_p(f(d)) = v_p(d − d₀)`：
層ごとの新しい準同型ではなく、**一つの `p` 進数 `d₀` への距離**で全層が書ける。 -/
theorem dvd_iff_dvd_sub_root {p : ℤ} (hp : Prime p) (a b : ℤ) (g : Polynomial ℤ)
    (hb : ¬ p ∣ b) (d₀ d : ℤ) (h0 : (layerPoly a b p g).eval d₀ = 0) (j : ℕ) :
    p ^ j ∣ (layerPoly a b p g).eval d ↔ p ^ j ∣ d - d₀ := by
  obtain ⟨q, hq⟩ := root_factor a b p g d₀ d h0
  constructor
  · intro h
    rw [hq] at h
    have hcop : IsCoprime p (b + p * q) := by
      rw [(Prime.coprime_iff_not_dvd hp)]
      intro hdvd
      exact hb (by
        have : p ∣ b := by
          have h2 : b = (b + p * q) - p * q := by ring
          rw [h2]; exact dvd_sub hdvd ⟨q, rfl⟩
        exact this)
    exact (IsCoprime.pow_left hcop).dvd_of_dvd_mul_right h
  · intro h
    rw [hq]
    exact Dvd.dvd.mul_right h _

/-- 根を仮定しない形：層 `j` の「悪い類」はちょうど一つ。 -/
theorem unique_bad_class {p : ℤ} (hp : Prime p) (a b : ℤ) (g : Polynomial ℤ)
    (hb : ¬ p ∣ b) (d₁ d₂ : ℤ) (j : ℕ)
    (h1 : p ^ j ∣ (layerPoly a b p g).eval d₁)
    (h2 : p ^ j ∣ (layerPoly a b p g).eval d₂) :
    p ^ j ∣ d₁ - d₂ := by
  obtain ⟨q, hq⟩ : (d₁ - d₂) ∣ g.eval d₁ - g.eval d₂ := sub_dvd_eval_sub d₁ d₂ g
  have hdiff : (layerPoly a b p g).eval d₁ - (layerPoly a b p g).eval d₂
      = (d₁ - d₂) * (b + p * q) := by
    simp only [layerPoly_eval]
    linear_combination p * hq
  have hd : p ^ j ∣ (d₁ - d₂) * (b + p * q) := by rw [← hdiff]; exact dvd_sub h1 h2
  have hcop : IsCoprime p (b + p * q) := by
    rw [(Prime.coprime_iff_not_dvd hp)]
    intro hdvd
    exact hb (by
      have h2' : b = (b + p * q) - p * q := by ring
      rw [h2']; exact dvd_sub hdvd ⟨q, rfl⟩)
  exact (IsCoprime.pow_left hcop).dvd_of_dvd_mul_right hd

/-- **Hensel の一段（手書き）。** `p ∤ b` なら層 `j` の悪い類は存在する。 -/
theorem exists_bad_class {p : ℤ} (hp : Prime p) (a b : ℤ) (g : Polynomial ℤ)
    (hb : ¬ p ∣ b) : ∀ j : ℕ, ∃ d : ℤ, p ^ j ∣ (layerPoly a b p g).eval d := by
  intro j
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
      obtain ⟨d, w, hw⟩ := ih
      obtain ⟨x, y, hxy⟩ : IsCoprime b p := ((Prime.coprime_iff_not_dvd hp).mpr hb).symm
      refine ⟨d + p ^ j * (- (w * x)), ?_⟩
      obtain ⟨q, hq⟩ : (p ^ j * (- (w * x))) ∣
          g.eval (d + p ^ j * (- (w * x))) - g.eval d := by
        have := sub_dvd_eval_sub (d + p ^ j * (- (w * x))) d g
        simpa using this
      have hw' : a + b * d + p * g.eval d = p ^ j * w := by
        simpa [layerPoly_eval] using hw
      refine ⟨w * y - w * x * q, ?_⟩
      simp only [layerPoly_eval]
      linear_combination hw' + p * hq - (p ^ j * w) * hxy

end Layers

/-! ## 4. 二桁目の帳簿 -/

/-- 一桁目：`N ≡ (1+p)T + 2pQ (mod p²)` なら `p ∣ N ⟺ p ∣ T`。 -/
theorem second_digit_zero_iff {p N T Q : ℤ}
    (h : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q)) : p ∣ N ↔ p ∣ T := by
  obtain ⟨c, hc⟩ := h
  constructor
  · intro hN
    have h1 : T = N - p * (T + 2 * Q + p * c) := by linarith [hc]
    rw [h1]
    exact dvd_sub hN ⟨_, rfl⟩
  · intro hT
    have h1 : N = (1 + p) * T + 2 * p * Q + p ^ 2 * c := by linarith [hc]
    rw [h1]
    obtain ⟨t1, rfl⟩ := hT
    exact ⟨(1 + p) * t1 + 2 * Q + p * c, by ring⟩

/-- **二桁目の判定。** `N ≡ (1+p)T + 2pQ (mod p²)` で `T = p·T₁` なら
`p² ∣ N ⟺ p ∣ T₁ + 2Q`。（`Q` が大域の量であることが「三層目に局所の準同型が無い」ことの
理由であり、判定の形はこの一行に尽きる。） -/
theorem second_digit_criterion {p N T₁ Q : ℤ} (hp : Prime p)
    (h : p ^ 2 ∣ N - ((1 + p) * (p * T₁) + 2 * p * Q)) :
    p ^ 2 ∣ N ↔ p ∣ T₁ + 2 * Q := by
  obtain ⟨c, hc⟩ := h
  have hp0 : p ≠ 0 := hp.ne_zero
  constructor
  · intro hN
    obtain ⟨n2, hn2⟩ := hN
    refine ⟨n2 - T₁ - c, ?_⟩
    have key : p * (T₁ + 2 * Q) = p * (p * (n2 - T₁ - c)) := by
      linear_combination hn2 - hc
    exact mul_left_cancel₀ hp0 key
  · intro hd
    obtain ⟨k, hk⟩ := hd
    exact ⟨T₁ + k + c, by linear_combination hc + p * hk⟩

/-! ## 5. `a₁` の項の相殺 -/

/-- **`σ` 側の一次項と Weierstrass 側の `a₁` 項は相殺する。**
`a = p·A`・`ψ = p²·Ψ`・`ω² − φ³ = −a·φ·ω·ψ + p⁴·X` のとき、
`S·p³·φ²·ω = a·ψ·(ω² − φ³)` で定まる `S` は `p³` で割れる（`p ∤ φ`・`p ∤ ω`）。
これが二桁目の公式に `a₁` が現れない理由である。 -/
theorem a1_correction_cancels {p A Ψ φ ω X S : ℤ} (hp : Prime p)
    (hφ : ¬ p ∣ φ) (hω : ¬ p ∣ ω)
    (heq : ω ^ 2 - φ ^ 3 = -((p * A) * φ * ω * (p ^ 2 * Ψ)) + p ^ 4 * X)
    (hS : S * p ^ 3 * φ ^ 2 * ω = (p * A) * (p ^ 2 * Ψ) * (ω ^ 2 - φ ^ 3)) :
    p ^ 3 ∣ S := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set Z : ℤ := - (A ^ 2 * Ψ ^ 2 * φ * ω) + p * (A * Ψ * X) with hZ
  have h1 : p ^ 3 * (S * (φ ^ 2 * ω)) = p ^ 3 * (p ^ 3 * Z) := by
    rw [hZ]; linear_combination hS + (p ^ 3 * A * Ψ) * heq
  have h3 : S * (φ ^ 2 * ω) = p ^ 3 * Z := mul_left_cancel₀ (pow_ne_zero 3 hp0) h1
  have hcop : IsCoprime (p ^ 3) (φ ^ 2 * ω) :=
    IsCoprime.pow_left
      (IsCoprime.mul_right
        (IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp).mpr hφ))
        ((Prime.coprime_iff_not_dvd hp).mpr hω))
  exact hcop.dvd_of_dvd_mul_right ⟨Z, h3⟩

end PadicHeight

#print axioms PadicHeight.eval_quartic_dvd
#print axioms PadicHeight.eval_shift_second_digit
#print axioms PadicHeight.fermatQuot_second_move
#print axioms PadicHeight.root_factor
#print axioms PadicHeight.dvd_iff_dvd_sub_root
#print axioms PadicHeight.unique_bad_class
#print axioms PadicHeight.exists_bad_class
#print axioms PadicHeight.second_digit_zero_iff
#print axioms PadicHeight.second_digit_criterion
#print axioms PadicHeight.a1_correction_cancels
