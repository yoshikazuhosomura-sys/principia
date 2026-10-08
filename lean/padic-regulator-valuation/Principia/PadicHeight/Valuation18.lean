import Mathlib

/-!
# 非退化性の算術——`ψ_p` 側は無条件、`φ_p` 側は一桁だけ先

`p ≥ 5` 良通常・異常・分裂の楕円曲線で、`T` を `p` 等分点、`x_T = x(T)` とする。
本ファイルは二つの付値の主張の**算術の段**を記帳する。幾何と `p` 進解析の側は
仮定として入る（形式群・除法多項式・Tate 曲線・不変微分は Mathlib に無い）。

* **`ψ_p` の側（仮定なし）。**形式群の恒等式
  `φ_p(X(t)) = p^{−2} μ(t)^{−2} u([p](t)) Ψ₁(t)²` を `t = 0` で読むと
  `p²·Φ = S²`（`Φ = φ_p(x_T)` は単数、`S = Ψ₁(0) = ψ_p′(x_T)·c₁`、`c₁` は単数）。
  ここから **`v_p(ψ_p′(x_T)) = 1` ちょうど**（`psi_deriv_valuation_one`）。

* **`φ_p` の側（非退化性 (ND)）。**同じ恒等式を `t` で一度微分すると
  `p·G(x_T) = 2·H′(x_T)`、`H := (x³+a₄x+a₆)·(ψ_p′/p)²`、
  `H′ = K·Br`、`K = ψ_p′/p`（単数）、`Br = (3x²+a₄)K + 2(x³+a₄x+a₆)K′`。
  この形からは **`p ∣ Br` が自動で従い**（`bracket_divisible`）、
  **(ND) ⟺ `v_p(Br) = 1` ちょうど**（`nd_iff_bracket`）。
  すなわち (ND) は `ψ_p` の `mod p³` の情報で、`ψ_p` の `mod p²`（＝`K mod p`）より
  ちょうど一桁先にある。これが「不変微分では届かない」の算術的な言い換えである。

* **重み勘定。**終結式 `Res_x(G, ψ_p mod p)` の重みが `12·m_p`、
  `m_p = (p²−1)(2p²−3)/24` であること（`resultant_weight`）、`m_p` が整数であること
  （`m_p_integral`）、および `Res_x(G, ψ_p mod p) = c^{deg G}·Res_x(G, g)^p`
  という分解と整合すること（`resultant_weight_split`）を記帳する。

* **二者択一。**体の上で `R = c·D^m`、`c ≠ 0`、`D ≠ 0` なら `R ≠ 0`
  （`ne_zero_of_const_mul_pow`）、互いに素なら共通根を持たない
  （`eval_ne_zero_of_isCoprime`）。この二つで「`c_p ≠ 0` ⟹ (ND)」が閉じる。
-/

namespace PadicHeight

/-! ## §1 平方の付値——`ψ_p′(x_T)` はちょうど `p` で一度割れる -/

/-- `p²·Φ = S²` で `Φ` が単数なら `v_p(S) = 1` ちょうど。 -/
theorem sq_valuation_one {p Φ S : ℤ} (hp : Prime p) (h : p ^ 2 * Φ = S ^ 2)
    (hΦ : ¬ p ∣ Φ) : p ∣ S ∧ ¬ p ^ 2 ∣ S := by
  have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
  have hpS : p ∣ S := by
    refine hp.dvd_of_dvd_pow (n := 2) ⟨p * Φ, ?_⟩
    rw [← h]; ring
  obtain ⟨S', rfl⟩ := hpS
  have hΦ' : Φ = S' ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hp0) ?_
    rw [h]; ring
  refine ⟨⟨S', rfl⟩, ?_⟩
  rintro ⟨k, hk⟩
  have hS' : S' = p * k := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hk]; ring
  exact hΦ ⟨p * k ^ 2, by rw [hΦ', hS']; ring⟩

/-- **`v_p(ψ_p′(x_T)) = 1`（仮定なし）。**`S = K·c` で `c` が単数なら `K` の付値も 1。 -/
theorem psi_deriv_valuation_one {p Φ S K c : ℤ} (hp : Prime p) (h : p ^ 2 * Φ = S ^ 2)
    (hΦ : ¬ p ∣ Φ) (hS : S = K * c) (hc : ¬ p ∣ c) : p ∣ K ∧ ¬ p ^ 2 ∣ K := by
  obtain ⟨h1, h2⟩ := sq_valuation_one hp h hΦ
  have h1' : p ∣ K * c := by rw [← hS]; exact h1
  have hpK : p ∣ K := by
    rcases hp.dvd_mul.mp h1' with h | h
    · exact h
    · exact absurd h hc
  obtain ⟨K', rfl⟩ := hpK
  refine ⟨⟨K', rfl⟩, ?_⟩
  rintro ⟨k, hk⟩
  have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
  have hK' : K' = p * k := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hk]; ring
  exact h2 ⟨k * c, by rw [hS, hK']; ring⟩

/-! ## §2 非退化性 (ND) の算術 -/

/-- `p·G = 2·(K·Br)` で `2` と `K` が単数なら、**`p ∣ Br` は自動**。 -/
theorem bracket_divisible {p G K Br : ℤ} (hp : Prime p) (hp2 : ¬ p ∣ 2)
    (hK : ¬ p ∣ K) (hid : p * G = 2 * (K * Br)) : p ∣ Br := by
  have h : p ∣ 2 * (K * Br) := ⟨G, hid.symm⟩
  rcases hp.dvd_mul.mp h with h | h
  · exact absurd h hp2
  · rcases hp.dvd_mul.mp h with h | h
    · exact absurd h hK
    · exact h

/-- **(ND) ⟺ `v_p(Br) = 1`。**`¬ p ∣ G` が非退化性、`Br` は `ψ_p` だけで書ける括弧。 -/
theorem nd_iff_bracket {p G K Br : ℤ} (hp : Prime p) (hp2 : ¬ p ∣ 2)
    (hK : ¬ p ∣ K) (hid : p * G = 2 * (K * Br)) :
    (¬ p ∣ G) ↔ ¬ p ^ 2 ∣ Br := by
  obtain ⟨Br', rfl⟩ := bracket_divisible hp hp2 hK hid
  have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
  have hG : G = 2 * (K * Br') := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hid]; ring
  constructor
  · intro hGnd hsq
    obtain ⟨k, hk⟩ := hsq
    have : Br' = p * k := by
      refine mul_left_cancel₀ hp0 ?_
      rw [hk]; ring
    exact hGnd ⟨2 * (K * k), by rw [hG, this]; ring⟩
  · intro hsq hGd
    refine hsq ?_
    have hGd' : p ∣ 2 * (K * Br') := by rw [← hG]; exact hGd
    have hBr' : p ∣ Br' := by
      rcases hp.dvd_mul.mp hGd' with h | h
      · exact absurd h hp2
      · rcases hp.dvd_mul.mp h with h | h
        · exact absurd h hK
        · exact h
    obtain ⟨k, hk⟩ := hBr'
    exact ⟨k, by rw [hk]; ring⟩

/-- 非退化性が成り立つときの帰結を単独で。 -/
theorem nd_of_bracket_exact {p G K Br : ℤ} (hp : Prime p) (hp2 : ¬ p ∣ 2)
    (hK : ¬ p ∣ K) (hid : p * G = 2 * (K * Br)) (hBr : ¬ p ^ 2 ∣ Br) : ¬ p ∣ G :=
  (nd_iff_bracket hp hp2 hK hid).mpr hBr

/-! ## §3 終結式の重み勘定 -/

/-- `p` が 2 でも 3 でも割れなければ `24 ∣ (p²−1)(2p²−3)`、
すなわち `m_p = (p²−1)(2p²−3)/24` は整数である。 -/
theorem m_p_integral (p : ℤ) (h2 : ¬ (2 : ℤ) ∣ p) (h3 : ¬ (3 : ℤ) ∣ p) :
    (24 : ℤ) ∣ (p ^ 2 - 1) * (2 * p ^ 2 - 3) := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, p = 12 * j + 1 ∨ p = 12 * j + 5 ∨ p = 12 * j + 7 ∨ p = 12 * j + 11 :=
    ⟨p / 12, by omega⟩
  rcases hj with rfl | rfl | rfl | rfl
  · exact ⟨j * (6 * j + 1) * (2 * (12 * j + 1) ^ 2 - 3), by ring⟩
  · exact ⟨(3 * j + 1) * (2 * j + 1) * (2 * (12 * j + 5) ^ 2 - 3), by ring⟩
  · exact ⟨(2 * j + 1) * (3 * j + 2) * (2 * (12 * j + 7) ^ 2 - 3), by ring⟩
  · exact ⟨(6 * j + 5) * (j + 1) * (2 * (12 * j + 11) ^ 2 - 3), by ring⟩

/-- 同様に `m_p^{(g)} = (p−1)²(p+1)/12` も整数である
（`Res_x(G, g)` の側の指数。`g` は `ψ_p mod p` の分離部分）。 -/
theorem m_g_integral (p : ℤ) (h2 : ¬ (2 : ℤ) ∣ p) (h3 : ¬ (3 : ℤ) ∣ p) :
    (12 : ℤ) ∣ (p - 1) ^ 2 * (p + 1) := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, p = 12 * j + 1 ∨ p = 12 * j + 5 ∨ p = 12 * j + 7 ∨ p = 12 * j + 11 :=
    ⟨p / 12, by omega⟩
  rcases hj with rfl | rfl | rfl | rfl
  · exact ⟨24 * j ^ 2 * (6 * j + 1), by ring⟩
  · exact ⟨8 * (3 * j + 1) ^ 2 * (2 * j + 1), by ring⟩
  · exact ⟨12 * (2 * j + 1) ^ 2 * (3 * j + 2), by ring⟩
  · exact ⟨4 * (6 * j + 5) ^ 2 * (j + 1), by ring⟩

/-- **重みの公式。**`A` の `x` 次数 `m`・重み `α`、`B` の `x` 次数 `n`・重み `β` のとき
`Res_x(A,B)` の重みは `nα + mβ − 2mn`。`A = G mod p`（`m = p²−(p+3)/2`, `α = 2p²−2`）、
`B = ψ_p mod p`（`n = p(p−1)/2`, `β = p²−1`）を入れると、それは `12·m_p` に等しい
（`p = 2q+1` と書いた形。両辺 2 倍して整数の等式にしてある）。 -/
theorem resultant_weight (q : ℤ) :
    2 * ((2 * q + 1) * q * (2 * (2 * q + 1) ^ 2 - 2)
        + ((2 * q + 1) ^ 2 - (q + 2)) * ((2 * q + 1) ^ 2 - 1)
        - 2 * ((2 * q + 1) ^ 2 - (q + 2)) * ((2 * q + 1) * q))
      = ((2 * q + 1) ^ 2 - 1) * (2 * (2 * q + 1) ^ 2 - 3) := by
  ring

/-- **分解との整合。**`ψ_p ≡ c·g(x^p) (mod p)` から
`Res_x(G, ψ_p mod p) = c^{deg G}·Res_x(G, g)^p` で、指数の勘定は
`12 m_p = 12 p·m_p^{(g)} + (deg G)·(p−1)`。`p = 2q+1` の形で書く。 -/
theorem resultant_weight_split (q : ℤ) :
    ((2 * q + 1) ^ 2 - 1) * (2 * (2 * q + 1) ^ 2 - 3)
      = 2 * ((2 * q + 1) * ((2 * q + 1) - 1) ^ 2 * ((2 * q + 1) + 1)
             + ((2 * q + 1) ^ 2 - (q + 2)) * ((2 * q + 1) - 1)) := by
  ring

/-! ## §4 二者択一（`c_p ≠ 0` から (ND) へ） -/

/-- 体の上で `R = c·D^m`、`c ≠ 0`、`D ≠ 0` なら `R ≠ 0`。 -/
theorem ne_zero_of_const_mul_pow {F : Type*} [Field F] {c D R : F} {m : ℕ}
    (hR : R = c * D ^ m) (hc : c ≠ 0) (hD : D ≠ 0) : R ≠ 0 := by
  rw [hR]
  exact mul_ne_zero hc (pow_ne_zero m hD)

/-- 互いに素な二つの多項式は共通根を持たない。
`g = G mod p`、`h = ψ_p mod p`、`r = x(T̄)` に当てると、これが (ND) そのものである。 -/
theorem eval_ne_zero_of_isCoprime {F : Type*} [Field F] {g h : Polynomial F}
    (hco : IsCoprime g h) {r : F} (hr : h.eval r = 0) : g.eval r ≠ 0 := by
  intro hg
  obtain ⟨u, v, huv⟩ := hco
  have := congrArg (Polynomial.eval r) huv
  simp [Polynomial.eval_add, Polynomial.eval_mul, hg, hr] at this

/-- 記帳：非退化性の三つの言い換えを一つに。`Br` は `ψ_p` だけで書ける量で、
`p ∣ Br` は常に成り立ち、ちょうど一度割れることが (ND) と同値である。 -/
theorem nondegeneracy_summary {p G K Br : ℤ} (hp : Prime p) (hp2 : ¬ p ∣ 2)
    (hK : ¬ p ∣ K) (hid : p * G = 2 * (K * Br)) :
    p ∣ Br ∧ ((¬ p ∣ G) ↔ ¬ p ^ 2 ∣ Br) :=
  ⟨bracket_divisible hp hp2 hK hid, nd_iff_bracket hp hp2 hK hid⟩

/-- `p` が 2 でも 3 でも割れなければ `24 ∣ p²−1`。
これで `m_K = (p²−1)(p²−3)/24` と `m_S = p²(p²−1)/24` はどちらも整数である。 -/
theorem twentyfour_dvd_sq_sub_one (p : ℤ) (h2 : ¬ (2 : ℤ) ∣ p) (h3 : ¬ (3 : ℤ) ∣ p) :
    (24 : ℤ) ∣ p ^ 2 - 1 := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, p = 12 * j + 1 ∨ p = 12 * j + 5 ∨ p = 12 * j + 7 ∨ p = 12 * j + 11 :=
    ⟨p / 12, by omega⟩
  rcases hj with rfl | rfl | rfl | rfl
  · exact ⟨6 * j ^ 2 + j, by ring⟩
  · exact ⟨6 * j ^ 2 + 5 * j + 1, by ring⟩
  · exact ⟨6 * j ^ 2 + 7 * j + 2, by ring⟩
  · exact ⟨6 * j ^ 2 + 11 * j + 5, by ring⟩

/-- **`K = ψ_p′/p` の側の重み。**`deg K = m'`（`2m' = p²−3`）、重み `2m'`、
`ψ_p mod p` は `x` 次数 `n`・重み `p²−1`。終結式の重みは `(p²−3)(p²−1) / 2 = 12·m_K`。 -/
theorem resultant_weight_K (p n m' : ℤ) (hm : 2 * m' = p ^ 2 - 3) :
    2 * (n * (p ^ 2 - 3) + m' * (p ^ 2 - 1) - 2 * m' * n) = (p ^ 2 - 3) * (p ^ 2 - 1) := by
  linear_combination ((p ^ 2 - 1) - 2 * n) * hm

/-- **`S₁` の側の重み。**`deg(S₁ mod p) = n`（`2n = p²−p`）、重み `p²+1`。
終結式の重みは `p²(p²−1)/2 = 12·m_S`。 -/
theorem resultant_weight_S (p n : ℤ) (hn : 2 * n = p ^ 2 - p) :
    2 * (n * (p ^ 2 + 1) + n * (p ^ 2 - 1) - 2 * n * n) = p ^ 2 * (p ^ 2 - 1) := by
  linear_combination (-(2 * n - p ^ 2 - p)) * hn

/-- 二つの指数を足すともとの指数になる：`m_K + m_S = m_p`。 -/
theorem m_K_add_m_S (p : ℤ) :
    (p ^ 2 - 1) * (p ^ 2 - 3) + p ^ 2 * (p ^ 2 - 1) = (p ^ 2 - 1) * (2 * p ^ 2 - 3) := by
  ring

/-- **分解 `G ≡ −K·S₁ (mod ψ_p)` の帰結。**`K` が根で消えないなら、
非退化性は `S₁` がその根で消えないことと同値である。 -/
theorem nd_iff_S_ne_zero {F : Type*} [Field F] {g k s ψ h : Polynomial F}
    (hg : g = -(k * s) + ψ * h) {r : F} (hψ : ψ.eval r = 0) (hk : k.eval r ≠ 0) :
    g.eval r ≠ 0 ↔ s.eval r ≠ 0 := by
  have hev : g.eval r = -(k.eval r * s.eval r) := by
    rw [hg]; simp [hψ]
  rw [hev]
  simp [hk]

end PadicHeight

#print axioms PadicHeight.sq_valuation_one
#print axioms PadicHeight.psi_deriv_valuation_one
#print axioms PadicHeight.bracket_divisible
#print axioms PadicHeight.nd_iff_bracket
#print axioms PadicHeight.nd_of_bracket_exact
#print axioms PadicHeight.m_p_integral
#print axioms PadicHeight.m_g_integral
#print axioms PadicHeight.resultant_weight
#print axioms PadicHeight.resultant_weight_split
#print axioms PadicHeight.ne_zero_of_const_mul_pow
#print axioms PadicHeight.eval_ne_zero_of_isCoprime
#print axioms PadicHeight.nondegeneracy_summary
#print axioms PadicHeight.twentyfour_dvd_sq_sub_one
#print axioms PadicHeight.resultant_weight_K
#print axioms PadicHeight.resultant_weight_S
#print axioms PadicHeight.m_K_add_m_S
#print axioms PadicHeight.nd_iff_S_ne_zero
