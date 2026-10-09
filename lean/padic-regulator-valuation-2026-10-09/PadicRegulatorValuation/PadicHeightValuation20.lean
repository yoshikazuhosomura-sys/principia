import Mathlib

/-!
# 奇数次分離同種写像の二本の恒等式と、`(ND)` の還元の算術

これまでに `(ND) ⟺ S₁(x(T̄)) ≢ 0 (mod p)` まで落ち、`S₁ = 2·Dψ_p`（草稿 §3.12 の命題 15。
`D` は Serre 微分の `−1` 倍）を
`p ≤ 19` で確かめていた。ここではその恒等式を**一本の合同式**に還元した。還元に使う代数は
「同種写像の二式 `(*) P′h − 2Ph′ = cΩ`・`(**) w·Ω² = P³ + a₄Ph⁴ + a₆h^6` を微分して
核多項式の根で見る」だけで、これは Lean に載る。幾何（除法多項式・Verschiebung・
標準部分群・モジュラー形式）は Mathlib に無いので仮定として入り、**主定理は Lean の定理ではない**。

* `isogeny_A1` : `h(ξ) = 0` なら `P(ξ)²·(4w(ξ)h′(ξ)² − c²P(ξ)) = 0`。
  すなわち `P(ξ) ≠ 0` なら `c²P(ξ) = 4w(ξ)h′(ξ)²`（補題 A1）。
* `isogeny_A1_field` : 整域で `P(ξ) ≠ 0` としたときの形。
* `isogeny_A2_core` : 一段微分した式から `c²P′(ξ) = 2[w(h′)²]′(ξ)`（補題 A2）。
* `deriv_eval_of_factor` : `F = h·C` と `h(ξ) = 0` から `F′(ξ) = h′(ξ)·C(ξ)`。
* `residue_iff` : `h′(ξ)·C(ξ) = −2W` のとき `C(ξ) = 2A²·d ⟺ W + A²h′(ξ)·d = 0`（(R′) の同値）。
* `const_mod_p_deriv` : `M = C a + C p · T` なら `M′ = C p · T′`（`M ≡ 定数 (mod p) ⟹ p ∣ M′`）。
* `lead_cancel`, `lc_difference`, `deg_K_eq`, `weight_L` : 主係数・次数・重みの勘定
  （`p = 2n+1` の一本の相殺、`(p²−1)/2 ≡ (p−1)/2 (mod p)` など）。
-/

namespace PadicHeight

open Polynomial

/-! ## §1 一般の奇数次分離同種写像の二本 -/

/-- 補題 A1。`(*)` と `(**)` を核多項式の根 `ξ` で見ると
`P(ξ)²·(4w(ξ)h′(ξ)² − c²P(ξ)) = 0`。 -/
theorem isogeny_A1 {R : Type*} [CommRing R] (P h Om w : R[X]) (a4 a6 c : R) (ξ : R)
    (hs : derivative P * h - 2 * P * derivative h = C c * Om)
    (hss : w * Om ^ 2 = P ^ 3 + C a4 * P * h ^ 4 + C a6 * h ^ 6)
    (hξ : h.eval ξ = 0) :
    (P.eval ξ) ^ 2 * (4 * w.eval ξ * (derivative h).eval ξ ^ 2 - c ^ 2 * P.eval ξ) = 0 := by
  have E1 : c * Om.eval ξ = -(2 * P.eval ξ * (derivative h).eval ξ) := by
    have := congrArg (Polynomial.eval ξ) hs
    simp [hξ] at this
    linear_combination -this
  have E2 : w.eval ξ * Om.eval ξ ^ 2 = P.eval ξ ^ 3 := by
    have := congrArg (Polynomial.eval ξ) hss
    simp [hξ] at this
    linear_combination this
  linear_combination (w.eval ξ * (2 * P.eval ξ * (derivative h).eval ξ - c * Om.eval ξ)) * E1
    + c ^ 2 * E2

/-- 補題 A1（整域で `P(ξ) ≠ 0` のとき）。 -/
theorem isogeny_A1_domain {R : Type*} [CommRing R] [IsDomain R]
    (P h Om w : R[X]) (a4 a6 c : R) (ξ : R)
    (hs : derivative P * h - 2 * P * derivative h = C c * Om)
    (hss : w * Om ^ 2 = P ^ 3 + C a4 * P * h ^ 4 + C a6 * h ^ 6)
    (hξ : h.eval ξ = 0) (hP : P.eval ξ ≠ 0) :
    c ^ 2 * P.eval ξ = 4 * w.eval ξ * (derivative h).eval ξ ^ 2 := by
  have h0 := isogeny_A1 P h Om w a4 a6 c ξ hs hss hξ
  have := mul_eq_zero.mp h0
  rcases this with h1 | h2
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1) hP
  · exact (sub_eq_zero.mp h2).symm

/-- 補題 A2（算術の核・可換環で割り算なし）。`(*)`・`(**)` とその一階微分を根 `ξ` で
見た値（`E1, E3, E4`）と補題 A1 から、`2P₀²·(c²P′(ξ) − 2[w(h′)²]′(ξ)) = 0`。 -/
theorem isogeny_A2_core {R : Type*} [CommRing R]
    (P₀ P₁ h₁ h₂ w₀ w₁ c Om₀ Om₁ : R)
    (E1 : c * Om₀ = -(2 * P₀ * h₁))
    (E3 : c * Om₁ = -(P₁ * h₁) - 2 * P₀ * h₂)
    (E4 : w₁ * Om₀ ^ 2 + 2 * w₀ * Om₀ * Om₁ = 3 * P₀ ^ 2 * P₁)
    (A1 : c ^ 2 * P₀ = 4 * w₀ * h₁ ^ 2) :
    2 * P₀ ^ 2 * (c ^ 2 * P₁ - 2 * (w₁ * h₁ ^ 2 + 2 * w₀ * h₁ * h₂)) = 0 := by
  linear_combination (w₁ * (c * Om₀ - 2 * P₀ * h₁) + 2 * w₀ * (c * Om₁)) * E1
    + (-4 * w₀ * P₀ * h₁) * E3 + (-c ^ 2) * E4 + (-(P₀ * P₁)) * A1

/-- 補題 A2（体・`P₀ ≠ 0`）：`c²·P′(ξ) = 2·[w·(h′)²]′(ξ)`。 -/
theorem isogeny_A2 {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    (P₀ P₁ h₁ h₂ w₀ w₁ c Om₀ Om₁ : K) (hP : P₀ ≠ 0)
    (E1 : c * Om₀ = -(2 * P₀ * h₁))
    (E3 : c * Om₁ = -(P₁ * h₁) - 2 * P₀ * h₂)
    (E4 : w₁ * Om₀ ^ 2 + 2 * w₀ * Om₀ * Om₁ = 3 * P₀ ^ 2 * P₁)
    (A1 : c ^ 2 * P₀ = 4 * w₀ * h₁ ^ 2) :
    c ^ 2 * P₁ = 2 * (w₁ * h₁ ^ 2 + 2 * w₀ * h₁ * h₂) := by
  have h0 := isogeny_A2_core P₀ P₁ h₁ h₂ w₀ w₁ c Om₀ Om₁ E1 E3 E4 A1
  have hne : (2 : K) * P₀ ^ 2 ≠ 0 := mul_ne_zero hchar (pow_ne_zero 2 hP)
  have := (mul_eq_zero.mp h0).resolve_left (by
    intro hz; exact hne (by linear_combination hz))
  exact sub_eq_zero.mp this

/-! ## §2 定理 R（還元）の算術 -/

/-- `F = h·C` と `h(ξ) = 0` なら `F′(ξ) = h′(ξ)·C(ξ)`（定理 R の留数の段）。 -/
theorem deriv_eval_of_factor {R : Type*} [CommRing R] (F h C : R[X]) (ξ : R)
    (hF : F = h * C) (hξ : h.eval ξ = 0) :
    (derivative F).eval ξ = (derivative h).eval ξ * C.eval ξ := by
  subst hF
  simp [derivative_mul, hξ]

/-- (R′) の同値：`h′(ξ)·C(ξ) = −2W` のとき、`C(ξ) = 2A²·d ⟺ W + A²·h′(ξ)·d = 0`。 -/
theorem residue_iff {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    (h₁ C₀ A d W : K) (hh : h₁ ≠ 0) (hC : h₁ * C₀ = -2 * W) :
    C₀ = 2 * A ^ 2 * d ↔ W + A ^ 2 * h₁ * d = 0 := by
  constructor
  · intro hCd
    have : h₁ * (2 * A ^ 2 * d) = -2 * W := by rw [← hCd]; exact hC
    have h2 : (2 : K) * (W + A ^ 2 * h₁ * d) = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left hchar
  · intro hW
    have : h₁ * C₀ = h₁ * (2 * A ^ 2 * d) := by linear_combination hC - 2 * hW
    exact mul_left_cancel₀ hh this

/-- `M ≡ 定数 (mod p)` なら `p ∣ M′`（定理 Q の (Q-i) の帰結）。 -/
theorem const_mod_p_deriv {R : Type*} [CommRing R] (a p : R) (M T : R[X])
    (hM : M = C a + C p * T) : derivative M = C p * derivative T := by
  subst hM; simp [derivative_add, derivative_mul]

/-! ## §3 主係数・次数・重みの勘定（`p = 2n+1`） -/

/-- 主係数の相殺（補題 C）：`4n² − 1 = (2n−1)·p`。標数 `p` で `4n² ≡ 1` なので
`Φ` と `4w(h′)²` の `X^p` の係数が相殺し、`deg(Φ − 4w(h′)²) ≤ p−1`。 -/
theorem lead_cancel (n : ℤ) : 4 * n ^ 2 - 1 = (2 * n - 1) * (2 * n + 1) := by ring

/-- 定理 Q の主係数比較：`lc(K) = (p²−1)/2 = 2n²+2n` と `lc(u^n h′(x^p)) = n` の差は `n·p`。 -/
theorem lc_difference (n : ℤ) : (2 * n ^ 2 + 2 * n) - n = n * (2 * n + 1) := by ring

/-- 次数の一致：`deg_x(u^n·h′(x^p)) = 3n + p(n−1) = (p²−3)/2 = deg_x K`。 -/
theorem deg_K_eq (n : ℤ) : 3 * n + (2 * n + 1) * (n - 1) = 2 * n ^ 2 + 2 * n - 1 := by ring

/-- (L) の重みの勘定：`[X^{p−1}]Φ`・`[X^{n−1}]h`・`A·∂A` はどれも重み `2p`。 -/
theorem weight_L (p : ℤ) :
    2 * p ^ 2 - 2 * p * (p - 1) = 2 * p ∧ 2 * (p - 1) + 2 = 2 * p := by
  constructor <;> ring

/-- `(2n+1 : ZMod (2n+1)) = 0`——(Q-iv) の相殺（`(2n+1)M′/p` の項が `mod p` で消える理由）。 -/
theorem two_n_add_one_eq_zero (n : ℕ) : ((2 * n + 1 : ℕ) : ZMod (2 * n + 1)) = 0 := by
  simp

end PadicHeight

#print axioms PadicHeight.isogeny_A1
#print axioms PadicHeight.isogeny_A1_domain
#print axioms PadicHeight.isogeny_A2_core
#print axioms PadicHeight.isogeny_A2
#print axioms PadicHeight.deriv_eval_of_factor
#print axioms PadicHeight.residue_iff
#print axioms PadicHeight.const_mod_p_deriv
#print axioms PadicHeight.lead_cancel
#print axioms PadicHeight.lc_difference
#print axioms PadicHeight.deg_K_eq
#print axioms PadicHeight.weight_L
#print axioms PadicHeight.two_n_add_one_eq_zero
