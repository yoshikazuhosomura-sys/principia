/-
  p 進高さの付値（その 29）：p 冪倍の平行移動で分母のフェルマー商の差が局所量で決まること。

  背景（形式化しない部分）：q := n²h_p は格子 Λ 上の二次形式、B はその双線型形式。
  R = p^a·Z の平行移動では D := q(P+R) − q(P) = 2p^a B(P,Z) + p^{2a} q(Z)。
  定理 N* の三項の差 D = DΘ + D𝔉 + DL（𝔉 := (2/(1−p))log(1+pF)）について、
  DΘ ≡ p^a·C(P)ψ(Z)、p^{a+1} ∣ DL。線型形式 ℓ_P := 2B(P,·) − C(P)ψ(·) は ker χ で消えるので
  ℓ_P(Z)·χ(P) = ℓ_P(P)·χ(Z)。本ファイルはこの線型代数と桁の勘定、逆向きの N₃ の多項式恒等式、
  分離の算術、反例の桁を閉じる。
-/
import Mathlib

namespace PadicTranslateLinear

/-- 核の包含 `ker g ⊆ ker f` だけから `f Z · g P = f P · g Z`（`ZMod n` 値の加法準同型）。
    `g = χ`・`f = ℓ_P` と読めば `ℓ_P = κ·χ`、`κ = ℓ_P(P)/χ(P)`。 -/
theorem ratio_of_ker_le {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (f g : G →+ ZMod n) (hker : ∀ z, g z = 0 → f z = 0) (P Z : G) :
    f Z * g P = f P * g Z := by
  have hW : g ((g P).val • Z - (g Z).val • P) = 0 := by
    simp only [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    ring
  have h := hker _ hW
  simp only [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val] at h
  linear_combination h

/-- 系：`χ Z = 0` なら `ℓ_P Z = 0`（`χ P ≠ 0` のとき）——`ker χ` 方向の平行移動では `F` の差は `0`。 -/
theorem vanish_of_chi_zero {G : Type*} [AddCommGroup G] {p : ℕ} [Fact p.Prime]
    (f g : G →+ ZMod p) (hker : ∀ z, g z = 0 → f z = 0) (P Z : G)
    (hP : g P ≠ 0) (hZ : g Z = 0) : f Z = 0 := by
  have h := ratio_of_ker_le f g hker P Z
  rw [hZ, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hP

end PadicTranslateLinear

namespace PadicTranslateDigit

/-- 二次形式の p^a 倍の平行移動：`D = p^a b + p^{2a} c`（`a ≥ 1`）なら `D ≡ p^a b (mod p^{a+1})`。 -/
theorem shift_quadratic (p b c : ℤ) {a : ℕ} (ha : 1 ≤ a) :
    p ^ a * b + p ^ (2 * a) * c ≡ p ^ a * b [ZMOD p ^ (a + 1)] := by
  have h : p ^ (2 * a) = p ^ (a + 1) * p ^ (a - 1) := by
    rw [← pow_add]; congr 1; omega
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  refine ⟨p ^ (a - 1) * c, ?_⟩
  rw [h]; ring

/-- 帳簿の桁：`D = DΘ + DF + DL`、`D ≡ p^a u`、`DΘ ≡ p^a w`、`p^{a+1} ∣ DL` なら
    `DF ≡ p^a (u − w) (mod p^{a+1})`。 -/
theorem ledger_digit {p D DT DF DL u w : ℤ} {a : ℕ}
    (hsum : D = DT + DF + DL) (hD : D ≡ p ^ a * u [ZMOD p ^ (a + 1)])
    (hT : DT ≡ p ^ a * w [ZMOD p ^ (a + 1)]) (hL : p ^ (a + 1) ∣ DL) :
    DF ≡ p ^ a * (u - w) [ZMOD p ^ (a + 1)] := by
  have hL' : DL ≡ 0 [ZMOD p ^ (a + 1)] := (Int.modEq_zero_iff_dvd).mpr hL
  have hDF : DF = D - DT - DL := by rw [hsum]; ring
  rw [hDF]
  have := (hD.sub hT).sub hL'
  rw [show p ^ a * u - p ^ a * w - 0 = p ^ a * (u - w) by ring] at this
  exact this

/-- `e = 2` の点（`ψ ≠ 0`）で `p ∣ q` なら係数 `q − Cψ/2` は消えない（計算で見た 80/80 の型）。 -/
theorem kappa_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q C ψ : ZMod p}
    (hq : q = 0) (hC : C ≠ 0) (hψ : ψ ≠ 0) : q - C * ψ * (2 : ZMod p)⁻¹ ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
    exact hp2 this
  rw [hq, zero_sub, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hC hψ) (inv_ne_zero h2)

/-- 分離：`p^k ∣ q` かつ `q' − q = p^{k−1} u`（`p ∤ u`）なら `p^k ∤ q'`。 -/
theorem separates {p q q' u : ℤ} {k : ℕ} (hp : p ≠ 0) (hk : 1 ≤ k) (hq : p ^ k ∣ q)
    (hd : q' - q = p ^ (k - 1) * u) (hu : ¬ p ∣ u) : ¬ p ^ k ∣ q' := by
  intro h
  have h1 : p ^ k ∣ q' - q := dvd_sub h hq
  have hpk : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [hd, hpk] at h1
  have hp0 : p ^ (k - 1) ≠ 0 := pow_ne_zero _ hp
  exact hu ((mul_dvd_mul_iff_left hp0).mp h1)

end PadicTranslateDigit

namespace PadicInverseLedger

/-- 逆向きの N₃（系 F₂）の多項式恒等式：`8F = 4A − 4pA + pA² + 8p²m` なら
    `64·(2(1+p)F − pF²) ≡ 64A (mod p²)`（`8F` を `X` と書いて `16(1+p)X − pX² − 64A` が `p²` で割れる）。 -/
theorem inverse_n3 (A p m : ℤ) :
    p ^ 2 ∣ 16 * (1 + p) * (4 * A - 4 * p * A + p * A ^ 2 + 8 * p ^ 2 * m)
      - p * (4 * A - 4 * p * A + p * A ^ 2 + 8 * p ^ 2 * m) ^ 2 - 64 * A := by
  refine ⟨-64 * A + 16 * A ^ 2 + 128 * m + 128 * p * m
      - 8 * A * (-4 * A + A ^ 2 + 8 * p * m) - p * (-4 * A + A ^ 2 + 8 * p * m) ^ 2, ?_⟩
  ring

/-- 平行移動の二次形式の恒等式：`q(P + p^a Z) − q(P) = p^a·2B(P,Z) + p^{2a} q(Z)`
    （`q(x) = B(x,x)`、`B` は対称双線型。ここでは係数の形 `(x + t y)ᵀ M (x + t y)` で）。 -/
theorem translate_quadratic (b11 b12 b22 x1 x2 z1 z2 t : ℤ) :
    let Q := fun (y1 y2 : ℤ) => b11 * y1 ^ 2 + 2 * b12 * y1 * y2 + b22 * y2 ^ 2
    let B := b11 * x1 * z1 + b12 * (x1 * z2 + x2 * z1) + b22 * x2 * z2
    Q (x1 + t * z1) (x2 + t * z2) - Q x1 x2 = t * (2 * B) + t ^ 2 * Q z1 z2 := by
  intro Q B
  simp only [Q, B]
  ring

/-- 第二差分：`q(P+Z) + q(P−Z) − 2q(P) = 2q(Z)`（`q(Z) ≡ 0 (mod p)` を `Θ` の一次の項から出す段）。 -/
theorem second_difference (b11 b12 b22 x1 x2 z1 z2 : ℤ) :
    let Q := fun (y1 y2 : ℤ) => b11 * y1 ^ 2 + 2 * b12 * y1 * y2 + b22 * y2 ^ 2
    Q (x1 + z1) (x2 + z2) + Q (x1 - z1) (x2 - z2) - 2 * Q x1 x2 = 2 * Q z1 z2 := by
  intro Q
  simp only [Q]
  ring

/-- 反例の桁（`4407a1`・`p = 5`・`P = −5g₁ + 6g₂`・`R = 25(g₁ − 2g₂)`）：
    `F mod 125` は `49` と `24`、差はちょうど `5²` で割れる（`dF = 2`）。 -/
theorem counterexample_digits : (25 : ℤ) ∣ 49 - 24 ∧ ¬ (125 : ℤ) ∣ 49 - 24 := by
  constructor
  · exact ⟨1, by norm_num⟩
  · decide

end PadicInverseLedger

#print axioms PadicTranslateLinear.ratio_of_ker_le
#print axioms PadicTranslateLinear.vanish_of_chi_zero
#print axioms PadicTranslateDigit.shift_quadratic
#print axioms PadicTranslateDigit.ledger_digit
#print axioms PadicTranslateDigit.kappa_ne_zero
#print axioms PadicTranslateDigit.separates
#print axioms PadicInverseLedger.inverse_n3
#print axioms PadicInverseLedger.translate_quadratic
#print axioms PadicInverseLedger.second_difference
#print axioms PadicInverseLedger.counterexample_digits
