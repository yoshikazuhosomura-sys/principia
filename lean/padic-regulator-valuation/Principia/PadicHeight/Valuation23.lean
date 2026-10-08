import Mathlib

/-!
# `Λ(z) = log(x σ_p²)` の係数の恒等式と、桁の深さの算術

草稿（`PAPER-padic-regulator-valuation`）の §3.11・§4 冒頭の帳簿を「桁を切る前の形」で
読み直したときに出てくる算術だけを集める。帳簿は

`n²h_p(P) = (1/(1−p))·[p^{−2}log(1+p²Θ) + 2log(1+pF)] + p^{−2}·Λ(z(P″))`,
`Λ(z) = log(x(P″)·σ_p(t(P″))²)`

の形に閉じる。`Λ` は形式対数 `z` の偶級数 `Λ(z) = μ₂z² + μ₄z⁴ + μ₆z⁶ + ⋯` であり、
Mazur–Tate の微分方程式 `(d/dz)²log σ_p = −(x+c)` と `x(z) + b₂/12 = ℘(z)`
（`℘ = z^{−2} + c₁z² + c₂z⁴ + ⋯`・`c₁ = c₄/240`・`c₂ = c₆/6048`）から係数が決まる。

幾何と `p` 進解析（除法多項式・形式群・形式対数・Mazur–Tate の `σ`・`p` 進高さ・Weierstrass の
`℘` 展開）は Mathlib に無いので仮定として入る。**主定理・定理 N\* は Lean の定理ではない。**

* `mu2_eq`・`mu4_eq`・`mu6_eq`・`mu6_no_b2_cube` : `μ₂ = −c`・`μ₄ = −b₄/12`・
  `μ₆ = −b₂b₄/360 − b₆/30` と、`μ₆` で `b₂³` が消えること。
* `lambda3_eq` : `t` 展開の第三係数が `−a₁c` であること（`−cz²` の再パラメータ化）。
* `lambda_depth_mono`・`lambda_depth_m2_e2`・`x_form_suffices` : `Λ` の第 `m` 項が現れる桁。
* `val_thirty`・`val_thirty_seven`・`mu6_visible_at_ten` : `μ₆` の分母の `5` が桁を一つ持ち上げる。
* `theta_depth_j5_p5`・`log_term_j10_five`・`log_term_j10_seven` : 対数の側の同じ現象。
* `layer_depth` : `e = 1 + v_p(t₁)` から `Λ` の先頭の深さが `2v_p(t₁)` であること。
-/

namespace PadicHeightStar

/-! ## §1 `Λ` の係数（`℘` の展開と Mazur–Tate の微分方程式から）

`x(z)z² = 1 + a z² + c₁z⁴ + c₂z⁶ + ⋯`（`a = −b₂/12`）と
`2log(σ_p(z)/z) = (E₂/12)z² − 2Σ_k c_k z^{2k+2}/((2k+1)(2k+2))` を足して
`Λ(z) = log(x(z)z²) + 2log(σ_p(z)/z)` の係数を読む。 -/

variable {K : Type*} [Field K] [CharZero K]

/-- `z²` の係数：`−b₂/12 + E₂/12 = −c`、`c = (b₂ − E₂)/12`。
第三桁に立つ項 `−c/(p²x(P″))` の係数がこれである。 -/
theorem mu2_eq (b₂ E₂ : K) : -(b₂ / 12) + E₂ / 12 = -((b₂ - E₂) / 12) := by
  field_simp
  ring

/-- `z⁴` の係数：`c₁ − a²/2 − c₁/6 = −b₄/12`（`a = −b₂/12`・`c₁ = (b₂²−24b₄)/240`）。
**`E₂` は入らない。** -/
theorem mu4_eq (b₂ b₄ : K) :
    (b₂ ^ 2 - 24 * b₄) / 240 - (b₂ ^ 2 / 144) / 2 - ((b₂ ^ 2 - 24 * b₄) / 240) / 6
      = -(b₄ / 12) := by
  field_simp
  ring

/-- `z⁶` の係数：`c₂ − a c₁ + a³/3 − c₂/15 = −b₂b₄/360 − b₆/30`
（`c₂ = (−b₂³ + 36b₂b₄ − 216b₆)/6048`）。ここも `E₂` は入らない。 -/
theorem mu6_eq (b₂ b₄ b₆ : K) :
    ((-b₂ ^ 3 + 36 * b₂ * b₄ - 216 * b₆) / 6048)
      - (-(b₂ / 12)) * ((b₂ ^ 2 - 24 * b₄) / 240)
      + (-(b₂ / 12)) ^ 3 / 3
      - ((-b₂ ^ 3 + 36 * b₂ * b₄ - 216 * b₆) / 6048) / 15
      = -(b₂ * b₄ / 360) - b₆ / 30 := by
  field_simp
  ring

/-- `μ₆` で `b₂³` の三つの寄与がちょうど消える：`−1/6480 + 1/2880 − 1/5184 = 0`。 -/
theorem mu6_no_b2_cube : (-1 : ℚ) / 6480 + 1 / 2880 - 1 / 5184 = 0 := by norm_num

/-- `Λ` を `t`（形式群の座標）で展開したときの第三係数は `−a₁c` である：
`z = t + (a₁/2)t² + ⋯` の再パラメータ化にすぎず、新しい局所量ではない。
ここで `g₁ = (a₁²+a₂)/3 + E₂/24`・`g₂ = (a₁³+2a₁a₂+2a₃)/4 + a₁E₂/16`。 -/
theorem lambda3_eq (a₁ a₂ a₃ E₂ : K) :
    2 * ((a₁ ^ 3 + 2 * a₁ * a₂ + 2 * a₃) / 4 + a₁ * E₂ / 16) - a₃ - a₁ * a₂
        - a₁ ^ 3 / 4 - a₁ * ((a₁ ^ 2 + a₂) / 3 + E₂ / 24)
      = -(a₁ * ((a₁ ^ 2 + 4 * a₂ - E₂) / 12)) := by
  field_simp
  ring

/-! ## §2 桁の深さ（`Λ` の側）

`p^{−2}μ_{2m}z^{2m}` の付値は `2me − 2 + v_p(μ_{2m})`（`e = v_p(z(P″)) ≥ 2`）。
`mod p^k` で見えるのは付値 `≤ k−1` の項だけである。 -/

/-- `e ≥ 2`・`m ≥ 2` なら `Λ` の第 `m` 項の深さは `≥ 6`：**第六桁には `μ₂` 以外入らない。** -/
theorem lambda_depth_mono {e m : ℕ} (he : 2 ≤ e) (hm : 2 ≤ m) : 6 ≤ 2 * m * e - 2 := by
  have h : 2 * 2 * 2 ≤ 2 * m * e := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) he
  omega

/-- `e = 2`・`m = 2` では深さちょうど 6：`μ₄ = −b₄/12` は `mod p⁶` で見えず `mod p⁷` で見える。 -/
theorem lambda_depth_m2_e2 : 2 * 2 * 2 - 2 = 6 ∧ ¬ (6 ≤ (5 : ℕ)) := by
  refine ⟨by norm_num, by norm_num⟩

/-- `z²` を `1/x(P″)` で置き換えた誤差の深さは `≥ 2e + 4 − 2 ≥ 6`：
第六桁までは `1/x(P″)` で足り、第七桁からは `z²` でなければならない。 -/
theorem x_form_suffices {e : ℕ} (he : 2 ≤ e) : 6 ≤ 2 * e + 4 - 2 := by omega

/-! ## §3 `μ_{2m}` の分母の `p` が桁を持ち上げる（`μ₆` と `p = 5`） -/

/-- `v_5(30) = 1`：`μ₆ = −b₂b₄/360 − b₆/30` は `p = 5` で `p` 進整数でない。 -/
theorem val_thirty : padicValNat 5 30 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : (30 : ℕ) = 5 * 6 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num)]
  have h5 : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
  have h6 : padicValNat 5 6 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h5, h6]

/-- `v_5(360) = 1`：もう一方の分母も `5` でちょうど一度割れる。 -/
theorem val_three_sixty : padicValNat 5 360 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : (360 : ℕ) = 5 * 72 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num)]
  have h5 : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
  have h72 : padicValNat 5 72 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h5, h72]

/-- `v_7(30) = 0`：`p = 7` では `μ₆` は `p` 進整数である。 -/
theorem val_thirty_seven : padicValNat 7 30 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

/-- `e = 2`・`m = 3` の深さは `10 + v_p(μ₆)`：`p = 5` なら 9 で **第十桁に見え**、
`p ≠ 5`（`v_p(μ₆) = 0`）なら 10 で第十桁には**見えない**。 -/
theorem mu6_visible_at_ten : 10 - 1 ≤ (9 : ℕ) ∧ ¬ ((10 : ℕ) ≤ 9) := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## §4 対数の側の同じ現象（`Θ` の第 5 項・`F` の第 10 項） -/

/-- `Θ` の第 `j` 項の深さは `2j−2−v_p(j)`。`j = 5`・`p = 5` で 7（第八桁に見える）。 -/
theorem theta_depth_j5_p5 : 2 * 5 - 2 - padicValNat 5 5 = 7 := by
  have h5 : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
  rw [h5]

/-- `j = 5`・`p = 7` では深さ 8（第八桁には見えない）。 -/
theorem theta_depth_j5_p7 : 2 * 5 - 2 - padicValNat 7 5 = 8 := by
  have h : padicValNat 7 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h]

/-- `F` の第 `j` 項の深さは `j−v_p(j)`。`j = 10`・`p = 5` で 9（第十桁に見える）。 -/
theorem log_term_j10_five : 10 - padicValNat 5 10 = 9 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : (10 : ℕ) = 5 * 2 := by norm_num
  have h10 : padicValNat 5 10 = 1 := by
    rw [h, padicValNat.mul (by norm_num) (by norm_num)]
    have h5 : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
    have h2 : padicValNat 5 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    rw [h5, h2]
  rw [h10]

/-- `j = 10`・`p = 7` では深さ 10（第十桁には見えない）。 -/
theorem log_term_j10_seven : 10 - padicValNat 7 10 = 10 := by
  have h : padicValNat 7 10 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h]

/-! ## §5 層の側（`z(P″) = p·log_E(t₁)` の付値の帰結） -/

/-- `P″ = p(P′ − T)` と形式対数の準同型性から `e = 1 + v_p(t₁)`。
したがって `Λ` の先頭の深さ `2e − 2` は `2v_p(t₁)` に等しい：
`Λ` の側の情報は層 `t₁` の桁で尽くされる。 -/
theorem layer_depth {e v : ℕ} (h : e = 1 + v) : 2 * e - 2 = 2 * v := by omega

/-- 桁が一つ深くなるごとに要る層は一つ・`F` の桁は一つ（線形にしか増えない）。 -/
theorem data_count_linear (k : ℕ) : (k + 1) - k = 1 := by omega

end PadicHeightStar

#print axioms PadicHeightStar.mu2_eq
#print axioms PadicHeightStar.mu4_eq
#print axioms PadicHeightStar.mu6_eq
#print axioms PadicHeightStar.mu6_no_b2_cube
#print axioms PadicHeightStar.lambda3_eq
#print axioms PadicHeightStar.lambda_depth_mono
#print axioms PadicHeightStar.lambda_depth_m2_e2
#print axioms PadicHeightStar.x_form_suffices
#print axioms PadicHeightStar.val_thirty
#print axioms PadicHeightStar.val_three_sixty
#print axioms PadicHeightStar.val_thirty_seven
#print axioms PadicHeightStar.mu6_visible_at_ten
#print axioms PadicHeightStar.theta_depth_j5_p5
#print axioms PadicHeightStar.theta_depth_j5_p7
#print axioms PadicHeightStar.log_term_j10_five
#print axioms PadicHeightStar.log_term_j10_seven
#print axioms PadicHeightStar.layer_depth
#print axioms PadicHeightStar.data_count_linear
