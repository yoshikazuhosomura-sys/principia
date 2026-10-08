import Mathlib

/-!
# 帳簿の局所項が消える枡（CM）——`c = 0` のときの二つの速さ

草稿 `PAPER-padic-regulator-valuation` の §3.11 の帳簿

`n²h_p(P) = (1/(1−p))·[p^{−2}log(1+p²Θ) + 2log(1+pF)] + p^{−2}·ℒ(z(P″))`

で、`ℒ(z) = μ₂z² + μ₄z⁴ + μ₆z⁶ + ⋯` の第一係数は `μ₂ = −c`（`c = (b₂ − E₂)/12`）である。
`j` 不変量 0 の曲線（`Q(√−3)` による虚数乗法）では `E₂` が消えて **`c = 0`** になり、
さらにその極小模型では `b₂ = b₄ = 0` ゆえ `μ₄ = −b₄/12 = 0` でもある。つまり `ℒ` の先頭は
`μ₆z⁶` に落ちる。このファイルは**そのとき何が変わり何が変わらないか**の算術だけを集める。

* `ledger_lags_any_m`・`cm_lags_ten` : 帳簿の局所項の遅れ。`m` が何であれ二桁以上、
  先頭が `m = 3` なら十桁。**`c = 0` は遅れを増やすだけで、最小性の論法を壊さない。**
* `m1_leads_iff`・`m1_leads_of_unit_c` : `m = 1` の項が先頭になる条件
  `v_p(c) < 2·min(e,1+j) + v_p(μ₄)`。`p ∤ c` なら自動的に成り立つ。
* `boundary_cancel_m1`・`boundary_cancel_pow`・`boundary_all_but_one_p7` : 境界の行（`1+j = e`）の
  打ち消しの規準。`m = 1` では `2u + 1 = 0`（草稿の `u ≡ −1/2`）、一般の `m` では
  `(1 + u⁻¹)^{2m} = 1`。`(p−1) ∣ 2m` のときは `u ≠ −1` の**すべて**で打ち消す。
* `cm_prime_mod_three`・`cm_not_thirteen` : `j = 0` の曲線が `a_p = 1` になる `p` は
  `4p = 1 + 3f²` を満たすものだけ。ゆえに `p ≡ 1 (mod 3)` で、`5 ≤ p ≤ 19` では `p = 7, 19` のみ。
* `cm_ledger_invisible_before_eleventh`・`cm_no_local_invariant_before_eleventh` :
  `e = 2` の CM の枡では `p^{−2}ℒ` の付値は 10 で、**第十一桁より前には局所不変量が一つも要らない**。
* `layer_is_needed_cm` : 速い項が `p^{k−1}·u`・遅い項が `p^k` の倍数なら、二つのうち高々一つが
  `mod p^k` で消える（`c = 0` でも同じ形で使える割り切れの補題）。

形式群・形式対数・`p` 進 `σ` 関数・除法多項式は Mathlib に無いので、速さそのもの
（`v_p(ΔΘ) = j − 1`・`v_p(Δz) = 1 + j`）は仮定であって、ここで証明するものではない。
-/

namespace PadicHeightCM

/-! ## §1 帳簿の局所項の遅れ（`m` に一様・`c = 0` でも成り立つ） -/

/-- `Δ(z^{2m})` の付値は `1 + j` に `(2m−1)·min(e, 1+j)` を足したものなので、
`p^{−2}` を掛けたあとでも `Θ` 側の `j − 1` より**二桁以上**深い。
`e ≥ 2`・`j ≥ 1`・`m ≥ 1` だけを使い、`v_p(μ_{2m}) ≥ 0` も `c ≠ 0` も使わない。 -/
theorem ledger_lags_any_m {e j m : ℕ} (he : 2 ≤ e) (hj : 1 ≤ j) (hm : 1 ≤ m) :
    (j - 1) + 2 ≤ (1 + j) + (2 * m - 1) * min e (1 + j) - 2 := by
  have h2 : 2 ≤ min e (1 + j) := le_min he (by omega)
  have h1 : 1 ≤ 2 * m - 1 := by omega
  have : 1 * min e (1 + j) ≤ (2 * m - 1) * min e (1 + j) :=
    Nat.mul_le_mul_right _ h1
  omega

/-- `c = 0` かつ `μ₄ = 0` の枡（`j = 0` の CM）では先頭は `m = 3` の項で、
遅れは二桁ではなく**十桁**になる。 -/
theorem cm_lags_ten {e j : ℕ} (he : 2 ≤ e) (hj : 1 ≤ j) :
    (j - 1) + 10 ≤ (1 + j) + 5 * min e (1 + j) - 2 := by
  have h2 : 2 ≤ min e (1 + j) := le_min he (by omega)
  have : 5 * 2 ≤ 5 * min e (1 + j) := Nat.mul_le_mul_left 5 h2
  omega

/-! ## §2 どの項が先頭か（命題 20 (iii) に要る仮定） -/

/-- `m = 1` の項（付値 `v_p(c) + min(e,1+j) + (1+j)`）が `m = 2` の項
（付値 `v_p(μ₄) + (1+j) + 3·min(e,1+j)`）より浅いことと、
`v_p(c) < 2·min(e,1+j) + v_p(μ₄)` は同値である。 -/
theorem m1_leads_iff {e j vc v4 : ℕ} :
    vc + min e (1 + j) + (1 + j) < v4 + (1 + j) + 3 * min e (1 + j) ↔
      vc < 2 * min e (1 + j) + v4 := by
  omega

/-- `p ∤ c`（`v_p(c) = 0`）なら、`e ≥ 2`・`j ≥ 1` のもとでその条件は自動的に成り立つ。
逆に `c = 0` では `m = 1` の項が無いので、草稿の等号の主張には仮定が要る。 -/
theorem m1_leads_of_unit_c {e j v4 : ℕ} (he : 2 ≤ e) (hj : 1 ≤ j) :
    0 < 2 * min e (1 + j) + v4 := by
  have h2 : 2 ≤ min e (1 + j) := le_min he (by omega)
  omega

/-! ## §3 境界の行（`1 + j = e`）の打ち消しの規準 -/

/-- `w := Δz/z` は境界の行で単数で、`w ≡ u⁻¹ (mod p)`。`m = 1` の項の先頭が打ち消されるのは
`(1 + w)² = 1`、すなわち `2u + 1 = 0` のときちょうど（草稿の `u ≡ −1/2 (mod p)`）。 -/
theorem boundary_cancel_m1 {p : ℕ} [Fact p.Prime] {u : ZMod p} (hu : u ≠ 0) :
    (1 + u⁻¹) ^ 2 = 1 ↔ 2 * u + 1 = 0 := by
  have hu' : u⁻¹ ≠ 0 := inv_ne_zero hu
  have key : (1 + u⁻¹) ^ 2 - 1 = (u⁻¹) ^ 2 * (2 * u + 1) := by
    field_simp
    ring
  constructor
  · intro h
    have h0 : (u⁻¹) ^ 2 * (2 * u + 1) = 0 := by rw [← key, h, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rw [pow_two] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2 <;> exact absurd h2 hu'
    · exact h1
  · intro h
    have h0 : (1 + u⁻¹) ^ 2 - 1 = 0 := by rw [key, h, mul_zero]
    exact sub_eq_zero.mp h0

/-- 一般の `m`：先頭が打ち消されるのは `(1 + u⁻¹)^{2m} = 1` のときで、
これは `(u+1)^{2m} = u^{2m}` と同じ条件である。 -/
theorem boundary_cancel_pow {p m : ℕ} [Fact p.Prime] {u : ZMod p} (hu : u ≠ 0) :
    (1 + u⁻¹) ^ (2 * m) = 1 ↔ (u + 1) ^ (2 * m) = u ^ (2 * m) := by
  have hun : u ^ (2 * m) ≠ 0 := pow_ne_zero _ hu
  have h1 : 1 + u⁻¹ = (u + 1) * u⁻¹ := by field_simp
  rw [h1, mul_pow, inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq hun]

/-- `(p − 1) ∣ 2m` のときは、`u ≠ 0` と `u + 1 ≠ 0` のすべての `u` で打ち消す（Fermat）。 -/
theorem boundary_cancel_of_card {p m : ℕ} [Fact p.Prime] {u : ZMod p} (hu : u ≠ 0)
    (hu1 : u + 1 ≠ 0) (hdvd : (p - 1) ∣ 2 * m) : (1 + u⁻¹) ^ (2 * m) = 1 := by
  have hu' : u⁻¹ ≠ 0 := inv_ne_zero hu
  have h1 : 1 + u⁻¹ = (u + 1) * u⁻¹ := by field_simp
  have ha : 1 + u⁻¹ ≠ 0 := by rw [h1]; exact mul_ne_zero hu1 hu'
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow]

/-- `p = 7`・`2m = 6 = p − 1` の場合を数で：`u = −1` 以外のすべてで打ち消し、
`u = −1` では打ち消さない。CM の枡（`c = 0`・`μ₄ = 0`）の先頭は `m = 3` の項なので、
境界の行の規準は `m = 1` の `u ≡ −1/2` ではなく**この形**になる。 -/
theorem boundary_p7_m3 : ∀ u : ZMod 7, u ≠ 0 → u + 1 ≠ 0 → (1 + u⁻¹) ^ 6 = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro u hu hu1
  simpa using boundary_cancel_of_card (p := 7) (m := 3) hu hu1 (by norm_num)

/-- 例外の枡：`u = −1 = 6` では `1 + u⁻¹ = 0` なので打ち消しは起こらない。 -/
theorem boundary_p7_exception : (1 + (-1 : ZMod 7)⁻¹) ^ 6 = 0 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [inv_neg_one, add_neg_cancel, zero_pow (by norm_num)]

/-- `p = 7` では `m = 1` の規準（`2u + 1 = 0`、すなわち `u = 3`）と
`m = 3` の例外（`u = 6`）は別の剰余である。 -/
theorem boundary_m1_vs_m3_p7 : (2 * (3 : ZMod 7) + 1 = 0) ∧ ((3 : ZMod 7) ≠ -1) := by
  refine ⟨by decide, by decide⟩


/-! ## §4 `j = 0` の曲線が異常になれる素数 -/

/-- `Q(√−3)` による虚数乗法をもつ曲線の `p` での跡 `a` は `a² − 4p = −3f²` を満たす。
`a = 1`（異常＝`#E(F_p) = p`）なら `4p = 1 + 3f²` で、ゆえに `p ≡ 1 (mod 3)`。 -/
theorem cm_prime_mod_three {p s : ℕ} (h : 4 * p = 1 + 3 * s) : p % 3 = 1 := by omega

/-- `p ≡ 2 (mod 3)` の素数では `j = 0` の曲線は超特異で `a_p = 0`、異常になれない。 -/
theorem cm_no_anomalous_of_mod_two {p : ℕ} (h : p % 3 = 2) : ¬ ∃ s, 4 * p = 1 + 3 * s := by
  rintro ⟨s, hs⟩
  have := cm_prime_mod_three hs
  omega

/-- `p = 7`（`f = 3`）と `p = 19`（`f = 5`）は `4p = 1 + 3f²` を満たす。 -/
theorem cm_seven_nineteen : 4 * 7 = 1 + 3 * 3 ^ 2 ∧ 4 * 19 = 1 + 3 * 5 ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

/-- `p = 13` は `p ≡ 1 (mod 3)` だが `4p − 1 = 51 = 3·17` で `17` は平方でないので、
`j = 0` の曲線は `13` で異常になれない。ゆえに `5 ≤ p ≤ 19` で CM の枡があるのは `p = 7, 19` だけ。 -/
theorem cm_not_thirteen (f : ℕ) : 4 * 13 ≠ 1 + 3 * f ^ 2 := by
  rcases Nat.lt_or_ge f 6 with h | h
  · interval_cases f <;> norm_num
  · have h1 : 3 * 6 ^ 2 ≤ 3 * f ^ 2 :=
      Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left h 2)
    omega

/-! ## §5 CM の枡では第十一桁より前に局所不変量が要らない -/

/-- `c = 0`・`μ₄ = 0` で `e = 2` の枡では `p^{−2}ℒ` の付値は `6e − 2 = 10`、
初めて見えるのは**第十一桁**である。 -/
theorem cm_ledger_invisible_before_eleventh : (6 * 2 - 2 : ℕ) = 10 ∧ (6 * 2 - 2 : ℕ) + 1 = 11 := by
  refine ⟨by norm_num, by norm_num⟩

/-- ゆえに `k ≤ 10` では、定理 G⁽ᵏ⁾ の局所不変量の一覧 `μ₂, …, μ_{2m₀}` は**空**である
（`2me − 2 + v_p(μ_{2m}) ≤ k − 1` を満たす `m` が無い）。大域の資料は
`(χ, γ, …, γ_k)` と `F mod p^{k−1}` だけで、`2k` 本のまま。 -/
theorem cm_no_local_invariant_before_eleventh {k : ℕ} (hk : k ≤ 10) : ¬ (6 * 2 - 2 ≤ k - 1) := by
  omega

/-! ## §6 必要性の論法は `c = 0` でも同じ形で通る -/

/-- 速い項が `p^{k−1}·u`（`p ∤ u`）・遅い項が `p^k` の倍数なら、和は `p^k` で割れない。
`c = 0` は遅い項をさらに深くするだけなので、この形の仮定は保たれる。 -/
theorem layer_is_needed_cm {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {u y a b : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (hy : (p : ℤ) ^ k ∣ y)
    (hab : a - b = (p : ℤ) ^ (k - 1) * u + y) :
    ¬ ((p : ℤ) ^ k ∣ a ∧ (p : ℤ) ^ k ∣ b) := by
  have hp0 : ((p : ℤ)) ^ (k - 1) ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hx : ¬ (p : ℤ) ^ k ∣ (p : ℤ) ^ (k - 1) * u := by
    intro h
    rw [show k = (k - 1) + 1 by omega, pow_succ] at h
    exact hu ((mul_dvd_mul_iff_left hp0).mp h)
  rintro ⟨ha, hb⟩
  have hd : (p : ℤ) ^ k ∣ (p : ℤ) ^ (k - 1) * u := by
    have : (p : ℤ) ^ k ∣ a - b := dvd_sub ha hb
    rw [hab] at this
    simpa using (dvd_sub this hy)
  exact hx hd

/-- CM の枡（`e = 2`・先頭が `m = 3`）での数：第 `k` 層を動かすと `Θ` は付値 `k − 1` で動き、
`p^{−2}ℒ` は付値 `k + 9` でしか動かない。差は十桁。 -/
theorem cm_gap_at_k {k : ℕ} (hk : 1 ≤ k) : (k - 1) + 10 = k + 9 := by omega

#print axioms PadicHeightCM.ledger_lags_any_m
#print axioms PadicHeightCM.cm_lags_ten
#print axioms PadicHeightCM.m1_leads_iff
#print axioms PadicHeightCM.m1_leads_of_unit_c
#print axioms PadicHeightCM.boundary_cancel_m1
#print axioms PadicHeightCM.boundary_cancel_pow
#print axioms PadicHeightCM.boundary_cancel_of_card
#print axioms PadicHeightCM.boundary_p7_m3
#print axioms PadicHeightCM.boundary_p7_exception
#print axioms PadicHeightCM.boundary_m1_vs_m3_p7
#print axioms PadicHeightCM.cm_prime_mod_three
#print axioms PadicHeightCM.cm_no_anomalous_of_mod_two
#print axioms PadicHeightCM.cm_seven_nineteen
#print axioms PadicHeightCM.cm_not_thirteen
#print axioms PadicHeightCM.cm_ledger_invisible_before_eleventh
#print axioms PadicHeightCM.cm_no_local_invariant_before_eleventh
#print axioms PadicHeightCM.layer_is_needed_cm
#print axioms PadicHeightCM.cm_gap_at_k

end PadicHeightCM
