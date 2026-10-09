import Mathlib

/-!
# 二つの速さ ——層が桁に届く速さと、帳簿の局所項が動く速さ

帳簿（草稿 `PAPER-padic-regulator-valuation` の §3.11）は

`n²h_p(P) = (1/(1−p))·[p^{−2}log(1+p²Θ) + 2log(1+pF)] + p^{−2}·ℒ(z(P″))`

の形に閉じる。形式群の第 `j` 層を動かす（`t₁ ↦ t₁ + p^j`）と、右辺の三項はそれぞれ別の速さで動く。

* `Θ` の側：`v_p(ΔΘ) = j − 1`（層が届く速さ。`φ_p′ = p·G` と `G(x(T)) ≢ 0` から）
* `ℒ` の側：`z = p·log_E(t₁)` ゆえ `v_p(Δz) = 1 + j`、`v_p(z) = e` ゆえ
  `v_p(Δ(z²)) = e + j + 1`、`p^{−2}` を掛けて `e + j − 1`
* `F` の側：`F ↦ F + p^i` で `v_p(Δ(2log(1+pF))) = i + 1`

付値 `v` の項は `mod p^{v+1}` で初めて見えるので、桁の序数は `v + 1`。このファイルは
**この三つの速さの算術と、そこから最小性が出る形の割り切れの補題だけ**を集める。
形式群・形式対数・除法多項式・`p` 進高さ・Mazur–Tate の `σ` は Mathlib に無いので、
速さそのもの（`v_p(ΔΘ) = j − 1` など）は仮定であって、ここで証明するものではない。

* `theta_rate_digit`・`ledger_rate_digit` : 二つの速さの桁の序数
* `ledger_lags`・`ledger_lags_general`・`gap_is_e`・`uniform_in_k` : `ℒ` 側は `e ≥ 2` 桁だけ遅れる（`k` に依らない）
* `exact_pred_not_at`・`no_cancel`・`at_most_one_vanishes` : 「ちょうどの付値で動く」から
  「`mod p^k` の値が違う」へ渡す割り切れの補題
* `fermat_digit`・`fermat_digits_needed`・`data_count` : `F` の桁の本数と、資料の総数 `2k`
* `four_*`・`fifth_layer_hidden_at_four` : `k = 4` の場合（第四層は効き、第五層は効かない）
-/

namespace PadicHeightLayer

/-! ## §1 二つの速さの桁の序数 -/

/-- 第 `j` 層を動かすと `Θ` は付値ちょうど `j − 1` で動くので、**第 `j` 桁**で初めて見える。 -/
theorem theta_rate_digit {j : ℕ} (hj : 1 ≤ j) : (j - 1) + 1 = j := by omega

/-- 帳簿の局所項の側は、`p^{−2}` を掛けたあとの付値が `e + j − 1` で、
**第 `e + j` 桁**で初めて見える。 -/
theorem ledger_rate_digit {e j : ℕ} (he : 2 ≤ e) (hj : 1 ≤ j) :
    (e + j + 1) - 2 + 1 = e + j := by omega

/-- `ℒ` 側は `Θ` 側より **ちょうど `e` 桁**遅れる。 -/
theorem gap_is_e {e j : ℕ} (hj : 1 ≤ j) : (j - 1) + e = e + j - 1 := by omega

/-- `e ≥ 2` ゆえ遅れは二桁以上ある。 -/
theorem ledger_lags {e j : ℕ} (he : 2 ≤ e) (_hj : 1 ≤ j) : j + 2 ≤ e + j := by omega

/-- 一般の形（`j` が小さく `1 + j ≤ e` のときも含む）：`Δ(z²)` の付値は
`min e (1+j) + (1+j)` 以上なので、`p^{−2}` の後は `j + 1` 以上あり、
`Θ` 側の `j − 1` より**必ず二桁以上深い**。`e ≥ 2` と `j ≥ 1` だけを使う。 -/
theorem ledger_lags_general {e j : ℕ} (he : 2 ≤ e) (hj : 1 ≤ j) :
    (j - 1) + 2 ≤ min e (1 + j) + (1 + j) - 2 := by
  rcases Nat.le_total e (1 + j) with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

/-- 第 `k` 桁を読むとき、`Θ` の動きは見え（付値 `k − 1 < k`）、
`ℒ` の動きは見えない（付値 `e + k − 1 ≥ k`）。**`k` に依らない。** -/
theorem uniform_in_k {e k : ℕ} (he : 2 ≤ e) (hk : 1 ≤ k) : k - 1 < k ∧ k ≤ e + k - 1 := by
  omega

/-! ## §2 「ちょうどの付値」から「`mod p^k` が違う」へ -/

/-- 付値がちょうど `k − 1`：`p^{k−1}·u` は `p ∤ u` なら `p^k` で割れない。 -/
theorem exact_pred_not_at {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) : ¬ (p : ℤ) ^ k ∣ (p : ℤ) ^ (k - 1) * u := by
  have hp0 : ((p : ℤ)) ^ (k - 1) ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.ne_zero)
  intro h
  rw [show k = (k - 1) + 1 by omega, pow_succ] at h
  exact hu ((mul_dvd_mul_iff_left hp0).mp h)

/-- 遅い項は速い項を打ち消せない。 -/
theorem no_cancel {q x y : ℤ} (hx : ¬ q ∣ x) (hy : q ∣ y) : ¬ q ∣ (x + y) := by
  intro h
  exact hx (by simpa using dvd_sub h hy)

/-- 差が `p^k` で割れないなら、両方が `p^k` で割れることはない
（＝二つのうち高々一つが `v_p(Reg_p) ≥ k` を満たす）。 -/
theorem at_most_one_vanishes {q a b : ℤ} (h : ¬ q ∣ (a - b)) : ¬ (q ∣ a ∧ q ∣ b) := by
  intro hab
  exact h (dvd_sub hab.1 hab.2)

/-- §1 と §2 を繋いだ形：速い項が `p^{k−1}·u`（`p ∤ u`）・遅い項が `p^k` の倍数なら、
和は `p^k` で割れず、したがって二つの値のうち高々一つが `mod p^k` で消える。 -/
theorem layer_is_needed {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {u y a b : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (hy : (p : ℤ) ^ k ∣ y)
    (hab : a - b = (p : ℤ) ^ (k - 1) * u + y) :
    ¬ ((p : ℤ) ^ k ∣ a ∧ (p : ℤ) ^ k ∣ b) := by
  refine at_most_one_vanishes ?_
  rw [hab]
  exact no_cancel (exact_pred_not_at hp hk hu) hy

/-! ## §3 `F` の桁の本数と資料の総数 -/

/-- `F ↦ F + p^i` は付値 `i + 1` で動くので、**第 `i + 2` 桁**で初めて見える。 -/
theorem fermat_digit (i : ℕ) : (i + 1) + 1 = i + 2 := by omega

/-- ゆえに第 `k` 桁に届く `F` の桁は `i ≤ k − 2` の `k − 1` 本、すなわち `F mod p^{k−1}`。 -/
theorem fermat_digits_needed {i k : ℕ} (hk : 2 ≤ k) : i + 2 ≤ k ↔ i ≤ k - 2 := by omega

/-- 資料の総数：`χ` と `γ₁, …, γ_k` と `F` の `k − 1` 桁で `2k` 本。一桁につき二本ずつ増える。 -/
theorem data_count {k : ℕ} (hk : 1 ≤ k) : 1 + k + (k - 1) = 2 * k := by omega

/-- 一桁進むと資料は二本増える。 -/
theorem data_count_step {k : ℕ} (_hk : 1 ≤ k) : 2 * (k + 1) - 2 * k = 2 := by omega

/-! ## §4 `k = 4` の場合（第四層は効き、第五層は効かない） -/

/-- 第四層：`Θ` は付値ちょうど `3` で動き、第四桁で見える。 -/
theorem four_theta : (4 : ℕ) - 1 = 3 ∧ (3 : ℕ) < 4 := by omega

/-- `e = 2` のときの帳簿の局所項：`p^{−2}` の後の付値は `5`、見えるのは第六桁。
第四桁には効かない。 -/
theorem four_ledger_e2 : (2 + 4 + 1 : ℕ) - 2 = 5 ∧ (4 : ℕ) ≤ 5 ∧ (2 + 4 : ℕ) = 6 := by omega

/-- 陰性対照：第五層は `Θ` を付値 `4` で動かすので `mod p⁴` では動かない。 -/
theorem fifth_layer_hidden_at_four : (5 : ℕ) - 1 = 4 ∧ (4 : ℕ) ≤ 4 := by omega

/-- `F` の第三桁（`i = 2`）は第四桁に届き、第四桁（`i = 3`）は届かない
＝ `k = 4` に要るのは `F mod p³` まで。 -/
theorem fourth_digit_of_F : (2 + 2 : ℕ) ≤ 4 ∧ ¬ ((3 + 2 : ℕ) ≤ 4) := by omega

/-- `k = 4` の資料は八本（`χ, γ₁, γ₂, γ₃, γ₄` と `F` の三桁）。 -/
theorem four_data_count : (1 + 4 + 3 : ℕ) = 2 * 4 := by norm_num

#print axioms PadicHeightLayer.theta_rate_digit
#print axioms PadicHeightLayer.ledger_rate_digit
#print axioms PadicHeightLayer.gap_is_e
#print axioms PadicHeightLayer.ledger_lags
#print axioms PadicHeightLayer.ledger_lags_general
#print axioms PadicHeightLayer.uniform_in_k
#print axioms PadicHeightLayer.exact_pred_not_at
#print axioms PadicHeightLayer.no_cancel
#print axioms PadicHeightLayer.at_most_one_vanishes
#print axioms PadicHeightLayer.layer_is_needed
#print axioms PadicHeightLayer.fermat_digit
#print axioms PadicHeightLayer.fermat_digits_needed
#print axioms PadicHeightLayer.data_count
#print axioms PadicHeightLayer.data_count_step
#print axioms PadicHeightLayer.four_theta
#print axioms PadicHeightLayer.four_ledger_e2
#print axioms PadicHeightLayer.fifth_layer_hidden_at_four
#print axioms PadicHeightLayer.fourth_digit_of_F
#print axioms PadicHeightLayer.four_data_count

end PadicHeightLayer
