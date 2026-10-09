import Mathlib

/-!
# 四桁目の帳簿と、三桁目の量の局所性——算術の段

三桁目の帳簿

  `N ≡ (1 + p + p²)·T + 2p(1 + p)·Q − p²Q² − (p²/2)T² − p²W  (mod p³)`

には、それまでの桁に無かった量 `W` が現れる。本ファイルは二つのことを記帳する。

**§1 `W` は形式群の第一層だけで書ける。**高さ 1 の形式群では `[p](t)` の
`2 ≤ i < p` 次の係数がすべて `p` で割れる。ゆえに `t₁ = p·g + p²·u` に対し
`[p](t₁) ≡ p²·g (mod p³)` で、`W = c·T²/p⁴`（`T = [p](t₁)`）は `c·g² (mod p)` に等しい。
`W` は新しい量を要求しない——これが `w_local` である。

**§2 四桁目。**`(p − 1)(1 + p + p² + p³) = p⁴ − 1` と対数の三次項が入る。
`σ` の三次の係数と Weierstrass 式の三次の項は、どちらも付値 `3e ≥ 6` で四桁目には届かない
（`cubic_term_vanishes`）。`T·η` の二つの寄与は相殺する（`theta_eta_cancels`）。

**§3 判定。**四桁目まで下りたときの判定は `p ∣ 6U + 6(S − Q²) + 4Q³` であり
（`fourth_digit_reduction`・`quartic_dvd_iff_crit`）、三桁目までの三条件と合わせて
`min(v_p(N), 4)` が完全に決まる（`quintichotomy`）。

幾何・`p` 進解析（`σ` 関数・Eisenstein 級数 `E₂`・除法多項式・形式群そのもの）は
Lean に入っておらず、本ファイルが載せるのは合同式の算術だけである。
-/

namespace PadicHeight

/-! ## §1 三桁目の量 `W` の局所性 -/

/-- 高さ 1 の形式群では `[p](t)` の低次の係数が `p` で割れる。そのとき
`c·t^i`（`i ≥ 2`・`p ∣ t`）は `p³` で割れる——`[p](t₁)` の `mod p³` に効かない。 -/
theorem low_terms_vanish {p c t : ℤ} (hc : p ∣ c) (ht : p ∣ t) {i : ℕ} (hi : 2 ≤ i) :
    p ^ 3 ∣ c * t ^ i := by
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨t', rfl⟩ := ht
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := ⟨i - 2, by omega⟩
  refine ⟨c' * t' ^ 2 * (p * t') ^ j, ?_⟩
  rw [pow_add]
  ring

/-- **形式群の `p` 倍の第二桁。**`t₁ = p·g + p²·u` で、残差 `R` が `p³` で割れるなら
`[p](t₁) = p·t₁ + R` は `p²·g` に `mod p³` で等しい。 -/
theorem p_mult_second_digit {p g u R T t : ℤ} (ht : t = p * g + p ^ 2 * u)
    (hR : p ^ 3 ∣ R) (hT : T = p * t + R) : p ^ 3 ∣ T - p ^ 2 * g := by
  obtain ⟨r, rfl⟩ := hR
  subst ht hT
  exact ⟨u + r, by ring⟩

/-- **`W` は局所量である。**`T = p²·g + p³·u`（＝`t(pnP)/p²` の第一桁が `g`）なら
`c·T² − p⁴·(c·g²)` は `p⁵` で割れる。すなわち `W := c·T²/p⁴ ≡ c·g² (mod p)`。 -/
theorem w_local {p c g u T : ℤ} (hT : T = p ^ 2 * g + p ^ 3 * u) :
    p ^ 5 ∣ c * T ^ 2 - p ^ 4 * (c * g ^ 2) := by
  subst hT
  exact ⟨c * (2 * g * u + p * u ^ 2), by ring⟩

/-- `1/x = t²(1 + a·t + ⋯)` の補正項は `mod p` の `W` に効かない（`p² ∣ t` なら `p⁵ ∣ a·t³`）。 -/
theorem inv_x_correction {p a t : ℤ} (ht : p ^ 2 ∣ t) : p ^ 5 ∣ a * t ^ 3 := by
  obtain ⟨t', rfl⟩ := ht
  exact ⟨a * t' ^ 3 * p, by ring⟩

/-- `W ≠ 0` は `g ≠ 0` と同じ（`e = 2 ⟺ γ ≢ 0` の記帳）。 -/
theorem w_ne_zero_iff {p c g : ℤ} (hp : Prime p) (hc : ¬ p ∣ c) :
    ¬ p ∣ c * g ^ 2 ↔ ¬ p ∣ g := by
  constructor
  · intro h hg
    exact h (Dvd.dvd.mul_left (dvd_pow hg (by norm_num)) c)
  · intro hg h
    rcases (hp.dvd_mul.1 h) with h1 | h2
    · exact hc h1
    · exact hg (hp.dvd_of_dvd_pow h2)

/-! ## §2 四桁目に入る算術の段 -/

/-- `(p − 1)(1 + p + p² + p³) = p⁴ − 1`。 -/
theorem inv_pred_quartic (p : ℤ) : (p - 1) * (1 + p + p ^ 2 + p ^ 3) = p ^ 4 - 1 := by ring

/-- ゆえに `−(1 + p + p² + p³)` は `p − 1` の `mod p⁴` の逆元である。 -/
theorem neg_inv_pred_quartic (p : ℤ) :
    p ^ 4 ∣ (p - 1) * (-(1 + p + p ^ 2 + p ^ 3)) - 1 :=
  ⟨-1, by ring⟩

/-- **分母の段を `mod p⁶` へ。**`6(p − 1)L ≡ 6pQ − 3p²Q² + 2p³Q³ (mod p⁶)` なら
`6·(−2p²L) ≡ 12p³(1 + p + p²)Q − 6p⁴(1 + p)Q² + 4p⁵Q³ (mod p⁶)`。
（`L = log_p(d′)`・`Q = q_p(d′)`。`6` を掛けてあるのは `2` と `3` で割らずに済ませるため。） -/
theorem denominator_fourth_digit {p L Q : ℤ}
    (h : p ^ 6 ∣ 6 * (p - 1) * L - (6 * p * Q - 3 * p ^ 2 * Q ^ 2 + 2 * p ^ 3 * Q ^ 3)) :
    p ^ 6 ∣ 6 * (-2 * p ^ 2 * L) -
      (12 * p ^ 3 * (1 + p + p ^ 2) * Q - 6 * p ^ 4 * (1 + p) * Q ^ 2 + 4 * p ^ 5 * Q ^ 3) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨2 * p ^ 2 * (1 + p + p ^ 2 + p ^ 3) * k - 12 * L + 12 * Q
            - 6 * (1 + p) * Q ^ 2 + 4 * (1 + p + p ^ 2) * Q ^ 3, ?_⟩
  linear_combination (2 * p ^ 2 * (1 + p + p ^ 2 + p ^ 3)) * hk

/-- **`T·η` の二つの寄与は相殺する。**（一方は `Q` の `T·η` の項から、もう一方は `p⁴Q²` から。）
`p³ ∣ η` のとき差は `p⁶` で割れる。 -/
theorem theta_eta_cancels {p T H : ℤ} (hH : p ^ 3 ∣ H) :
    p ^ 6 ∣ p ^ 2 * (1 + p) * (p - 1) * T * H
          - p ^ 2 * (1 + p + p ^ 2 + p ^ 3) * (p - 1) * T * H := by
  obtain ⟨h, rfl⟩ := hH
  exact ⟨-(p * (1 + p) * (p - 1) * T * h), by ring⟩

/-- **三次の項は四桁目に届かない。**`σ` の `t³` の係数も Weierstrass 式の `a₃ωψ³` も
付値 `3e ≥ 6` で、`h_p(pnP)` の `mod p⁶` では消える。 -/
theorem cubic_term_vanishes {p g t : ℤ} (ht : p ^ 2 ∣ t) : p ^ 6 ∣ g * t ^ 3 := by
  obtain ⟨t', rfl⟩ := ht
  exact ⟨g * t' ^ 3, by ring⟩

/-! ## §3 四桁目の判定と五分類 -/

/-- **四桁目への繰り下げ。**四桁目の帳簿（`6` 倍した形）と `T₁ + 2Q = pS`・`S − Q² − W = pU`
から、`6N ≡ p³(6U + 6(S − Q²) + 4Q³) (mod p⁴)`。 -/
theorem fourth_digit_reduction {p N T₁ Q S U W : ℤ}
    (hS : T₁ + 2 * Q = p * S) (hU : S - Q ^ 2 - W = p * U)
    (hN : p ^ 4 ∣ 6 * N - (6 * p * (1 + p + p ^ 2 + p ^ 3) * T₁
            + 12 * p * (1 + p + p ^ 2) * Q - 6 * p ^ 2 * (1 + p) * Q ^ 2
            + 4 * p ^ 3 * Q ^ 3 - 3 * p ^ 4 * (1 + p) * T₁ ^ 2 - 6 * p ^ 2 * W)) :
    p ^ 4 ∣ 6 * N - p ^ 3 * (6 * U + 6 * (S - Q ^ 2) + 4 * Q ^ 3) := by
  obtain ⟨k, hk⟩ := hN
  refine ⟨k + (6 * S + 6 * T₁ - 3 * (1 + p) * T₁ ^ 2), ?_⟩
  linear_combination hk + (6 * p * (1 + p + p ^ 2)) * hS + (6 * p ^ 2) * hU

/-- **判定。**`6N ≡ p³·C (mod p⁴)` で `p ∤ 6` なら `p⁴ ∣ N ⟺ p ∣ C`。 -/
theorem quartic_dvd_iff_crit {p N C : ℤ} (hp : Prime p) (h6 : ¬ p ∣ (6 : ℤ))
    (hN : p ^ 4 ∣ 6 * N - p ^ 3 * C) : p ^ 4 ∣ N ↔ p ∣ C := by
  constructor
  · intro hdvd
    have h1 : p ^ 4 ∣ p ^ 3 * C := by
      have := dvd_sub (Dvd.dvd.mul_left hdvd 6) hN
      simpa using this
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, ?_⟩
    have e : p ^ 3 * C = p ^ 3 * (p * c) := by rw [hc]; ring
    exact mul_left_cancel₀ (pow_ne_zero 3 hp.ne_zero) e
  · intro hdvd
    obtain ⟨c, rfl⟩ := hdvd
    have h1 : p ^ 4 ∣ 6 * N := by
      have h2 : p ^ 4 ∣ p ^ 3 * (p * c) := ⟨c, by ring⟩
      have := dvd_add hN h2
      simpa using this
    exact hp.pow_dvd_of_dvd_mul_left 4 h6 h1

/-- 三桁目までの帳簿が同じでも `v_p(N)` の `3` と `4` は分かれる。 -/
theorem exists_same_third_diff_fourth (p : ℤ) :
    ∃ N N' : ℤ, p ^ 3 ∣ N ∧ p ^ 3 ∣ N' ∧ N = p ^ 3 ∧ N' = p ^ 4 := by
  exact ⟨p ^ 3, p ^ 4, dvd_rfl, ⟨p, by ring⟩, rfl, rfl⟩

/-- 五分類の境目：`min(·, 4)` が違う ⟺ 付値が違い、かつ小さい方が 3 以下。 -/
theorem min_four_ne_iff {m n : ℕ} : min m 4 ≠ min n 4 ↔ (m ≠ n ∧ min m n ≤ 3) := by
  omega

/-- 四桁目まで見ても、両方が 4 以上の事例は分けられない。 -/
theorem min_four_eq_of_four_le {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) :
    min m 4 = min n 4 := by omega

/-- **五分類。**四つの判定（一桁目・二桁目・三桁目・四桁目）が `min(v_p(N), 4)` を決める。 -/
theorem quintichotomy {m : ℕ} :
    min m 4 = if m = 0 then 0 else if m = 1 then 1 else if m = 2 then 2
              else if m = 3 then 3 else 4 := by
  split_ifs with h0 h1 h2 h3 <;> omega

end PadicHeight

#print axioms PadicHeight.low_terms_vanish
#print axioms PadicHeight.p_mult_second_digit
#print axioms PadicHeight.w_local
#print axioms PadicHeight.inv_x_correction
#print axioms PadicHeight.w_ne_zero_iff
#print axioms PadicHeight.inv_pred_quartic
#print axioms PadicHeight.neg_inv_pred_quartic
#print axioms PadicHeight.denominator_fourth_digit
#print axioms PadicHeight.theta_eta_cancels
#print axioms PadicHeight.cubic_term_vanishes
#print axioms PadicHeight.fourth_digit_reduction
#print axioms PadicHeight.quartic_dvd_iff_crit
#print axioms PadicHeight.exists_same_third_diff_fourth
#print axioms PadicHeight.min_four_ne_iff
#print axioms PadicHeight.min_four_eq_of_four_le
#print axioms PadicHeight.quintichotomy
