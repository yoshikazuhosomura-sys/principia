import Mathlib

/-!
# 三桁目の帳簿——算術の段

分裂の異常素点における `p` 進高さの帳簿は、これまで二桁目まで書けていた：

  `N ≡ (1 + p)·T + 2p·Q  (mod p²)`

（`N = n²h_p(P)`・`T` は `p` 分多項式の Fermat 商の第二段・`Q` は点の分母の Fermat 商）。
三桁目は、その素朴な延長では書けない。延長を阻むのは次の三つの算術の段である。

* `1/(p − 1) ≡ −(1 + p + p²) (mod p³)`（`inv_pred_cube`・`neg_inv_pred_cube`）。
* **`Q₂` は商について加法的でない**：`u^{p−1} = 1 + p²A`・`v^{p−1} = 1 + p²B` のとき
  `(u/v)^{p−1} = 1 + p²Q` の `Q` は `A − B` ではなく `A − B + p²B(B − A) + O(p⁴)` である
  （`q2_quotient`——**恒等式**として記帳した）。`mod p²` では見えず、`mod p³` で効く。
* Weierstrass 式を `mod p⁵` に上げたときの二乗と三乗の突き合わせ（`sq_cube_step`）。
  ここで `2e = 4` の項が生き残り、形式群の `σ` の `t²` の係数（模型の正規化定数）が入る。

§2 は、三桁目の帳簿

  `N ≡ (1 + p)·p·(T₁ + 2Q) − p²Q² − p²W  (mod p³)`  （`T = p·T₁`）

が何を決めるかを記帳する。結論は **`v_p(N) ≥ 3 ⟺ p ∣ S − Q² − W`**（`T₁ + 2Q = p·S`）であり、
二桁目の三分類と合わせて `min(v_p(N), 3)` が完全に決まる（`quadrichotomy`）。
`W` は三桁目に初めて現れる量で、二桁目の帳簿からは決まらない（§3 の反例）。

幾何・`p` 進解析（`σ` 関数・除法多項式・形式群・Eisenstein 級数）は Lean に入っておらず、
本ファイルが載せるのは合同式の算術だけである。
-/

namespace PadicHeight

/-! ## §1 三桁目を阻んでいた三つの段 -/

/-- `(p − 1)(1 + p + p²) = p³ − 1`。 -/
theorem inv_pred_cube (p : ℤ) : (p - 1) * (1 + p + p ^ 2) = p ^ 3 - 1 := by ring

/-- ゆえに `−(1 + p + p²)` は `p − 1` の `mod p³` の逆元である。 -/
theorem neg_inv_pred_cube (p : ℤ) : p ^ 3 ∣ (p - 1) * (-(1 + p + p ^ 2)) - 1 :=
  ⟨-1, by ring⟩

/-- **`Q₂` の商の法則（恒等式）。**`A = B + Q + p²BQ`（すなわち
`(1 + p²B)(1 + p²Q) = 1 + p²A`）なら
`Q − (A − B + p²B(B − A)) = p⁴·B²Q`。
`mod p²` の帳簿では `Q = A − B` で足りていたが、`mod p³` では補正 `p²B(B − A)` が要る。 -/
theorem q2_quotient {p A B Q : ℤ} (h : A = B + Q + p ^ 2 * B * Q) :
    Q - (A - B + p ^ 2 * B * (B - A)) = p ^ 4 * (B ^ 2 * Q) := by
  subst h; ring

/-- 系：上の状況で `p⁴ ∣ Q − (A − B + p²B(B − A))`。 -/
theorem q2_quotient_dvd {p A B Q : ℤ} (h : A = B + Q + p ^ 2 * B * Q) :
    p ^ 4 ∣ Q - (A - B + p ^ 2 * B * (B - A)) :=
  ⟨B ^ 2 * Q, q2_quotient h⟩

/-- **二乗と三乗の突き合わせ。**`2B + p²B² ≡ 3A + 3p²A² + E (mod p³)` で `p ∣ E` なら
`8B ≡ 12A + 3p²A² + 4E (mod p³)`。
（`B ≡ 3A/2` を `mod p` で使って `p²B²` を `p²A²` に書き換える段。`8 = 2³` を掛けてあるのは
`mod p³` の中で `2` で割らずに済ませるためである。） -/
theorem sq_cube_step {p A B E : ℤ}
    (h : p ^ 3 ∣ (2 * B + p ^ 2 * B ^ 2) - (3 * A + 3 * p ^ 2 * A ^ 2 + E))
    (hE : p ∣ E) :
    p ^ 3 ∣ 8 * B - (12 * A + 3 * p ^ 2 * A ^ 2 + 4 * E) := by
  have hd : p ∣ (2 * B + p ^ 2 * B ^ 2) - (3 * A + 3 * p ^ 2 * A ^ 2 + E) :=
    dvd_trans (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)) h
  have h1 : p ∣ 2 * B - 3 * A := by
    have e : 2 * B - 3 * A =
        ((2 * B + p ^ 2 * B ^ 2) - (3 * A + 3 * p ^ 2 * A ^ 2 + E))
          + p * (p * (3 * A ^ 2 - B ^ 2)) + E := by ring
    rw [e]
    exact dvd_add (dvd_add hd ⟨p * (3 * A ^ 2 - B ^ 2), rfl⟩) hE
  have h2 : p ∣ 4 * B ^ 2 - 9 * A ^ 2 := by
    obtain ⟨c, hc⟩ := h1
    refine ⟨c * (2 * B + 3 * A), ?_⟩
    have e : 4 * B ^ 2 - 9 * A ^ 2 = (2 * B - 3 * A) * (2 * B + 3 * A) := by ring
    rw [e, hc]; ring
  have h3 : p ^ 3 ∣ p ^ 2 * (4 * B ^ 2 - 9 * A ^ 2) := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [hc]; ring⟩
  have e : 8 * B - (12 * A + 3 * p ^ 2 * A ^ 2 + 4 * E) =
      4 * ((2 * B + p ^ 2 * B ^ 2) - (3 * A + 3 * p ^ 2 * A ^ 2 + E))
        - p ^ 2 * (4 * B ^ 2 - 9 * A ^ 2) := by ring
  rw [e]
  exact dvd_sub (Dvd.dvd.mul_left h 4) h3

/-- **分母の段を一桁深く。**`(1 + p + p²)` の重みを付けた分母の寄与は、`mod p⁵` では
`2p³(1 + p)F − p⁴F²` に落ちる。 -/
theorem denominator_third_digit (p F : ℤ) :
    p ^ 5 ∣ (2 * p ^ 3 * (1 + p + p ^ 2) * F - p ^ 4 * (1 + p + p ^ 2) * F ^ 2)
          - (2 * p ^ 3 * (1 + p) * F - p ^ 4 * F ^ 2) :=
  ⟨2 * F - F ^ 2 - p * F ^ 2, by ring⟩

/-! ## §2 三桁目の帳簿が決めるもの -/

section ThirdDigit

variable {p N T T₁ Q S W : ℤ}

/-- 書き換え：`T₁ + 2Q = pS` なら `p³ ∣ N − p²(S − Q² − W)`。 -/
theorem cube_dvd_sub_crit
    (h : p ^ 3 ∣ N - ((1 + p) * p * (T₁ + 2 * Q) - p ^ 2 * Q ^ 2 - p ^ 2 * W))
    (hS : T₁ + 2 * Q = p * S) :
    p ^ 3 ∣ N - p ^ 2 * (S - Q ^ 2 - W) := by
  have e : N - p ^ 2 * (S - Q ^ 2 - W)
      = (N - ((1 + p) * p * (T₁ + 2 * Q) - p ^ 2 * Q ^ 2 - p ^ 2 * W)) + p ^ 3 * S := by
    rw [hS]; ring
  rw [e]
  exact dvd_add h ⟨S, rfl⟩

/-- 肯定側：`p ∣ S − Q² − W` なら `p³ ∣ N`。 -/
theorem cube_dvd_of_crit
    (h : p ^ 3 ∣ N - ((1 + p) * p * (T₁ + 2 * Q) - p ^ 2 * Q ^ 2 - p ^ 2 * W))
    (hS : T₁ + 2 * Q = p * S) (hc : p ∣ S - Q ^ 2 - W) : p ^ 3 ∣ N := by
  have key := cube_dvd_sub_crit h hS
  obtain ⟨c, hc'⟩ := hc
  have h2 : p ^ 3 ∣ p ^ 2 * (S - Q ^ 2 - W) := by rw [hc']; exact ⟨c, by ring⟩
  have := dvd_add key h2
  simpa using this

/-- 否定側：`p ∤ S − Q² − W` なら `p³ ∤ N`。 -/
theorem not_cube_dvd_of_crit_ne (hp : Prime p)
    (h : p ^ 3 ∣ N - ((1 + p) * p * (T₁ + 2 * Q) - p ^ 2 * Q ^ 2 - p ^ 2 * W))
    (hS : T₁ + 2 * Q = p * S) (hc : ¬ p ∣ S - Q ^ 2 - W) : ¬ p ^ 3 ∣ N := by
  intro hN
  apply hc
  have key := cube_dvd_sub_crit h hS
  have h2 : p ^ 3 ∣ p ^ 2 * (S - Q ^ 2 - W) := by
    have := dvd_sub hN key
    simpa using this
  obtain ⟨c, hcc⟩ := h2
  refine ⟨c, ?_⟩
  have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have e : p ^ 2 * (S - Q ^ 2 - W) = p ^ 2 * (p * c) := by rw [hcc]; ring
  exact mul_left_cancel₀ hp0 e

/-- **三桁目の判定。**`v_p(N) ≥ 3 ⟺ p ∣ S − Q² − W`。 -/
theorem cube_dvd_iff_crit (hp : Prime p)
    (h : p ^ 3 ∣ N - ((1 + p) * p * (T₁ + 2 * Q) - p ^ 2 * Q ^ 2 - p ^ 2 * W))
    (hS : T₁ + 2 * Q = p * S) : p ^ 3 ∣ N ↔ p ∣ S - Q ^ 2 - W :=
  ⟨fun hN => by
      by_contra hc
      exact not_cube_dvd_of_crit_ne hp h hS hc hN,
   fun hc => cube_dvd_of_crit h hS hc⟩

/-- 二桁目の帳簿（`mod p²`）と三桁目の帳簿（`mod p³`・`T = pT₁` の枝）を合わせると
`min(v_p(N), 3)` が完全に決まる。 -/
theorem quadrichotomy (hp : Prime p)
    (h2 : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q))
    (h3 : ∀ T₁ : ℤ, T = p * T₁ →
      p ^ 3 ∣ N - ((1 + p) * p * (T₁ + 2 * Q) - p ^ 2 * Q ^ 2 - p ^ 2 * W)) :
    (¬ p ∣ T → ¬ p ∣ N) ∧
    (∀ T₁ : ℤ, T = p * T₁ →
      (¬ p ∣ T₁ + 2 * Q → p ∣ N ∧ ¬ p ^ 2 ∣ N) ∧
      (∀ S : ℤ, T₁ + 2 * Q = p * S →
        (¬ p ∣ S - Q ^ 2 - W → p ^ 2 ∣ N ∧ ¬ p ^ 3 ∣ N) ∧
        (p ∣ S - Q ^ 2 - W → p ^ 3 ∣ N))) := by
  constructor
  · intro hT hN
    apply hT
    have h1 : p ∣ N - ((1 + p) * T + 2 * p * Q) :=
      dvd_trans (dvd_pow_self p two_ne_zero) h2
    have hNT : p ∣ N - T := by
      have e : N - T = (N - ((1 + p) * T + 2 * p * Q)) + p * (T + 2 * Q) := by ring
      rw [e]; exact dvd_add h1 ⟨T + 2 * Q, rfl⟩
    have := dvd_sub hN hNT
    simpa using this
  · intro T₁ hT
    have key2 : p ^ 2 ∣ N - p * (T₁ + 2 * Q) := by
      have e : N - p * (T₁ + 2 * Q) = (N - ((1 + p) * T + 2 * p * Q)) + p ^ 2 * T₁ := by
        rw [hT]; ring
      rw [e]; exact dvd_add h2 ⟨T₁, rfl⟩
    refine ⟨?_, ?_⟩
    · intro hcrit
      have h1 : p ∣ N - p * (T₁ + 2 * Q) := dvd_trans (dvd_pow_self p two_ne_zero) key2
      refine ⟨?_, ?_⟩
      · have := dvd_add h1 (⟨T₁ + 2 * Q, rfl⟩ : p ∣ p * (T₁ + 2 * Q))
        simpa using this
      · intro hN
        apply hcrit
        have hd : p ^ 2 ∣ p * (T₁ + 2 * Q) := by
          have := dvd_sub hN key2
          simpa using this
        obtain ⟨c, hc⟩ := hd
        refine ⟨c, ?_⟩
        have e : p * (T₁ + 2 * Q) = p * (p * c) := by rw [hc]; ring
        exact mul_left_cancel₀ hp.ne_zero e
    · intro S hS
      have hthird := h3 T₁ hT
      refine ⟨?_, ?_⟩
      · intro hc
        refine ⟨?_, not_cube_dvd_of_crit_ne hp hthird hS hc⟩
        have hd : p ^ 2 ∣ p * (T₁ + 2 * Q) := by rw [hS]; exact ⟨S, by ring⟩
        have := dvd_add key2 hd
        simpa using this
      · intro hc
        exact cube_dvd_of_crit hthird hS hc

end ThirdDigit

/-! ## §3 三桁目は二桁目からは決まらない・四分類の境目 -/

/-- 二桁目の帳簿が同じ（`T = Q = 0`）でも、`v_p(N)` の `2` と `3` は分かれる。
三桁目の量 `W` が要る理由の最小の見取り図。 -/
theorem exists_same_second_diff_third (p : ℤ) :
    ∃ N N' : ℤ, p ^ 2 ∣ N - ((1 + p) * 0 + 2 * p * 0) ∧
      p ^ 2 ∣ N' - ((1 + p) * 0 + 2 * p * 0) ∧ N = p ^ 2 ∧ N' = p ^ 3 := by
  refine ⟨p ^ 2, p ^ 3, ?_, ?_, rfl, rfl⟩
  · simp
  · have : p ^ 2 ∣ p ^ 3 := ⟨p, by ring⟩
    simpa using this

/-- 四分類の境目：`min(·, 3)` が違う ⟺ 付値が違い、かつ小さい方が 2 以下。 -/
theorem min_three_ne_iff {m n : ℕ} : min m 3 ≠ min n 3 ↔ (m ≠ n ∧ min m n ≤ 2) := by
  omega

/-- 三桁目まで見ても、両方が 3 以上の事例は分けられない。 -/
theorem min_three_eq_of_three_le {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    min m 3 = min n 3 := by omega

end PadicHeight

#print axioms PadicHeight.inv_pred_cube
#print axioms PadicHeight.neg_inv_pred_cube
#print axioms PadicHeight.q2_quotient
#print axioms PadicHeight.q2_quotient_dvd
#print axioms PadicHeight.sq_cube_step
#print axioms PadicHeight.denominator_third_digit
#print axioms PadicHeight.cube_dvd_sub_crit
#print axioms PadicHeight.cube_dvd_of_crit
#print axioms PadicHeight.not_cube_dvd_of_crit_ne
#print axioms PadicHeight.cube_dvd_iff_crit
#print axioms PadicHeight.quadrichotomy
#print axioms PadicHeight.exists_same_second_diff_third
#print axioms PadicHeight.min_three_ne_iff
#print axioms PadicHeight.min_three_eq_of_three_le
