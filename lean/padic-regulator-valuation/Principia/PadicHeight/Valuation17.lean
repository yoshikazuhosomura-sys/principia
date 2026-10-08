import Mathlib

/-!
# 感度の帳簿——形式群の層が高さの何桁目を動かすか

三桁目・四桁目の帳簿に現れる量 `Θ = (Φ^{p−1} − 1)/p²`（`Φ` は `p` 分多項式の分子の値）は、
点を形式群の第 `j` 層のぶんだけ動かすと、`p^{j−1}` の桁から先が動く。本ファイルはその
**付値の算術**を記帳する。幾何の側の三つの入力は仮定として入る：

* `Φ(t) = φ_p(X(t))` の `t` についての差が
  `Diff = p·g·Δ + p·Δ²·B + Δ⁵·C` の形に書けること
  （`p ∣ φ_p′` という補題から一次の項に `p` が出る。`Δ⁵` は `Δ^p` を `p ≥ 5` で弱めた形）、
* `g` が単数であること（非退化性 `v_p(φ_p′(x_T)) = 1`）、
* `Φ` が単数であること。

このとき差の付値はちょうど `j + 1` で（`shift_depth_exact`）、`p − 1` 乗を取っても
付値は変わらず（`unit_pow_diff_exact`）、`p²` で割って `Θ` に直すと
**ちょうど `j − 1`**（`theta_sensitivity_exact`）。

決定の側（`theta_digit_determined`）は不等式だけで足り、これが
「`min(v_p(Reg_p), 3)` を決めるのは形式群の三層である」の記帳になる
（`three_layers_determine`）。逆向きの鋭さ（層を一つ落とすと桁が変わる）は
`layer_three_moves_digit_two` である。非退化性を落とすと結論が壊れることも記帳した
（`nondegeneracy_needed`）。

`σ` 関数・Eisenstein 級数・除法多項式・形式群そのものは Lean に入っていない。
-/

namespace PadicHeight

/-! ## §1 二項展開の一次の項 -/

/-- `(A + D)^{m+1} − A^{m+1} = (m+1)·A^m·D + D²·C`。 -/
theorem pow_sub_pow_expand (A D : ℤ) : ∀ m : ℕ,
    ∃ C : ℤ, (A + D) ^ (m + 1) - A ^ (m + 1) = ((m : ℤ) + 1) * A ^ m * D + D ^ 2 * C := by
  intro m
  induction m with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨A * C + ((n : ℤ) + 1) * A ^ n + D * C, ?_⟩
      push_cast
      linear_combination (A + D) * hC

/-! ## §2 単数の `n` 乗を取っても付値は変わらない -/

/-- `p^m ∣ D` かつ `p^(m+1) ∤ D` なら `D = p^m·d` で `p ∤ d`。 -/
theorem exists_exact_part {p D : ℤ} {m : ℕ}
    (hD : p ^ m ∣ D) (hD' : ¬ p ^ (m + 1) ∣ D) : ∃ d : ℤ, D = p ^ m * d ∧ ¬ p ∣ d := by
  obtain ⟨d, rfl⟩ := hD
  refine ⟨d, rfl, ?_⟩
  intro hpd
  exact hD' (by obtain ⟨e, rfl⟩ := hpd; exact ⟨e, by ring⟩)

/-- **単数の `n` 乗の差の付値。**`A` が単数・`n` が `p` と素・`D` の付値がちょうど `m ≥ 1` なら、
`(A+D)^n − A^n` の付値もちょうど `m`。 -/
theorem unit_pow_diff_exact {p A D : ℤ} {m n : ℕ} (hp : Prime p)
    (hA : ¬ p ∣ A) (hn : ¬ p ∣ ((n : ℤ) + 1)) (hm : 1 ≤ m)
    (hD : p ^ m ∣ D) (hD' : ¬ p ^ (m + 1) ∣ D) :
    p ^ m ∣ (A + D) ^ (n + 1) - A ^ (n + 1) ∧
      ¬ p ^ (m + 1) ∣ (A + D) ^ (n + 1) - A ^ (n + 1) := by
  obtain ⟨d, hd, hdp⟩ := exists_exact_part hD hD'
  obtain ⟨C, hC⟩ := pow_sub_pow_expand A D n
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk hd
  have hne : (p : ℤ) ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  refine ⟨?_, ?_⟩
  · rw [hC]
    exact dvd_add ⟨((n : ℤ) + 1) * A ^ n * d, by ring⟩ ⟨p ^ (k + 1) * d ^ 2 * C, by ring⟩
  · intro hcon
    rw [hC] at hcon
    obtain ⟨e, he⟩ := hcon
    have h4 : ((n : ℤ) + 1) * A ^ n * d = p * (e - p ^ k * d ^ 2 * C) := by
      apply mul_left_cancel₀ hne
      linear_combination he
    rcases hp.dvd_mul.mp (⟨_, h4⟩ : p ∣ ((n : ℤ) + 1) * A ^ n * d) with h6 | h6
    · rcases hp.dvd_mul.mp h6 with h7 | h7
      · exact hn h7
      · exact hA (hp.dvd_of_dvd_pow h7)
    · exact hdp h6

/-! ## §3 深さの補題——差の付値はちょうど `j + 1` -/

/-- **深さの補題（鋭い形）。**`Diff = p·g·Δ + p·Δ²·B + Δ⁵·C`・`Δ = p^j·d`・
`p ∤ g`・`p ∤ d`・`j ≥ 1` なら、`Diff` の付値はちょうど `j + 1`。 -/
theorem shift_depth_exact {p g B C d Diff : ℤ} {j : ℕ} (hp : Prime p) (hj : 1 ≤ j)
    (hg : ¬ p ∣ g) (hd : ¬ p ∣ d)
    (hDiff : Diff = p * g * (p ^ j * d) + p * (p ^ j * d) ^ 2 * B + (p ^ j * d) ^ 5 * C) :
    p ^ (j + 1) ∣ Diff ∧ ¬ p ^ (j + 2) ∣ Diff := by
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  subst hi
  have key : Diff = p ^ (i + 2) * (g * d)
      + p ^ (i + 3) * (p ^ i * d ^ 2 * B + p ^ (4 * i + 2) * d ^ 5 * C) := by
    rw [hDiff]; ring
  refine ⟨?_, ?_⟩
  · rw [key]
    exact dvd_add ⟨g * d, by ring⟩ ⟨p * (p ^ i * d ^ 2 * B + p ^ (4 * i + 2) * d ^ 5 * C), by ring⟩
  · intro hcon
    rw [key] at hcon
    obtain ⟨e, he⟩ := hcon
    have hne : (p : ℤ) ^ (i + 2) ≠ 0 := pow_ne_zero _ hp.ne_zero
    have h4 : g * d = p * (e - (p ^ i * d ^ 2 * B + p ^ (4 * i + 2) * d ^ 5 * C)) := by
      apply mul_left_cancel₀ hne
      linear_combination he
    rcases hp.dvd_mul.mp (⟨_, h4⟩ : p ∣ g * d) with h5 | h5
    · exact hg h5
    · exact hd h5

/-- **決定の側**（不等式だけ）。`Δ` が `p^j` で割れれば（`j ≥ 1`）`Diff` は `p^(j+1)` で割れる。 -/
theorem shift_depth_dvd {p g B C D Diff : ℤ} {j : ℕ} (hj : 1 ≤ j) (hD : p ^ j ∣ D)
    (hDiff : Diff = p * g * D + p * D ^ 2 * B + D ^ 5 * C) :
    p ^ (j + 1) ∣ Diff := by
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  subst hi
  obtain ⟨d, rfl⟩ := hD
  rw [hDiff]
  refine dvd_add (dvd_add ⟨g * d, by ring⟩ ⟨p ^ (i + 1) * d ^ 2 * B, by ring⟩)
    ⟨p ^ (4 * i + 3) * d ^ 5 * C, by ring⟩

/-! ## §4 `Θ` の桁 -/

/-- `p²` で割ると付値は 2 だけ下がる。`Θ = (Φ^{p−1} − 1)/p²` の差に使う。 -/
theorem quotient_by_p_sq {p X Y : ℤ} {j : ℕ} (hp : p ≠ 0) (hj : 1 ≤ j)
    (hXY : X = p ^ 2 * Y) (h1 : p ^ (j + 1) ∣ X) (h2 : ¬ p ^ (j + 2) ∣ X) :
    p ^ (j - 1) ∣ Y ∧ ¬ p ^ j ∣ Y := by
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  subst hi
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := h1
    refine ⟨c, ?_⟩
    have hne : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hp
    apply mul_left_cancel₀ hne
    rw [← hXY, hc]; ring
  · intro hcon
    obtain ⟨c, hc⟩ := hcon
    exact h2 ⟨c, by rw [hXY, hc]; ring⟩

/-- **感度定理の算術。**`Φ` が単数・`ΔΦ = p·g·Δ + p·Δ²·B + Δ⁵·C`・`Δ = p^j·d`
（`p ∤ g`・`p ∤ d`・`j ≥ 1`）なら、`Θ = (Φ^{p−1} − 1)/p²` の差の付値は**ちょうど `j − 1`**。 -/
theorem theta_sensitivity_exact {p A g B C d Diff Y : ℤ} {j n : ℕ} (hp : Prime p)
    (hj : 1 ≤ j) (hA : ¬ p ∣ A) (hn : ¬ p ∣ ((n : ℤ) + 1)) (hg : ¬ p ∣ g) (hd : ¬ p ∣ d)
    (hDiff : Diff = p * g * (p ^ j * d) + p * (p ^ j * d) ^ 2 * B + (p ^ j * d) ^ 5 * C)
    (hY : (A + Diff) ^ (n + 1) - A ^ (n + 1) = p ^ 2 * Y) :
    p ^ (j - 1) ∣ Y ∧ ¬ p ^ j ∣ Y := by
  obtain ⟨h1, h2⟩ := shift_depth_exact hp hj hg hd hDiff
  obtain ⟨h3, h4⟩ := unit_pow_diff_exact hp hA hn (by omega : 1 ≤ j + 1) h1 h2
  exact quotient_by_p_sq hp.ne_zero hj hY h3 h4

/-- **決定の側。**`Δ` が `p^j` で割れれば `Θ` は `mod p^(j−1)` で動かない。 -/
theorem theta_digit_determined {p A g B C D Diff Y : ℤ} {j n : ℕ} (hp : Prime p) (hj : 1 ≤ j)
    (hD : p ^ j ∣ D)
    (hDiff : Diff = p * g * D + p * D ^ 2 * B + D ^ 5 * C)
    (hY : (A + Diff) ^ (n + 1) - A ^ (n + 1) = p ^ 2 * Y) :
    p ^ (j - 1) ∣ Y := by
  obtain ⟨C', hC'⟩ := pow_sub_pow_expand A Diff n
  have h1 : p ^ (j + 1) ∣ Diff := shift_depth_dvd hj hD hDiff
  have h2 : p ^ (j + 1) ∣ (A + Diff) ^ (n + 1) - A ^ (n + 1) := by
    rw [hC']
    refine dvd_add (h1.mul_left _) ?_
    exact (h1.trans (dvd_pow_self Diff two_ne_zero)).mul_right C'
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  subst hi
  simp only [Nat.add_sub_cancel]
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, ?_⟩
  have hne : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  apply mul_left_cancel₀ hne
  rw [← hY, hc]; ring

/-- **三層で `mod p²` が決まる。**`Δ` が `p³` で割れれば `Θ` は `mod p²` で動かない
——`min(v_p(Reg_p), 3)` が `(γ, γ₂, γ₃)` だけで決まることの記帳。 -/
theorem three_layers_determine {p A g B C D Diff Y : ℤ} {n : ℕ} (hp : Prime p)
    (hD : p ^ 3 ∣ D)
    (hDiff : Diff = p * g * D + p * D ^ 2 * B + D ^ 5 * C)
    (hY : (A + Diff) ^ (n + 1) - A ^ (n + 1) = p ^ 2 * Y) :
    p ^ 2 ∣ Y := by
  have h := theta_digit_determined hp (by omega : 1 ≤ 3) hD hDiff hY
  simpa using h

/-- **層を一つ足すと桁が動く。**第三層だけを動かすと `Θ` の `p²` の桁が変わる
（`p³ ∤ Y' − Y` ではなく、差の付値がちょうど 2）——三層目が要ることの記帳。 -/
theorem layer_three_moves_digit_two {p A g B C d Diff Y : ℤ} {n : ℕ} (hp : Prime p)
    (hA : ¬ p ∣ A) (hn : ¬ p ∣ ((n : ℤ) + 1)) (hg : ¬ p ∣ g) (hd : ¬ p ∣ d)
    (hDiff : Diff = p * g * (p ^ 3 * d) + p * (p ^ 3 * d) ^ 2 * B + (p ^ 3 * d) ^ 5 * C)
    (hY : (A + Diff) ^ (n + 1) - A ^ (n + 1) = p ^ 2 * Y) :
    p ^ 2 ∣ Y ∧ ¬ p ^ 3 ∣ Y := by
  have h := theta_sensitivity_exact hp (by omega : 1 ≤ 3) hA hn hg hd hDiff hY
  simpa using h

/-! ## §5 非退化性は落とせない -/

/-- 非退化性 `p ∤ g` を落とすと結論（付値がちょうど `j+1`）は壊れる。`p = 5`・`j = 1`・
`g = 5`・`d = 1`・`B = C = 0` で差は `5³` になり、`p^(j+2)` で割れてしまう。 -/
theorem nondegeneracy_needed :
    ∃ (p g d B C Diff : ℤ) (j : ℕ), Prime p ∧ 1 ≤ j ∧ p ∣ g ∧ ¬ p ∣ d ∧
      Diff = p * g * (p ^ j * d) + p * (p ^ j * d) ^ 2 * B + (p ^ j * d) ^ 5 * C ∧
      p ^ (j + 2) ∣ Diff := by
  refine ⟨5, 5, 1, 0, 0, 125, 1, by norm_num, le_refl 1, ⟨1, by ring⟩,
    by norm_num, by ring, ⟨1, by ring⟩⟩

/-- 逆に、非退化なら（同じ形で）付値はちょうど `j + 1` である——上の witness との対照。 -/
theorem nondegenerate_gives_exact :
    (5 : ℤ) ^ 2 ∣ (25 : ℤ) ∧ ¬ (5 : ℤ) ^ 3 ∣ (25 : ℤ) := by
  refine ⟨⟨1, by ring⟩, ?_⟩
  intro h
  obtain ⟨c, hc⟩ := h
  omega

/-! ## §6 感度から言明 G″ へ——桁と層の対応 -/

/-- **桁と層の対応（両向き）。**第 `j` 層を動かすと `Θ` の `p^(j−1)` の桁から先だけが動く。
決定（`p^(j−1)` までは不変）と鋭さ（`p^(j−1)` の桁はちょうど動く）を一つにまとめた形。 -/
theorem layer_digit_correspondence {p A g B C d Diff Y : ℤ} {j n : ℕ} (hp : Prime p)
    (hj : 1 ≤ j) (hA : ¬ p ∣ A) (hn : ¬ p ∣ ((n : ℤ) + 1)) (hg : ¬ p ∣ g) (hd : ¬ p ∣ d)
    (hDiff : Diff = p * g * (p ^ j * d) + p * (p ^ j * d) ^ 2 * B + (p ^ j * d) ^ 5 * C)
    (hY : (A + Diff) ^ (n + 1) - A ^ (n + 1) = p ^ 2 * Y) :
    (∀ k : ℕ, k ≤ j - 1 → p ^ k ∣ Y) ∧ ¬ p ^ j ∣ Y := by
  obtain ⟨h1, h2⟩ := theta_sensitivity_exact hp hj hA hn hg hd hDiff hY
  exact ⟨fun k hk => (pow_dvd_pow p hk).trans h1, h2⟩

end PadicHeight

#print axioms PadicHeight.pow_sub_pow_expand
#print axioms PadicHeight.exists_exact_part
#print axioms PadicHeight.unit_pow_diff_exact
#print axioms PadicHeight.shift_depth_exact
#print axioms PadicHeight.shift_depth_dvd
#print axioms PadicHeight.quotient_by_p_sq
#print axioms PadicHeight.theta_sensitivity_exact
#print axioms PadicHeight.theta_digit_determined
#print axioms PadicHeight.three_layers_determine
#print axioms PadicHeight.layer_three_moves_digit_two
#print axioms PadicHeight.nondegeneracy_needed
#print axioms PadicHeight.nondegenerate_gives_exact
#print axioms PadicHeight.layer_digit_correspondence
