/-
  コラッツ／Syracuse 測度について紙の上で出した補題のうち、有限の言明を
  Lean 4 + mathlib で機械検査する。

  設定：Syracuse 分布の Z/3^j への射影を ν_j とし、u_j(y) := 2·3^(j−1)·ν_j(y)、
        d_j := min{u_j(y) : y ≢ 0 (mod 3)} とする。再帰は
          u_j(y) = 3 Σ_{a ≥ 1, 2^a y ≡ 1 (mod 3)} 2^(−a) · u_(j−1)((2^a y − 1)/3)
        で、u の値は 3 の倍数の点で 0（ν は単数に台を持つ）。
        Λ(r) := u_(j−1) ≡ 1 と置いたときの全重み。r mod 9 だけで決まり、6 つの値を取る。

  本ファイルで機械検査するのは三つ。

  【1】Λ の倍化則（訂正版）。
       Λ(2r) = 2Λ(r) − 3·1{r ≡ 2 (mod 3)} と書くと r = 5 で破れる。
       正しい形は損失項が「子が 3 の倍数のとき消える」ことを含む：
         Λ(2r) = 2Λ(r) − 3·1{r ≡ 2 (mod 3) かつ 2r ≢ 1 (mod 9)}
       （u の側の恒等式 u_j(2y) = 2u_j(y) − 3·1{y≡2 (3)}·u_(j−1)((2y−1)/3) は正しい。
         u_(j−1) が 3 の倍数で 0 になることが、Λ の側では場合分けとして表に出る。）

  【2】全部 a_i = 1 の軌道が 3 進で −1 に到達することの核。
       Σ_{i<m} 3^i · 2^(m−1−i) = 3^m − 2^m であり、ZMod (3^m) では右辺が −2^m になる。
       これが ν_m(−1) ≥ 2^(−m)、すなわち u_m(−1) ≥ (2/3)(3/2)^m の出発点である。

  【3】射影性から d_(j+1) ≤ d_j が出ることの核。
       ν_(j+1) を Z/3^j へ押し出すと ν_j になる ⟹ 各セルは 3 つの子に分かれ、和は保たれる
       ⟹ 3 点の和が S なら、そのうち少なくとも一つは S/3 以下
       ⟹ min ν_(j+1) ≤ (min ν_j)/3 ⟹ 2·3^j·min ν_(j+1) ≤ 2·3^(j−1)·min ν_j。
-/
import Mathlib.Tactic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

namespace Collatz.LambdaMeasure

/-! ### 【1】Λ の倍化則（訂正版） -/

/-- `Λ(r)`（`r` は mod 9 の類）。生きている枝の重みの和。3 の倍数の類では 0。 -/
def Lam : ℕ → ℚ
  | 1 => 20 / 21
  | 2 => 40 / 21
  | 4 => 17 / 21
  | 5 => 10 / 21
  | 7 => 5 / 21
  | 8 => 34 / 21
  | _ => 0

/-- 損失が起きる条件：`r ≡ 2 (mod 3)` かつ `2r ≢ 1 (mod 9)`。
    後半は「損失項に現れる子 `(2r−1)/3` が 3 の倍数でない」ことに当たる。 -/
def lossy (r : ℕ) : Prop := r % 3 = 2 ∧ (2 * r) % 9 ≠ 1

instance (r : ℕ) : Decidable (lossy r) := by unfold lossy; infer_instance

/-- **Λ の倍化則（訂正版）。** 単数の 6 類すべてで成立する。 -/
theorem lam_two_mul (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 5 ∨ r = 7 ∨ r = 8) :
    Lam ((2 * r) % 9) = 2 * Lam r - 3 * (if lossy r then 1 else 0) := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · norm_num [Lam, lossy]

/-- **紙の側の書き方は誤りである。** 損失条件を `r ≡ 2 (mod 3)` だけにすると `r = 5` で破れる
    （`Λ(1) = 20/21` に対して `2Λ(5) − 3 = −43/21`）。 -/
theorem lam_two_mul_naive_fails :
    Lam ((2 * 5) % 9) ≠ 2 * Lam 5 - 3 := by
  norm_num [Lam]

/-- 参考：`r = 5` では引き算が起きない（`2·5 = 10 ≡ 1 (mod 9)` なので子が 3 の倍数）。 -/
theorem lam_five : Lam ((2 * 5) % 9) = 2 * Lam 5 := by
  norm_num [Lam]

/-- 参考：`Λ` の最小値は `Λ(7) = 5/21` である（単数の 6 類の中で）。 -/
theorem lam_seven_min (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 5 ∨ r = 7 ∨ r = 8) :
    Lam 7 ≤ Lam r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Lam]

/-! ### 【2】全部 `a_i = 1` の軌道の到達点 -/

/-- 等比和 `Σ_{i<m} 3^i 2^(m−1−i) = 3^m − 2^m`。 -/
theorem allones_sum (m : ℕ) :
    (∑ i ∈ Finset.range m, (3 : ℤ) ^ i * 2 ^ (m - 1 - i)) = 3 ^ m - 2 ^ m := by
  have h := geom_sum₂_mul (3 : ℤ) 2 m
  norm_num at h
  exact h

/-- **`ZMod (3^m)` では、全部 `a_i = 1` の軌道の到達点は `−2^m` である。**
    `2` は `ZMod (3^m)` の単数なので、これは正規化して `−1` と読める
    （Syracuse の指数列が全部 1 のときの `X_m = (3/2)^m − 1 ≡ −1`）。 -/
theorem allones_zmod (m : ℕ) :
    ((∑ i ∈ Finset.range m, (3 : ℤ) ^ i * 2 ^ (m - 1 - i) : ℤ) : ZMod (3 ^ m))
      = -((2 : ZMod (3 ^ m)) ^ m) := by
  rw [allones_sum]
  have h3 : ((3 : ZMod (3 ^ m))) ^ m = 0 := by
    have h : ((3 ^ m : ℕ) : ZMod (3 ^ m)) = 0 := ZMod.natCast_self _
    push_cast at h
    exact h
  push_cast
  rw [h3]
  ring

/-- 系：`2^m` を掛け戻した形。`X_m := Σ_{i<m} 3^i (2⁻¹)^(i+1)` が `−1` であることの分母を払った版。 -/
theorem allones_zmod' (m : ℕ) :
    ((3 : ZMod (3 ^ m)) ^ m - (2 : ZMod (3 ^ m)) ^ m) = -((2 : ZMod (3 ^ m)) ^ m) := by
  have h3 : ((3 : ZMod (3 ^ m))) ^ m = 0 := by
    have h : ((3 ^ m : ℕ) : ZMod (3 ^ m)) = 0 := ZMod.natCast_self _
    push_cast at h
    exact h
  rw [h3]
  ring

/-! ### 【3】射影性 ⟹ `d` の単調非増加 -/

/-- 3 点の和が `S` なら、そのうち少なくとも一つは `S/3` 以下。 -/
theorem exists_le_third {β : Type*} (s : Finset β) (wt : β → ℝ) (S : ℝ)
    (hcard : s.card = 3) (hsum : ∑ b ∈ s, wt b = S) :
    ∃ b ∈ s, wt b ≤ S / 3 := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  refine Finset.exists_le_of_sum_le hne ?_
  rw [Finset.sum_const, hcard, hsum, nsmul_eq_mul]
  push_cast
  linarith

/-- **射影系の最小値は 3 分の 1 以下に落ちる。**
    `p : β → α` のファイバーがどれも 3 点で、その上の `wt` の和が `g` に等しいとき、
    `g` の最小を与える `a₀` のファイバーに `wt ≤ g a₀ / 3` を満たす点がある。 -/
theorem min_le_third {α β : Type*} [Fintype β] [DecidableEq α]
    (p : β → α) (wt : β → ℝ) (g : α → ℝ) (a₀ : α)
    (hcard : (Finset.univ.filter fun b => p b = a₀).card = 3)
    (hsum : ∑ b ∈ Finset.univ.filter (fun b => p b = a₀), wt b = g a₀) :
    ∃ b, p b = a₀ ∧ wt b ≤ g a₀ / 3 := by
  obtain ⟨b, hb, hle⟩ := exists_le_third _ wt (g a₀) hcard hsum
  exact ⟨b, (Finset.mem_filter.mp hb).2, hle⟩

/-- **`d_(j+1) ≤ d_j`。** `d_j = 2·3^(j−1)·min ν_j` の正規化を入れた最後の一歩。
    `b ≤ a/3` から `2·3^(j+1)·b ≤ 2·3^j·a`。 -/
theorem d_antitone (j : ℕ) (a b : ℝ) (h : b ≤ a / 3) :
    2 * (3 : ℝ) ^ (j + 1) * b ≤ 2 * (3 : ℝ) ^ j * a := by
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  rw [pow_succ]
  nlinarith

/-! ### 【4】紙の側で出した言明 -/

/-- **主枝の子の比の上界（紙の側・M4）。**
    倍化恒等式を 4 段まわすと `u_j(16z) = 16u_j(z) − 3u_(j−1)(x_4(z))` で、
    左辺は最小値 `d_j` 以上。`z = z_j` を入れると `ρ_j ≤ 5·(d_j/d_(j−1))`。
    紙の側の `ρ_j ≤ 16/3` より（`d_j ≤ d_(j−1)` の下で）常に締まっている。 -/
theorem rho_le (dj dj₁ rho : ℝ) (h1 : 0 < dj₁) (h : dj ≤ 16 * dj - 3 * (rho * dj₁)) :
    rho ≤ 5 * dj / dj₁ := by
  rw [le_div_iff₀ h1]
  linarith

/-- **6 段版（紙の側・M5）。**
    `u_j(64z) = 64u_j(z) − 12u_(j−1)(x_4(z)) − 3u_(j−1)(x_6(z))` から
    `4ρ_j + σ_j ≤ 21·(d_j/d_(j−1))`。 -/
theorem rho_sigma_le (dj dj₁ rho sigma : ℝ) (h1 : 0 < dj₁)
    (h : dj ≤ 64 * dj - 12 * (rho * dj₁) - 3 * (sigma * dj₁)) :
    4 * rho + sigma ≤ 21 * dj / dj₁ := by
  rw [le_div_iff₀ h1]
  linarith

/-- **凍結アドレスからの 3 進距離（紙の側・N2）。**
    最小点が `z ≡ −2 (mod 81)` に凍っているなら、その主枝の子 `x = (16z−1)/3` と
    前の水準の最小点 `z'`（同じく `≡ −2 (mod 81)`）の 3 進距離は**厳密に** `1/9` である。
    紙の側が 9 水準で観測した `|x_4(z_j) − z_(j−1)|_3 = 1/9` は、
    mod 81 の凍結を仮定すれば定理になる。 -/
theorem x4_dist_eq_ninth (z z' x : ℤ) (hx : 3 * x = 16 * z - 1)
    (hz : (81 : ℤ) ∣ (z + 2)) (hz' : (81 : ℤ) ∣ (z' + 2)) :
    (9 : ℤ) ∣ (x - z') ∧ ¬ ((27 : ℤ) ∣ (x - z')) := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨b, hb⟩ := hz'
  constructor
  · exact ⟨-1 + 48 * a - 9 * b, by omega⟩
  · rintro ⟨c, hc⟩
    omega

/-- 系：`z ≡ −2 (mod 81)` なら主枝の子は `x ≡ 16 (mod 27)`（紙の側の観測 `x₄ ≡ 16 (mod 81)` の
    局所解析で決まる部分。5 桁目より深いところは決まらない）。 -/
theorem x4_mod_27 (z x : ℤ) (hx : 3 * x = 16 * z - 1) (hz : (81 : ℤ) ∣ (z + 2)) :
    x % 27 = 16 := by
  obtain ⟨a, ha⟩ := hz
  omega

end Collatz.LambdaMeasure

-- 依存している公理を表示する（sorryAx が出なければ、証明は完結している）
#print axioms Collatz.LambdaMeasure.lam_two_mul
#print axioms Collatz.LambdaMeasure.lam_two_mul_naive_fails
#print axioms Collatz.LambdaMeasure.lam_five
#print axioms Collatz.LambdaMeasure.lam_seven_min
#print axioms Collatz.LambdaMeasure.allones_sum
#print axioms Collatz.LambdaMeasure.allones_zmod
#print axioms Collatz.LambdaMeasure.allones_zmod'
#print axioms Collatz.LambdaMeasure.exists_le_third
#print axioms Collatz.LambdaMeasure.min_le_third
#print axioms Collatz.LambdaMeasure.d_antitone
#print axioms Collatz.LambdaMeasure.rho_le
#print axioms Collatz.LambdaMeasure.rho_sigma_le
#print axioms Collatz.LambdaMeasure.x4_dist_eq_ninth
#print axioms Collatz.LambdaMeasure.x4_mod_27
