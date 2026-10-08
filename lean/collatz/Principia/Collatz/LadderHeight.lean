/-
  Terras 模型の降下ラダーについて紙の上で出したもののうち、有限・有理の言明を
  Lean 4 + mathlib で機械検査する。

  Terras 模型では奇数 n の一段は n ↦ (3n+ε)/2^v、P(v=j) = 2^(−j) (j ≥ 1)。
  a := log₂3, u := a − 1 と置き、v の代わりに m := v − 1 ∼ Geom(1/2) on {0,1,…} を使うと
  歩幅は X = m − u、位置は W_k = M_k − k·u（M_k = Σ mᵢ は非負整数）。

  【1】Terras 模型の下で n_k/n_0 = 2^(−W_k) は厳密なマルチンゲールである。
       核は有理数の等式 Σ_{j≥1} 2^(−j)·3·2^(−j) = 1（有限版は 1 − 4^(−N)）。
       これが「裾の指数がちょうど 1」＝ P(R>λ) ≍ C/λ の指数 1 の中身である。
  【2】傾け dP̃/dP = 2^(−W) の下で m の分布は Geom(3/4) になる（規格化の有限版）。
  【3】降下ラダー高は u 以下（下向きの歩幅がちょうど一種類 −u しかないことの帰結）。
  【4】したがって整数の水準 −s を初めて下回るときの行き過ぎ O は 0 ≤ O < u を満たす。
  【5】位置 W_k の小数部は k だけで決まる（M_k が整数だから）。
       ⇒ 行き過ぎ O は frac(k·u) に等しく、C(s) の振動は log₂3 の連分数そのものになる。
  【6】巡回の方程式 2^b/3^a = Π(1 + ε/(3nᵢ)) を既知の四つの巡回で有理数として検算。
  【7】符号の共役 Syr_{+1}(−m) = −Syr_{−1}(m)。
       ⇒ ε = −1 の Syracuse 極限測度は ε = +1 のそれの y ↦ −y による像であり、
         倍化恒等式や測度の最小値まわりの定数はどれも符号に依らない
         ＝それらは 3n+1 と 3n−1 の非対称の機構になり得ない。
  【8】3n+1 側の「順位2の席」（上限 5.886、候補は 1 と 5）が空であることの核：5 は一段で 1 に落ちる。
-/
import Mathlib.Tactic
import Mathlib.Algebra.Ring.GeomSum

namespace Collatz.LadderHeight

/-! ### 【1】Terras 模型のマルチンゲール性（有限版） -/

/-- 一段の halving の分布は確率分布である（有限版）。 -/
theorem terras_prob_finite (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 / 2 : ℚ) ^ (j + 1) = 1 - (1 / 2 : ℚ) ^ N := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- **E[3/2^v] = 1**：n_k/n_0 は Terras 模型の下で厳密なマルチンゲール。
    有限版は 1 − 4^(−N)。これが裾の指数がちょうど 1 であることの中身である。 -/
theorem terras_martingale_finite (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 / 2 : ℚ) ^ (j + 1) * (3 * (1 / 2 : ℚ) ^ (j + 1))
      = 1 - (1 / 4 : ℚ) ^ N := by
  have key : ∀ j : ℕ, (1 / 2 : ℚ) ^ (j + 1) * (3 * (1 / 2 : ℚ) ^ (j + 1))
      = 3 * (1 / 4 : ℚ) ^ (j + 1) := by
    intro j
    rw [show (1 / 4 : ℚ) = (1 / 2) * (1 / 2) by norm_num, mul_pow]
    ring
  simp only [key]
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Cramér の根がちょうど θ = 1 であること（3^θ = 2^(1+θ) − 1 の θ = 1 での成立）。 -/
theorem cramer_root_one : (3 : ℚ) ^ (1 : ℕ) = 2 ^ (1 + 1 : ℕ) - 1 := by norm_num

/-! ### 【2】傾けた測度の下の歩幅分布（有限版） -/

/-- 傾け dP̃/dP = 2^(−W) の下で m ∼ Geom(3/4)：P̃(m) = (3/4)(1/4)^m は規格化されている。 -/
theorem tilted_geom_normalized (N : ℕ) :
    ∑ m ∈ Finset.range N, (3 / 4 : ℚ) * (1 / 4 : ℚ) ^ m = 1 - (1 / 4 : ℚ) ^ N := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- 傾けた歩幅の平均は 1/3 − u（負）。ここでは有理の部分 E[m] = 1/3 の有限版。 -/
theorem tilted_mean_finite (N : ℕ) :
    ∑ m ∈ Finset.range N, (m : ℚ) * ((3 / 4) * (1 / 4 : ℚ) ^ m)
      = 1 / 3 - (1 / 4 : ℚ) ^ N * ((N : ℚ) + 1 / 3) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-! ### 【3】【4】降下ラダー高と行き過ぎ -/

/-- 下向きの歩幅はちょうど −u の一種類しかない（歩幅 X = m − u, m ≥ 0）ので、
    新しい最小値の更新幅（降下ラダー高）は u を超えない。 -/
theorem ladder_height_le_u
    (u mstep Wprev Wk mn : ℝ) (hm : 0 ≤ mstep)
    (hstep : Wk = Wprev - u + mstep) (hmn : mn ≤ Wprev) :
    mn - Wk ≤ u := by
  subst hstep; linarith

/-- 水準 −s を初めて下回るときの行き過ぎ O は 0 ≤ O < u を満たす
    （下回る一手は必ず m = 0 の一種類だから）。 -/
theorem overshoot_in_range
    (u s Wprev Wk : ℝ) (_hu : 0 < u)
    (hprev : -s < Wprev) (hstep : Wk = Wprev - u) (hcross : Wk ≤ -s) :
    0 ≤ (-s) - Wk ∧ (-s) - Wk < u := by
  subst hstep
  exact ⟨by linarith, by linarith⟩

/-! ### 【5】位置の小数部は k だけで決まる -/

/-- W_k = M_k − k·u で M_k は整数なので、W_k の小数部は −k·u の小数部に等しい。
    ⇒ 行き過ぎ O = frac(σ·u)：C(s) の振動は log₂3 の連分数そのもの。 -/
theorem fract_position (M : ℤ) (t : ℝ) :
    Int.fract ((M : ℝ) - t) = Int.fract (-t) := by
  have : (M : ℝ) - t = (M : ℝ) + (-t) := by ring
  rw [this, Int.fract_intCast_add]

/-- 上と同じことの、整数水準への言い換え：s が整数なら (−s) − W の小数部も k だけで決まる。 -/
theorem fract_overshoot (M s : ℤ) (t : ℝ) :
    Int.fract ((-(s : ℝ)) - ((M : ℝ) - t)) = Int.fract t := by
  have h : (-(s : ℝ)) - ((M : ℝ) - t) = ((-s - M : ℤ) : ℝ) + t := by push_cast; ring
  rw [h, Int.fract_intCast_add]

/-! ### 【6】巡回の方程式 2^b/3^a = Π(1 + ε/(3nᵢ))：既知の四つの巡回 -/

/-- 3n+1 の自明な巡回 (1)：a = 1, b = 2。 -/
theorem cycle_eq_plus_one : (2 : ℚ) ^ (2 : ℕ) / 3 ^ (1 : ℕ) = 1 + 1 / (3 * 1) := by norm_num

/-- 3n−1 の巡回 (1)：a = 1, b = 1。 -/
theorem cycle_eq_minus_one : (2 : ℚ) ^ (1 : ℕ) / 3 ^ (1 : ℕ) = 1 - 1 / (3 * 1) := by norm_num

/-- 3n−1 の巡回 (5, 7)：a = 2, b = 3。 -/
theorem cycle_eq_minus_five_seven :
    (2 : ℚ) ^ (3 : ℕ) / 3 ^ (2 : ℕ) = (1 - 1 / (3 * 5)) * (1 - 1 / (3 * 7)) := by norm_num

/-- 3n−1 の巡回 (17, 25, 37, 55, 41, 61, 91)：a = 7, b = 11。 -/
theorem cycle_eq_minus_seven_cycle :
    (2 : ℚ) ^ (11 : ℕ) / 3 ^ (7 : ℕ) =
      (1 - 1 / (3 * 17)) * (1 - 1 / (3 * 25)) * (1 - 1 / (3 * 37)) * (1 - 1 / (3 * 55)) *
        (1 - 1 / (3 * 41)) * (1 - 1 / (3 * 61)) * (1 - 1 / (3 * 91)) := by norm_num

/-- 符号は「どちら側から近づくか」を決める：ε = +1 なら右辺 > 1、ε = −1 なら右辺 < 1。
    その有理数版（3n−1 の (5,7) 巡回で 2^b < 3^a）。 -/
theorem cycle_side_minus : (2 : ℚ) ^ (3 : ℕ) < 3 ^ (2 : ℕ) := by norm_num

/-- 3n+1 の自明な巡回では逆向き（2^b > 3^a）。 -/
theorem cycle_side_plus : (3 : ℚ) ^ (1 : ℕ) < 2 ^ (2 : ℕ) := by norm_num

/-! ### 【7】紙の側の核：符号の反転は 3 進の測度を y ↦ −y で移すだけ -/

/-- **Syr_{+1}(−m) = −Syr_{−1}(m)**：3m − 1 = 2^a·r ならば 3(−m) + 1 = 2^a·(−r)。
    2 進付値は符号で変わらないので、これは Syracuse 写像そのものの共役である。 -/
theorem syracuse_sign_conjugation (m r : ℤ) (a : ℕ) (h : 3 * m - 1 = 2 ^ a * r) :
    3 * (-m) + 1 = 2 ^ a * (-r) := by
  have hneg : 3 * (-m) + 1 = -(3 * m - 1) := by ring
  rw [hneg, h]; ring

/-- 奇数性は符号の反転で保たれる（上の共役が Syracuse 写像の像の上で閉じること）。 -/
theorem odd_neg_iff (r : ℤ) : Odd (-r) ↔ Odd r := by
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨-k - 1, by omega⟩

/-- 逆向きも成立：3m + 1 = 2^a·r ならば 3(−m) − 1 = 2^a·(−r)。
    ⇒ 二つの写像は n ↦ −n で完全に共役であり、3 進の極限測度は互いの符号反転像。
    ⇒ 倍化恒等式も、最小値まわりの定数も、ε に依らない量である。 -/
theorem syracuse_sign_conjugation' (m r : ℤ) (a : ℕ) (h : 3 * m + 1 = 2 ^ a * r) :
    3 * (-m) - 1 = 2 ^ a * (-r) := by
  have hneg : 3 * (-m) - 1 = -(3 * m + 1) := by ring
  rw [hneg, h]; ring

/-! ### 【8】3n+1 側の「順位2の席」が空であることの核 -/

/-- 順位2の席（a = 3, b = 5）の上限は 5.886…。この上限の有理版：3/(3·(5·log2 − 3·log3)) < 6
    に相当する整数の事実として、席の候補は 1 と 5 だけである（奇数・3 で割り切れない・6 未満）。
    その 5 は一段で 1 に落ちる：3·5 + 1 = 2^4·1 かつ 1 < 5。 -/
theorem seat_rank2_plus_candidate_five : 3 * 5 + 1 = 2 ^ 4 * 1 ∧ (1 : ℕ) < 5 := by norm_num

/-- 対して 3n−1 側の順位2の席（上限 5.993…）には 5 が実際に座る：
    3·5 − 1 = 2^1·7 かつ 3·7 − 1 = 2^2·5。二段で戻る（a = 2, b = 1 + 2 = 3）。 -/
theorem seat_rank2_minus_cycle : 3 * 5 - 1 = 2 ^ 1 * 7 ∧ 3 * 7 - 1 = 2 ^ 2 * 5 := by norm_num

/-- 巡回の元は 3 で割り切れない（3n ± 1 ≢ 0 (mod 3)）。席の候補を 1/3 に絞る根拠。 -/
theorem cycle_elem_not_div_three (n : ℤ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    ¬ (3 ∣ 3 * n + e) := by
  rintro ⟨k, hk⟩
  rcases he with h | h <;> subst h <;> omega

end Collatz.LadderHeight

/-! ### 依存公理の確認（`sorryAx` が無いこと） -/

#print axioms Collatz.LadderHeight.terras_prob_finite
#print axioms Collatz.LadderHeight.terras_martingale_finite
#print axioms Collatz.LadderHeight.cramer_root_one
#print axioms Collatz.LadderHeight.tilted_geom_normalized
#print axioms Collatz.LadderHeight.tilted_mean_finite
#print axioms Collatz.LadderHeight.ladder_height_le_u
#print axioms Collatz.LadderHeight.overshoot_in_range
#print axioms Collatz.LadderHeight.fract_position
#print axioms Collatz.LadderHeight.fract_overshoot
#print axioms Collatz.LadderHeight.cycle_eq_plus_one
#print axioms Collatz.LadderHeight.cycle_eq_minus_one
#print axioms Collatz.LadderHeight.cycle_eq_minus_five_seven
#print axioms Collatz.LadderHeight.cycle_eq_minus_seven_cycle
#print axioms Collatz.LadderHeight.cycle_side_minus
#print axioms Collatz.LadderHeight.cycle_side_plus
#print axioms Collatz.LadderHeight.syracuse_sign_conjugation
#print axioms Collatz.LadderHeight.odd_neg_iff
#print axioms Collatz.LadderHeight.syracuse_sign_conjugation'
#print axioms Collatz.LadderHeight.seat_rank2_plus_candidate_five
#print axioms Collatz.LadderHeight.seat_rank2_minus_cycle
#print axioms Collatz.LadderHeight.cycle_elem_not_div_three
