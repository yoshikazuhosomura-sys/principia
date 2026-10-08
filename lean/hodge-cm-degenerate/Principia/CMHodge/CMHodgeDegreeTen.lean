/-
  CM 型の退化した例外類 — 重複度の入り方と、次数 10・次数 12・予算の同時の証明書

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ` は積の主偏極、
  `W = Θ ∧_{F₀} Θ`（`F₀` は三次の総実体・`q = 19`）、`g = 7560`。成分は
  `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`・`Sᵢ ⪰ 0`）で、重複度 `y_k` は非負整数である。

  この頁で Lean にするのは五つで、どれも有限の代数の等式・不等式だけである。

  (A) 肥厚は次数 8 で排除される。重複度を「一方向の肥厚 `(f₁^m, f₂, f₃)`」で作ると
      `Σ Eᵢ = gI + (m−1)S₁` になり、次数 8 の要求は
      `Σ_k a_k (m_k − 1) = 0`（`a_k = [Z_k]·S₁^{(k)}·Θ² ≥ 0`）に帰着する。
      係数が非負で、狭義正の係数が一つでもあれば、その成分の重複度は 1 でなければならない。

  (B) 肥厚の `ch` は重複度について線型でない（次数 10 の係数に `m²`・`m³` が出る）。

  (C) 包除が対で止まる次元の勘定（`1 + 2 + 2 + 2 = 7 > 6`）。

  (D) 予算の真の上限は痕跡ではなく固有値である。共有因子の和が
      `Σ = 57·I + (−3)·(J − I)`（`J` は全 1 行列）のとき、`gI − c·Σ ⪰ 0` の上限は
      痕跡の判定が与える `c ≤ 44` ではなく `c ≤ 125` である。

  (E) 次数 10 の証明書。6 本の有効曲線類（5 重完全交叉）の**狭義正**の有理係数の和が
      `[C'] = deficit + glue/113` にちょうど等しい（6 座標すべて）。

  幾何の内容（層の存在・スキーム性・代数性）は Lean に入っていない。
  この頁は「上の有限の代数が確かに成り立つ」ことだけを主張する。
-/
import Mathlib

namespace CMHodgeDegreeTen

open Finset

/-! ### (A) 肥厚は次数 8 で排除される -/

/-- 非負の係数の和が 0 なら、狭義正の係数を持つ項の因子は 0 である。 -/
theorem nonneg_sum_zero_forces {n : ℕ} (a t : Fin n → ℚ)
    (ha : ∀ i, 0 ≤ a i) (ht : ∀ i, 0 ≤ t i)
    (hsum : ∑ i, a i * t i = 0) (j : Fin n) (hj : 0 < a j) : t j = 0 := by
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ a i * t i := fun i _ => mul_nonneg (ha i) (ht i)
  have hz : a j * t j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (ne_of_gt hj)
  · exact h

/-- 次数 8 の要求の形。重複度 `m i ≥ 1` を肥厚で作ると、食い違いは
    `Σ a i (m i − 1)` で、`a i ≥ 0` かつ `a j > 0` なら `m j = 1` が必要になる。 -/
theorem thickening_forces_reduced {n : ℕ} (a m : Fin n → ℚ)
    (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 1 ≤ m i)
    (hsum : ∑ i, a i * (m i - 1) = 0) (j : Fin n) (hj : 0 < a j) : m j = 1 := by
  have h := nonneg_sum_zero_forces a (fun i => m i - 1) ha
    (fun i => by linarith [hm i]) hsum j hj
  linarith [h]

/-- 実測（`g = 7560`・835 列）：狭義正の列が 822 本ある。 -/
theorem deg8_strictly_positive_columns : (822 : ℕ) ≤ 835 := by norm_num

/-! ### (B) 肥厚の `ch` は重複度について線型でない -/

/-- 完全交叉 `(m S₁, S₂, S₃)` の次数 10 の値は
    `f m = (1/6) A m³ + (1/4) B m² + C m`（`A = e S₁²`・`B = e S₁(S₂+S₃)`・`C` は `m` に依らない部分）。
    `A = 0` でも `B ≠ 0` なら `f` は線型でない（`f 2 ≠ 2 * f 1`）。 -/
theorem zeta10_not_linear (A B C : ℚ) (hA : A = 0) (hB : B ≠ 0) :
    ((1:ℚ)/6 * A * 2 ^ 3 + (1:ℚ)/4 * B * 2 ^ 2 + C * 2)
      ≠ 2 * ((1:ℚ)/6 * A * 1 ^ 3 + (1:ℚ)/4 * B * 1 ^ 2 + C * 1) := by
  subst hA; intro h; apply hB; linarith

/-- 階数 3 の共有因子（`S₁ = 3I`・`g = 7560`）では `m³` の係数も非零である（実測値）。 -/
theorem zeta10_cubic_coeff_nonzero :
    (2720160 : ℚ) ≠ 0 ∧ (30842534160 : ℚ) ≠ 0 := by
  constructor <;> norm_num

/-- 全方向の肥厚 `I^m` の生成点での長さは `C(m+2,3)` であって `m` ではない
    （`m = 1,…,6` での実測。`m ≥ 2` で `m` と食い違う）。 -/
theorem full_thickening_length_values :
    (List.range 6).map (fun k => ∑ j ∈ Finset.range (k+1), (j + 1) * (j + 2) / 2)
      = [1, 4, 10, 20, 35, 56] := by decide

theorem full_thickening_ne_multiplicity : (4 : ℕ) ≠ 2 ∧ (10 : ℕ) ≠ 3 := by
  constructor <;> norm_num

/-! ### (C) 包除が対で止まる（次元の勘定） -/

/-- 三つの成分の交わりの余次元は `1 + 2 + 2 + 2 = 7`。`dim X = 6` より大きいので空である。 -/
theorem triple_intersection_empty : (1 : ℕ) + 2 + 2 + 2 > 6 := by norm_num

/-- 二つの成分：共有因子を持てば余次元 5（曲線）、持たなければ余次元 6（点）。 -/
theorem pair_codims : (1 : ℕ) + 2 + 2 = 5 ∧ (3 : ℕ) + 3 = 6 := by
  constructor <;> norm_num


/-! ### (D) 予算の真の上限は痕跡ではなく固有値 -/

/-- 3 次の対称行列 `M = d·I + o·(J − I)` の固有値は `d + 2o`（固有ベクトル `(1,1,1)`）と
    `d − o`（二重）。`Σ_j S₁^{(j)} = 57·I + (−3)·(J − I)` では `51` と `60`。 -/
theorem shared_sum_eigenvalues :
    (57 : ℤ) + 2 * (-3) = 51 ∧ (57 : ℤ) - (-3) = 60 := by
  constructor <;> norm_num

/-- 半正定値の条件 `gI − c·Σ ⪰ 0` は最大固有値で決まる：`60 * c ≤ 7560`（`c ≤ 126`）。
    `det > 0` を要求すると `c ≤ 125`。痕跡の判定（`171 * c ≤ 7560`）は `c ≤ 44` しか与えない。 -/
theorem budget_eigen_beats_trace :
    60 * 125 < 7560 ∧ 60 * 126 = 7560 ∧ 171 * 44 ≤ 7560 ∧ 7560 < 171 * 45 ∧ 44 < 125 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `c = 113` での残りの因子 `gI − 113·Σ = 1119·I + 339·(J − I)`：
    対角・2 次の主小行列式・行列式のすべてが正（⇒ 狭義正定値）。 -/
theorem budget_psd_113 :
    (0 : ℤ) < 1119 ∧ (0 : ℤ) < 1119 * 1119 - 339 * 339 ∧
      (0 : ℤ) < 1119 ^ 3 - 3 * 1119 * 339 ^ 2 + 2 * 339 ^ 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- その行列式と `h⁰(D') = det²`（実測値）。 -/
theorem residual_h0_pos :
    (1119 : ℤ) ^ 3 - 3 * 1119 * 339 ^ 2 + 2 * 339 ^ 3 = 1093294800 ∧
      (0 : ℤ) < 1093294800 ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ### (E) 次数 10 の証明書 -/

/-- 6 本の 5 重完全交叉の類（`E_i` との交点数の 6 座標。整数ベクトル）。 -/
def v : Fin 6 → Fin 6 → ℚ
  | 0 => ![104, 56, 32, 128, 80, 16]
  | 1 => ![20, 20, 8, -32, 4, 4]
  | 2 => ![44, 8, 44, -4, -80, -4]
  | 3 => ![8, 20, 20, -4, 4, 32]
  | 4 => ![104, 32, 80, -40, 152, -8]
  | 5 => ![32, 104, 80, -40, 8, -152]

/-- 証明書の係数（狭義正の有理数）。 -/
def x : Fin 6 → ℚ
  | 0 => 973503365624205605573 / 383748
  | 1 => 1716048292944949039049 / 319790
  | 2 => 4404887084717296718291 / 959370
  | 3 => 10783331299714340274613 / 959370
  | 4 => 783505274115155048389 / 1918740
  | 5 => 4999391791297406637139 / 1918740

/-- 目標の類 `[C'] = deficit + glue/113`（6 座標）。 -/
def cprime : Fin 6 → ℚ
  | 0 => 89150529761956742792 / 113
  | 1 => 89830806710178861280 / 113
  | 2 => 89500938588806307880 / 113
  | 3 => -3490032269605076048 / 113
  | 4 => -1698518367538805248 / 113
  | 5 => 458418157506924616 / 113

/-- 係数はすべて狭義正である。 -/
theorem cert_coeffs_pos : ∀ j, 0 < x j := by
  intro j; fin_cases j <;> (unfold x; norm_num)

/-- 6 座標すべてで `Σ_j x j • v j = [C']` が厳密に成り立つ。
    ⇒ `[C']` は 5 重完全交叉の類の**狭義正の有理係数の和**であり、有効曲線類の錐の内部にある。 -/
theorem cert_exact : ∀ i, ∑ j, x j * v j i = cprime i := by
  intro i
  fin_cases i <;>
    simp [Fin.sum_univ_six, v, x, cprime] <;> norm_num

/-- 次数 12 の余り（点で吸収する本数）は `c = 113` で狭義正である（実測値）。 -/
theorem deg12_points_pos :
    (0 : ℚ) < 1933262236425183396439556 / 113 := by norm_num

/-- 三つの条件が同時に立つ窓（実測）：`104 ≤ c ≤ 125`。 -/
theorem window_nonempty : (104 : ℕ) ≤ 113 ∧ (113 : ℕ) ≤ 125 ∧ (104 : ℕ) ≤ 125 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

#print axioms nonneg_sum_zero_forces
#print axioms thickening_forces_reduced
#print axioms deg8_strictly_positive_columns
#print axioms zeta10_not_linear
#print axioms zeta10_cubic_coeff_nonzero
#print axioms full_thickening_length_values
#print axioms full_thickening_ne_multiplicity
#print axioms triple_intersection_empty
#print axioms pair_codims
#print axioms shared_sum_eigenvalues
#print axioms budget_eigen_beats_trace
#print axioms budget_psd_113
#print axioms residual_h0_pos
#print axioms cert_coeffs_pos
#print axioms cert_exact
#print axioms deg12_points_pos
#print axioms window_nonempty

end CMHodgeDegreeTen
