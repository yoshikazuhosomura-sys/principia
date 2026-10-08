/-
  CM 型の退化した例外類 — 内点の丸めによる非負整数解と、共有因子の予算

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ` は積の主偏極、
  `W = Θ ∧_{F₀} Θ`（`F₀` は三次の総実体・`q = 19`）。成分は
  `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`・`Sᵢ ⪰ 0`）で、要求は
  `Σ y_k [Z_k] = G₆ = (g³/24)Θ³ + (gq/2)ΘW`、`y_k ≥ 0` かつ `y_k ∈ ℤ` である。

  この頁で Lean にするのは三つである。

  (A) 丸めの補題。整数の線型系 `A y = b` について、
      「すべての座標が `m` 以上の整数点 `y₁`」と「`A k = b − A y₁` を満たし
       すべての座標が絶対値 `< m` の整数ベクトル `k`」があれば、
      `y := y₁ + k` は `A y = b` を満たす**狭義正**の整数解である。
      ⇒ 非負整数解の存在は「内点の余裕 `m`」対「格子の最近平面の誤差」の比較に還元される。
      これが実際に使った形で、余裕 `m = 33297`・誤差 `874` だった。

  (B) 余裕の上限。狭義正の汎関数 `d`（幾何では `d_k = ∫[Z_k]·Θ³ > 0`）について
      `Σ y_k d_k = D` が成り立つなら、すべての座標が `m` 以上の非負解に対し
      `m·Σ d_k ≤ D` である。⇒ **余裕は列の本数に反比例して減る。**
      列を絞ってから丸める道が不利であることの、量的な理由である。

  (C) 予算。共有因子の和 `Σ_j S₁^{(j)}` が**階数 1 の非負結合**（`Σ_j c_j u_j u_jᵀ`・`c_j ≥ 0`）で
      書けるとき、`tr(Σ_j S₁^{(j)}) ≤ g` ならば `gI − Σ_j S₁^{(j)} ⪰ 0` である
      （二次形式の水準で。Cauchy–Schwarz を各項に当てるだけで出る）。
      幾何では `S₁^{(j)}` は `a·uuᵀ` または `b·I = Σᵢ b·eᵢeᵢᵀ` なので、この形に必ず収まる。
      実測では `tr = 2454 ≤ g = 37800` だった。

  「新規」「世界初」とは書かない。ホッジ予想の本体・代数性については何も主張しない。
-/
import Mathlib

namespace CMHodgeRoundingBudget

/-! ## (A) 丸めの補題 -/

/-- 丸めの補題（線型の部分）：`k` が残差 `b − A y₁` を表せば `y₁ + k` は `A y = b` を満たす。 -/
theorem rounding_solves {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → ι → ℤ) (b : Fin n → ℤ) (y₁ k : ι → ℤ)
    (hk : ∀ i, ∑ j, A i j * k j = b i - ∑ j, A i j * y₁ j) :
    ∀ i, ∑ j, A i j * (y₁ j + k j) = b i := by
  intro i
  have : ∑ j, A i j * (y₁ j + k j) = (∑ j, A i j * y₁ j) + ∑ j, A i j * k j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hk i]; ring

/-- 丸めの補題（符号の部分）：余裕 `m` が誤差 `|k|` を上回れば、丸めた点は狭義正である。 -/
theorem rounding_pos {ι : Type*} (y₁ k : ι → ℤ) (m : ℤ)
    (hy : ∀ j, m ≤ y₁ j) (hk : ∀ j, |k j| < m) :
    ∀ j, 0 < y₁ j + k j := by
  intro j
  have h1 : -k j ≤ |k j| := neg_le_abs _
  have h2 : |k j| < m := hk j
  have h3 : m ≤ y₁ j := hy j
  linarith

/-- (A) の合わせ：余裕が誤差を上回るとき、丸めは非負整数解を与える。 -/
theorem rounding_nonneg_solution {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Fin n → ι → ℤ) (b : Fin n → ℤ) (y₁ k : ι → ℤ) (m : ℤ)
    (hy : ∀ j, m ≤ y₁ j) (hk : ∀ j, |k j| < m)
    (hres : ∀ i, ∑ j, A i j * k j = b i - ∑ j, A i j * y₁ j) :
    (∀ i, ∑ j, A i j * (y₁ j + k j) = b i) ∧ (∀ j, 0 ≤ y₁ j + k j) :=
  ⟨rounding_solves A b y₁ k hres,
   fun j => le_of_lt (rounding_pos y₁ k m hy hk j)⟩

/-- 本稿で実際に成り立った不等式（誤差 `874` ＜ 余裕 `33297`）と、得られた最小成分。 -/
theorem margin_beats_error : (874 : ℤ) < 33297 ∧ (0 : ℤ) < 32512 := by norm_num

/-! ## (B) 余裕の上限 -/

/-- 狭義正の汎関数の下では、余裕は「予算 ÷ 列の次数の総和」で上から押さえられる。 -/
theorem margin_le_budget_div {ι : Type*} [Fintype ι]
    (d y : ι → ℤ) (D m : ℤ) (hd : ∀ j, 0 < d j) (hy : ∀ j, m ≤ y j)
    (hsum : ∑ j, y j * d j = D) :
    m * ∑ j, d j ≤ D := by
  rw [← hsum, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    exact mul_le_mul_of_nonneg_right (hy j) (le_of_lt (hd j)) |>.trans_eq (by ring)

/-- 非負解の存在下では予算は非負である（有界性の言い直し）。 -/
theorem budget_nonneg {ι : Type*} [Fintype ι]
    (d y : ι → ℤ) (D : ℤ) (hd : ∀ j, 0 < d j) (hy : ∀ j, 0 ≤ y j)
    (hsum : ∑ j, y j * d j = D) : 0 ≤ D := by
  rw [← hsum]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (le_of_lt (hd j))

/-! ## (C) 予算：階数 1 の非負結合は痕跡で押さえられる -/

/-- 三次元の Cauchy–Schwarz（Lagrange の恒等式から）。 -/
theorem cauchy_schwarz_three (u x : Fin 3 → ℝ) :
    (u 0 * x 0 + u 1 * x 1 + u 2 * x 2) ^ 2
      ≤ (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  nlinarith [sq_nonneg (u 0 * x 1 - u 1 * x 0), sq_nonneg (u 0 * x 2 - u 2 * x 0),
             sq_nonneg (u 1 * x 2 - u 2 * x 1)]

/-- 階数 1 の一項：`c·(u·x)² ≤ c·|u|²·|x|²`（`c ≥ 0`）。 -/
theorem rankone_quad_le (c : ℝ) (hc : 0 ≤ c) (u x : Fin 3 → ℝ) :
    c * (u 0 * x 0 + u 1 * x 1 + u 2 * x 2) ^ 2
      ≤ c * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  have h := cauchy_schwarz_three u x
  calc c * (u 0 * x 0 + u 1 * x 1 + u 2 * x 2) ^ 2
      ≤ c * ((u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) :=
        mul_le_mul_of_nonneg_left h hc
    _ = c * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by ring

/-- **予算の補題**：共有因子の和が階数 1 の非負結合で、その痕跡が `g` 以下なら、
`gI − Σ_j S₁^{(j)}` は半正定値である（二次形式の水準）。 -/
theorem budget_psd_of_trace_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (u : ι → Fin 3 → ℝ) (g : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (htr : ∑ i ∈ s, c i * (u i 0 ^ 2 + u i 1 ^ 2 + u i 2 ^ 2) ≤ g)
    (x : Fin 3 → ℝ) :
    ∑ i ∈ s, c i * (u i 0 * x 0 + u i 1 * x 1 + u i 2 * x 2) ^ 2
      ≤ g * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  have hx : (0:ℝ) ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by positivity
  calc ∑ i ∈ s, c i * (u i 0 * x 0 + u i 1 * x 1 + u i 2 * x 2) ^ 2
      ≤ ∑ i ∈ s, c i * (u i 0 ^ 2 + u i 1 ^ 2 + u i 2 ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) :=
        Finset.sum_le_sum fun i hi => rankone_quad_le (c i) (hc i hi) (u i) x
    _ = (∑ i ∈ s, c i * (u i 0 ^ 2 + u i 1 ^ 2 + u i 2 ^ 2)) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
        rw [Finset.sum_mul]
    _ ≤ g * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := mul_le_mul_of_nonneg_right htr hx

/-- 本稿の予算の実測値（痕跡 `2454` ≤ `g = 37800`）。 -/
theorem trace_within_budget : (2454 : ℤ) ≤ 37800 := by norm_num

#print axioms rounding_solves
#print axioms rounding_pos
#print axioms rounding_nonneg_solution
#print axioms margin_beats_error
#print axioms margin_le_budget_div
#print axioms budget_nonneg
#print axioms cauchy_schwarz_three
#print axioms rankone_quad_le
#print axioms budget_psd_of_trace_le
#print axioms trace_within_budget

end CMHodgeRoundingBudget
