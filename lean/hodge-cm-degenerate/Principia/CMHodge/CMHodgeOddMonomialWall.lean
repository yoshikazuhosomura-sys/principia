/-
  CM 型の退化した例外類 — 奇単項の壁（2 進）と、対称化した表示が閉じること

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ` は積の主偏極、`W = Θ ∧_{F₀} Θ`
  （`F₀` は三次の総実体・`q = 19`）。成分は `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`・`Sᵢ ⪰ 0`）、
  要求は `Σ y_k [Z_k] = G₆ = (g³/24)Θ³ + (gq/2)ΘW`、`y_k ≥ 0` かつ `y_k ∈ ℤ`。

  `μ(I,·) : Sym²V → H⁶` は単射で、その像 `M21`（21 次元）の元は四次形式
  （3 変数・15 個の単項式）で表される。この頁で Lean にするのは次の算術だけである。

  (A) `u = v` の原子の四次形式は `(u·x)⁴` の非負整数倍で、その `x³y` の係数は `4u₁³u₂`
      （4 の倍数）、`xyz²` の係数は `12u₁u₂u₃²`（12 の倍数）である。
      目標の四次形式の `x³y` の係数は `-6g`、`xyz²` の係数は `-6g` である。
      `u ≠ v` の原子の部分を符号変換で不変に取ると（＝対称化すると）その寄与は奇単項で 0 になるので、
      要求は `g·(4k) = -6g`（または `g·(12k) = -6g`）となり、`2k = -3`（`2k = -1`）に帰着して不可能。

  (B) 混合原子（`S₁ = a·uu^T`・`S₂ = bI`）の四次形式は
      `ab(g-b)·(x²+y²+z²)(u·x)² - a²b·(u·x)⁴` で、その `x³y` の係数は
      `2ab(g-b)u₁u₂ - 4a²b u₁³u₂`。`a = b = 1`・`u = (1,1,0)`・`g` 偶数なら `2g - 6 ≡ 2 (mod 4)` で、
      (A) の壁を破る。

  (C) 混合原子を入れた場合に `g` が満たすべき条件。`x³y` と `xy³` の二行の差から
      `F = g·(E + 14)`（`E`・`F` はともに `24` の倍数）が出るので `12 ∣ g` である。
      ここで `24 ∣ E` は `4u₁u₂(u₁² - u₂²)` が `24` の倍数であること、すなわち
      `6 ∣ u₁u₂(u₁² - u₂²)` から来る。

  幾何・層・コホモロジー・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。
-/
import Mathlib

namespace CMHodgeOddMonomialWall

/-! ### (A) 奇単項の係数の割り切れ方 -/

/-- `(u·x)⁴` の `x³y` の係数は `4u₁³u₂` で、4 の倍数である。 -/
theorem four_dvd_x3y_coeff (u₁ u₂ : ℤ) : (4:ℤ) ∣ 4 * u₁ ^ 3 * u₂ := by
  exact ⟨u₁ ^ 3 * u₂, by ring⟩

/-- `(u·x)⁴` の `xyz²` の係数は `12u₁u₂u₃²` で、12 の倍数である。 -/
theorem twelve_dvd_xyz2_coeff (u₁ u₂ u₃ : ℤ) : (12:ℤ) ∣ 12 * u₁ * u₂ * u₃ ^ 2 :=
  ⟨u₁ * u₂ * u₃ ^ 2, by ring⟩

/-- 有限個の `u = v` 原子の和でも `x³y` の係数は 4 の倍数である。 -/
theorem four_dvd_sum_x3y {ι : Type*} (s : Finset ι) (M u₁ u₂ : ι → ℤ) :
    (4:ℤ) ∣ ∑ i ∈ s, M i * (4 * (u₁ i) ^ 3 * (u₂ i)) := by
  refine Finset.dvd_sum ?_
  intro i _
  exact Dvd.dvd.mul_left (four_dvd_x3y_coeff (u₁ i) (u₂ i)) (M i)

/-! ### 算術の核 -/

theorem two_mul_ne_neg_three (k : ℤ) : 2 * k ≠ -3 := by
  intro h
  have : (2:ℤ) ∣ -3 := ⟨k, h.symm⟩
  norm_num at this

theorem two_mul_ne_neg_one (k : ℤ) : 2 * k ≠ -1 := by
  intro h
  have : (2:ℤ) ∣ -1 := ⟨k, h.symm⟩
  norm_num at this

/-! ### (A) の壁 -/

/-- **対称化した表示の壁（`x³y`・mod 4）。**`u ≠ v` の原子の部分を符号変換で不変に取ると、
奇単項 `x³y` の等式は `g·(4k) = -6g` になり、`g ≠ 0` では成り立たない。 -/
theorem symmetric_wall_four (g k : ℤ) (hg : g ≠ 0) : g * (4 * k) ≠ -6 * g := by
  intro h
  have h2 : g * (4 * k + 6) = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hg h3
  · exact two_mul_ne_neg_three k (by linarith)

/-- **同じ壁の `xyz²`（mod 12）の形。** -/
theorem symmetric_wall_twelve (g k : ℤ) (hg : g ≠ 0) : g * (12 * k) ≠ -6 * g := by
  intro h
  have h2 : g * (12 * k + 6) = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hg h3
  · exact two_mul_ne_neg_three (3 * k) (by linarith)

/-- 和の形にした壁：`u = v` の原子だけでは `x³y` の係数 `-6g` は作れない。 -/
theorem odd_monomial_wall {ι : Type*} (s : Finset ι) (M u₁ u₂ : ι → ℤ) (g : ℤ) (hg : g ≠ 0) :
    g * (∑ i ∈ s, M i * (4 * (u₁ i) ^ 3 * (u₂ i))) ≠ -6 * g := by
  obtain ⟨k, hk⟩ := four_dvd_sum_x3y s M u₁ u₂
  rw [hk]
  exact symmetric_wall_four g k hg

/-! ### (B) 混合原子は mod 4 の壁を破る -/

/-- 混合原子（`a = b = 1`・`u = (1,1,0)`）の `x³y` の係数は `2g - 6` で、
`g` が偶数なら `mod 4` で `2` である（`u = v` の原子はすべて `0`）。 -/
theorem mixed_atom_breaks_mod_four (t : ℤ) : (2 * (2 * t - 1) * 1 - 4 * 1) % 4 = 2 := by
  omega

/-! ### (C) 混合原子を入れたときの `g` への条件 -/

/-- `u₁u₂(u₁² - u₂²)` は 6 の倍数である。 -/
theorem six_dvd_cross (a b : ℤ) : (6:ℤ) ∣ a * b * (a ^ 2 - b ^ 2) := by
  have key : ∀ x y : ZMod 6, x * y * (x ^ 2 - y ^ 2) = 0 := by decide
  have h : ((a * b * (a ^ 2 - b ^ 2) : ℤ) : ZMod 6) = 0 := by
    push_cast
    exact key a b
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mp h

/-- 従って `4u₁u₂(u₁² - u₂²)` は 24 の倍数である。 -/
theorem twentyfour_dvd_diff (a b : ℤ) : (24:ℤ) ∣ 4 * (a * b * (a ^ 2 - b ^ 2)) := by
  obtain ⟨c, hc⟩ := six_dvd_cross a b
  exact ⟨c, by rw [hc]; ring⟩

/-- **`12 ∣ g` が必要**：`x³y` と `xy³` の二行の差から `F = g(E + 14)` が出て、
`E`・`F` がともに 24 の倍数なら `12 ∣ g`。 -/
theorem twelve_dvd_g_of_rows (g E F : ℤ) (hE : (24:ℤ) ∣ E) (hF : (24:ℤ) ∣ F)
    (h : F = g * (E + 14)) : (12:ℤ) ∣ g := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨f, hf⟩ := hF
  have h7 : (12:ℤ) ∣ 7 * g := by
    refine ⟨f - g * e, ?_⟩
    have : (24:ℤ) * f = g * (24 * e + 14) := by rw [← hf, h, he]
    linarith [this]
  obtain ⟨m, hm⟩ := h7
  exact ⟨7 * m - 4 * g, by linarith [hm]⟩

end CMHodgeOddMonomialWall

#print axioms CMHodgeOddMonomialWall.four_dvd_x3y_coeff
#print axioms CMHodgeOddMonomialWall.twelve_dvd_xyz2_coeff
#print axioms CMHodgeOddMonomialWall.four_dvd_sum_x3y
#print axioms CMHodgeOddMonomialWall.two_mul_ne_neg_three
#print axioms CMHodgeOddMonomialWall.two_mul_ne_neg_one
#print axioms CMHodgeOddMonomialWall.symmetric_wall_four
#print axioms CMHodgeOddMonomialWall.symmetric_wall_twelve
#print axioms CMHodgeOddMonomialWall.odd_monomial_wall
#print axioms CMHodgeOddMonomialWall.mixed_atom_breaks_mod_four
#print axioms CMHodgeOddMonomialWall.six_dvd_cross
#print axioms CMHodgeOddMonomialWall.twentyfour_dvd_diff
#print axioms CMHodgeOddMonomialWall.twelve_dvd_g_of_rows
