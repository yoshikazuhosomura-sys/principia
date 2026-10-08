/-
  CM 型の退化した例外類 — 整数の模型にするときの、有限の代数だけ

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元・`td(X) = 1`）、`Θ` は積の主偏極、
  `W = Θ ∧_{F₀} Θ`（`F₀` は三次の総実体・`q = 19`）。`NS(X)⊗Q = Sym²(Q³)` で `D_S` が因子類、
  `χ(D_S) = det(S)²`（指数定理）。成分は `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`）、
  `A = (g/2)Θ`、`G = 2sinh(gΘ/2) - gβ`、`ch(O_{Z_k}) = ∏(1 - e^{-Sᵢ})`（Koszul）。

  この頁で Lean にするのは次の八つで、いずれも**有限の代数の等式・不等式**である。
  幾何・層・コホモロジー・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) 因子の類を整数にする `g` の最小値：台の `T` の分母は `28|u|²` と `(s' の分母)|v|²` を割り、
      箱 2 の原始ベクトルの `|u|²` は `{1,2,3,5,6,9}` に限る。ゆえに `g = lcm(2520, 1080) = 7560`。
      `28·5 = 140` は 4032 を割らないので、4032 では足りない。
  (2) 凸結合：二つの非負表示の凸結合は非負表示である（`t = 1/893025 = 1/945²`）。
  (3) `∏(1 - e^{-xᵢ})` の次数 4・5・6 の部分の閉じた形（`c₁ = 1`, `c₂ = -1/2`, `c₃ = 1/6`, `c₄ = -1/24`）。
      次数 4 は `-(1/2)xyz(x+y+z)` で、`Σxᵢ = gΘ` なら次数 6 の等式から従う。
  (4) `R₁₀` の係数（`g = 8`）と、次数 12 の要求の閉じた形（`g = 7560`）。
  (5) Farkas：線型汎関数が生成元で非負・目標で負なら、目標は錐に入らない。
      nef 類との交点数が負なら有効ではない、はその特別な場合である。
  (6) 貼り合わせの本数の下限：不足 `d < 0` を一組 `m > 0` で埋めるには `n ≥ (-d)/m` 組要る。
  (7) `Σxᵢ = g`・`xᵢ ≥ 0` なら `σ₂ = Σ_{i<j}xᵢxⱼ ≤ g²/3`（等号は `xᵢ = g/3`）。
  (8) 行和が 0 の対称行列に対し `Σ_{a,b} v_a(1 - v_b)Φ_{ab} = -Σ_{a,b} v_a v_b Φ_{ab}`。
      これで「原子の上で非負」が「`Φ ⪯ 0`」に翻訳される。
-/
import Mathlib

namespace CMHodgeIntegralModel

/-! ### (1) 因子の類を整数にする `g` -/

/-- 箱 2 の原始ベクトルの `|u|²` は `{1,2,3,5,6,9}` に限る。各々で `28|u|²` は 7560 を割る。 -/
theorem norms_dvd_7560 :
    (28 * 1 ∣ 7560) ∧ (28 * 2 ∣ 7560) ∧ (28 * 3 ∣ 7560) ∧
    (28 * 5 ∣ 7560) ∧ (28 * 6 ∣ 7560) ∧ (28 * 9 ∣ 7560) := by
  refine ⟨⟨270, rfl⟩, ⟨135, rfl⟩, ⟨90, rfl⟩, ⟨54, rfl⟩, ⟨45, rfl⟩, ⟨30, rfl⟩⟩

/-- `s'` の分母（1,2,3,4）と `|v|²` の積も 7560 を割る（最大のもので確かめる）。 -/
theorem sden_dvd_7560 : (4 * 9 ∣ 7560) ∧ (3 * 9 ∣ 7560) ∧ (4 * 5 ∣ 7560) ∧ (4 * 6 ∣ 7560) := by
  refine ⟨⟨210, rfl⟩, ⟨280, rfl⟩, ⟨378, rfl⟩, ⟨315, rfl⟩⟩

/-- 4032 では足りない：`|u|² = 5` の原子が整にならない。 -/
theorem not_dvd_4032 : ¬ (28 * 5 ∣ 4032) := by decide

/-- `g` の値と素因数分解。 -/
theorem g_factorisation : (7560 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 * 7 := by norm_num

theorem lcm_2520_1080 : Nat.lcm 2520 1080 = 7560 := by decide

/-! ### (2) 凸結合 -/

/-- 二つの非負係数の表示の凸結合は非負係数の表示である。 -/
theorem convex_nonneg {ι : Type*} (f h : ι → ℚ) (hf : ∀ i, 0 ≤ f i) (hh : ∀ i, 0 ≤ h i)
    (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ i, 0 ≤ (1 - t) * f i + t * h i := by
  intro i
  have : 0 ≤ 1 - t := by linarith
  have h1 : 0 ≤ (1 - t) * f i := mul_nonneg this (hf i)
  have h2 : 0 ≤ t * h i := mul_nonneg ht0 (hh i)
  linarith

/-- 本稿の混ぜ方：`s = q/(2g²)`（`g = 7560`・`q = 19`）と `s₀ = 19/128` の比。 -/
theorem t_value : ((19 : ℚ) / (2 * 7560 ^ 2)) / ((19 : ℚ) / 128) = 1 / 893025 := by norm_num

theorem t_is_square : (893025 : ℕ) = 945 ^ 2 := by norm_num

/-! ### (3) `∏(1 - e^{-xᵢ})` の閉じた形 -/

/-- 次数 4（`a+b+c = 4`・各 `≥ 1`）：係数は `(2,1,1)` 型の `-1/2` だけ。 -/
theorem zeta8_closed (x y z : ℚ) :
    (-(1:ℚ)/2) * (x ^ 2 * y * z) + (-(1:ℚ)/2) * (x * y ^ 2 * z) + (-(1:ℚ)/2) * (x * y * z ^ 2)
      = -(1/2) * (x * y * z) * (x + y + z) := by ring

/-- 次数 5：`(3,1,1)` 型は `1/6`、`(2,2,1)` 型は `1/4`。 -/
theorem zeta10_closed (x y z : ℚ) :
    (1:ℚ)/6 * (x ^ 3 * y * z + x * y ^ 3 * z + x * y * z ^ 3)
      + (1:ℚ)/4 * (x ^ 2 * y ^ 2 * z + x ^ 2 * y * z ^ 2 + x * y ^ 2 * z ^ 2)
      = (1/6) * (x * y * z) * (x ^ 2 + y ^ 2 + z ^ 2)
        + (1/4) * (x * y * z) * (x * y + y * z + z * x) := by ring

/-- 次数 6：`(4,1,1)` 型は `-1/24`、`(3,2,1)` 型は `-1/12`、`(2,2,2)` 型は `-1/8`。 -/
theorem zeta12_closed (x y z : ℚ) :
    (-(1:ℚ)/24) * (x ^ 4 * y * z + x * y ^ 4 * z + x * y * z ^ 4)
      + (-(1:ℚ)/12) * (x ^ 3 * y ^ 2 * z + x ^ 3 * y * z ^ 2 + x ^ 2 * y ^ 3 * z
          + x * y ^ 3 * z ^ 2 + x ^ 2 * y * z ^ 3 + x * y ^ 2 * z ^ 3)
      + (-(1:ℚ)/8) * (x ^ 2 * y ^ 2 * z ^ 2)
      = -(x * y * z) * ((1/24) * (x ^ 3 + y ^ 3 + z ^ 3)
          + (1/12) * (x ^ 2 * y + x ^ 2 * z + y ^ 2 * x + y ^ 2 * z + z ^ 2 * x + z ^ 2 * y)
          + (1/8) * (x * y * z)) := by ring

/-- `ΣSᵢ = gΘ` なら次数 8 の要求は次数 6 の等式から従う（乗数が `gΘ` になる）。 -/
theorem deg8_from_deg6 (x y z g E : ℚ) (hsum : x + y + z = g) (hE : x * y * z = E) :
    (-(1:ℚ)/2) * (x ^ 2 * y * z) + (-(1:ℚ)/2) * (x * y ^ 2 * z) + (-(1:ℚ)/2) * (x * y * z ^ 2)
      = -(g / 2) * E := by
  rw [← hE, ← hsum]; ring

/-! ### (4) `R₁₀` と次数 12 -/

theorem R10_coeff_theta5 : (8:ℚ) ^ 5 / 192 + (8:ℚ) ^ 5 / 1920 = 2816 / 15 := by norm_num
theorem R10_coeff_theta3W : (8:ℚ) ^ 3 * 19 / 16 = 608 := by norm_num
theorem R10_coeff_thetaW2 : -((8:ℚ) * 19 ^ 2 / 8) = -361 := by norm_num

/-- `∫R₁₀·Θ`（`g = 7560`・`∫Θ⁶ = 720`・`∫Θ⁴W = 144`・`∫Θ²W² = 48`）。 -/
theorem R10_degree_7560 :
    ((7560:ℚ) ^ 5 / 192 + (7560:ℚ) ^ 5 / 1920) * 720 + ((7560:ℚ) ^ 3 * 19 / 16) * 144
      + (-((7560:ℚ) * 19 ^ 2 / 8)) * 48 = 101866936456329161040 := by norm_num

/-- 次数 12 の要求 `(e^{-A}G)₁₂ = -(A³/6)G₆ - A·G₁₀` の閉じた形と値（`g = 7560`）。 -/
theorem deg12_required :
    -((7560:ℚ) ^ 6 / 1152) * 720 - ((7560:ℚ) ^ 4 * 19 / 96) * 144
      - ((7560:ℚ) ^ 6 / 3840) * 720 + ((7560:ℚ) ^ 2 * 19 ^ 2 / 16) * 48
      = -151689112087438310011200 := by norm_num

theorem deg12_required_closed (g q : ℚ) :
    -(g ^ 6 / 1152) * 720 - (g ^ 4 * q / 96) * 144 - (g ^ 6 / 3840) * 720 + (g ^ 2 * q ^ 2 / 16) * 48
      = -(13 / 16) * g ^ 6 - (3 / 2) * g ^ 4 * q + 3 * g ^ 2 * q ^ 2 := by ring

/-! ### (5) Farkas -/

/-- 線型汎関数が生成元で非負・目標で負なら、目標は生成元の非負結合ではない。 -/
theorem not_in_cone_of_functional {n : ℕ} (ψ : (Fin n → ℚ) → ℚ)
    (hlin : ∀ (y : Fin n → ℚ) (a : Fin n → (Fin n → ℚ)),
      ψ (fun j => ∑ k, y k * a k j) = ∑ k, y k * ψ (a k))
    (a : Fin n → (Fin n → ℚ)) (b : Fin n → ℚ)
    (hpos : ∀ k, 0 ≤ ψ (a k)) (hneg : ψ b < 0) :
    ¬ ∃ y : Fin n → ℚ, (∀ k, 0 ≤ y k) ∧ b = fun j => ∑ k, y k * a k j := by
  rintro ⟨y, hy, hb⟩
  have h1 : ψ b = ∑ k, y k * ψ (a k) := by rw [hb]; exact hlin y a
  have h2 : 0 ≤ ∑ k, y k * ψ (a k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hy k) (hpos k)
  linarith [h1 ▸ hneg]

/-- nef 類との交点数が負なら有効ではない（上の特別な場合の数値の形）。 -/
theorem not_effective_of_neg_degree (d : ℚ) (hd : d < 0) :
    ¬ ∃ (m : ℕ) (c : Fin m → ℚ), (∀ i, 0 ≤ c i) ∧ d = ∑ i, c i := by
  rintro ⟨m, c, hc, hd'⟩
  have : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  linarith [hd' ▸ hd]

/-! ### (6) 貼り合わせの本数の下限 -/

/-- 不足 `d < 0` を一組あたり高々 `m > 0` の有効類で埋めるには `n ≥ (-d)/m` 組必要。 -/
theorem pairs_lower_bound (d m : ℚ) (hd : d < 0) (hm : 0 < m) (n : ℕ)
    (h : 0 ≤ d + (n : ℚ) * m) : (-d) / m ≤ (n : ℚ) := by
  rw [div_le_iff₀ hm]; linarith

/-! ### (7) `σ₂` の上限 -/

theorem sigma2_le_third (x y z g : ℚ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = g) : x * y + y * z + z * x ≤ g ^ 2 / 3 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-! ### (8) 行和 0 の二次形式 -/

/-- `Φ` が対称で行和 0 なら、原子の値 `Σ v_a(1-v_b)Φ_{ab}` は `-vᵗΦv` に一致する。
    ゆえに「立方体 `[0,1]³` の上で非負」は「`Φ ⪯ 0`」と同値になる。 -/
theorem row_sum_zero_quadratic
    (p q r s t u v₁ v₂ v₃ : ℚ)
    (h1 : p + s + t = 0) (h2 : s + q + u = 0) (h3 : t + u + r = 0) :
    (v₁ * (1 - v₁) * p + v₁ * (1 - v₂) * s + v₁ * (1 - v₃) * t
      + v₂ * (1 - v₁) * s + v₂ * (1 - v₂) * q + v₂ * (1 - v₃) * u
      + v₃ * (1 - v₁) * t + v₃ * (1 - v₂) * u + v₃ * (1 - v₃) * r)
    = -(v₁ ^ 2 * p + v₂ ^ 2 * q + v₃ ^ 2 * r
        + 2 * v₁ * v₂ * s + 2 * v₁ * v₃ * t + 2 * v₂ * v₃ * u) := by
  have hp : p = -s - t := by linarith
  have hq : q = -s - u := by linarith
  have hr : r = -t - u := by linarith
  subst hp; subst hq; subst hr; ring

/-! ### 格子の必要条件 -/

theorem degree_sum_7560 : 30 * (7560:ℕ) ^ 3 + 1368 * 7560 = 12962446822080 := by norm_num

theorem gcd_dvd_degree : (90720 : ℕ) ∣ 12962446822080 := ⟨142884114, by norm_num⟩

end CMHodgeIntegralModel

#print axioms CMHodgeIntegralModel.norms_dvd_7560
#print axioms CMHodgeIntegralModel.sden_dvd_7560
#print axioms CMHodgeIntegralModel.not_dvd_4032
#print axioms CMHodgeIntegralModel.g_factorisation
#print axioms CMHodgeIntegralModel.lcm_2520_1080
#print axioms CMHodgeIntegralModel.convex_nonneg
#print axioms CMHodgeIntegralModel.t_value
#print axioms CMHodgeIntegralModel.t_is_square
#print axioms CMHodgeIntegralModel.zeta8_closed
#print axioms CMHodgeIntegralModel.zeta10_closed
#print axioms CMHodgeIntegralModel.zeta12_closed
#print axioms CMHodgeIntegralModel.deg8_from_deg6
#print axioms CMHodgeIntegralModel.R10_coeff_theta5
#print axioms CMHodgeIntegralModel.R10_coeff_theta3W
#print axioms CMHodgeIntegralModel.R10_coeff_thetaW2
#print axioms CMHodgeIntegralModel.R10_degree_7560
#print axioms CMHodgeIntegralModel.deg12_required
#print axioms CMHodgeIntegralModel.deg12_required_closed
#print axioms CMHodgeIntegralModel.not_in_cone_of_functional
#print axioms CMHodgeIntegralModel.not_effective_of_neg_degree
#print axioms CMHodgeIntegralModel.pairs_lower_bound
#print axioms CMHodgeIntegralModel.sigma2_le_third
#print axioms CMHodgeIntegralModel.row_sum_zero_quadratic
#print axioms CMHodgeIntegralModel.degree_sum_7560
#print axioms CMHodgeIntegralModel.gcd_dvd_degree
