/-
  CM 型の退化した例外類 — イデアル層の族を「`gΘ` の因子の中に入れる」ときの、有限の代数だけ

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元・`td(X) = 1`）、`Θ` は積の主偏極。
  `NS(X)⊗Q = Sym²(Q³)` で `D_S` が因子類、`φ_w^*θ₀ = D_{w wᵀ}`。`χ(D_S) = det(S)²`。
  `Z ⊂ D ∈ |gΘ|` を要求すると、Koszul と指数定理から `H⁰(I_Z(gΘ)) = Σᵢ fᵢ·H⁰(gΘ - Cᵢ)` で、
  `H⁰(gΘ - C) ≠ 0` には `gI - C ⪰ 0` が要る。

  この頁で Lean にするのは次の六つで、いずれも**有限の代数の等式・不等式**である。
  幾何・層・コホモロジー・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) Koszul の交代和による条件数：`π` 型の成分 `Θ₁∩Θ₂∩Θ₃`（≅ 種数 2 の曲線の三重積）が
      `|gΘ|` に課す条件の数は `(2g-1)³`。これは `a³ - 3a²b + 3ab² - b³ = (a-b)³`（`a = g²`・`b = (g-1)²`）である。
  (2) 含有可能性の指数条件：`gI - λ·w wᵀ` は `λ|w|² > g` のとき固有値 `g - λ|w|² < 0` を持つ。
      `λ = 64`・`|w|² ≥ 1`・`g = 8` では `8 - 64 < 0`。
  (3) σ の間隙による非可行性：`dₖ > 0`・`yₖ ≥ 0`・`σₖ ≤ σmax < g`・`Σ yₖ dₖ > 0` なら
      `Σ yₖ dₖ (σₖ - g) < 0` で、次数 8 の要求 `Σ yₖ dₖ (σₖ - g) = 2E`（`E ≥ 0`）と矛盾する。
  (4) `ΣSᵢ = gI` の場合の恒等式：adjunction 乗数が `gΘ` に一致すると、次数 8 の要求は
      次数 6 の等式から**自動で**従う（余次元 4 の補正は不要）。
  (5) 条件の数と切断の数の比：`(g³/6)(30g³ + 1368g) > g⁶`（すべての `g ≥ 1`）。漸近比は `5 + 228/g²`。
  (6) `R₁₀` の閉じた形の係数（`g = 8`・`A = 4Θ`）：`8·(g³/24) + g⁵/1920 = 2816/15`・`8·(gq/2) = 608`・
      `-(g q²/8) = -361`、および `π_alg ≠ π_geo`（`⟨π_geo,π_geo⟩ = 8` だが `⟨π_alg,π_geo⟩ = 128/19`）。
-/
import Mathlib

namespace CMHodgeIdealInDivisor

/-! ### (1) Koszul の交代和 = 条件の数 -/

/-- 三つの立方の差の恒等式。`(a-b)³ = a³ - 3a²b + 3ab² - b³`。 -/
theorem cube_alt_sum (a b : ℚ) : a^3 - 3*a^2*b + 3*a*b^2 - b^3 = (a - b)^3 := by ring

/-- `π` 型の成分 `Θ₁∩Θ₂∩Θ₃` が `|gΘ|` に課す条件の数は Koszul の交代和
`det(gI)² - 3det(gI-E₁)² + 3det(gI-E₁-E₂)² - det(gI-E₁-E₂-E₃)²`
`= (g³)² - 3((g-1)g²)² + 3((g-1)²g)² - ((g-1)³)²` で、これは `(2g-1)³` に等しい。
（幾何の側では種数 2 の曲線の `h⁰(8K) = 15` の三重積。`g = 8` で `15³ = 3375`。） -/
theorem koszul_condition_count (g : ℚ) :
    (g^3)^2 - 3*((g-1)*g^2)^2 + 3*((g-1)^2*g)^2 - ((g-1)^3)^2 = (2*g - 1)^3 := by
  ring

theorem koszul_condition_count_g8 :
    ((8:ℚ)^3)^2 - 3*((8-1)*8^2)^2 + 3*((8-1)^2*8)^2 - ((8-1)^3)^2 = 3375 := by norm_num

/-- `h⁰(X, gΘ) = det(gI)² = g⁶`。`g = 8` で `262144`。 -/
theorem h0_gTheta : ((8:ℚ)^3)^2 = 262144 := by norm_num

/-! ### (2) 含有可能性の指数条件 -/

/-- `gI - C`（`C = λ w wᵀ`・`|w|² = n`）は固有値 `g - λ n` を持つ。`λ n > g` なら負。 -/
theorem index_negative {g lam n : ℚ} (h : g < lam * n) : g - lam * n < 0 := by linarith

/-- 次数 8 の証明書：`λ = 64`・`|v|² ≥ 1`・`g = 8`。 -/
theorem lambda64_fails {n : ℚ} (hn : 1 ≤ n) : (8:ℚ) - 64 * n < 0 := by nlinarith

/-- 逆向き：含有可能な成分は `|w|² ≤ g` を満たす向きを持つ。 -/
theorem thin_iff {g n : ℚ} (hg : 0 < g) : (0 ≤ g - n) ↔ n ≤ g := by constructor <;> intro h <;> linarith

/-! ### (3) σ の間隙による非可行性（次数 8 の要求が満たせないこと） -/

/-- 二つの成分の場合の芯：`σᵢ ≤ σmax < g`・`dᵢ > 0`・`yᵢ ≥ 0`・`y₁d₁ + y₂d₂ > 0` なら
`y₁d₁(σ₁-g) + y₂d₂(σ₂-g) < 0`。右辺は `2E ≥ 0` なので矛盾する。 -/
theorem sigma_gap_two {y₁ y₂ d₁ d₂ σ₁ σ₂ σmax g E : ℚ}
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hs₁ : σ₁ ≤ σmax) (hs₂ : σ₂ ≤ σmax) (hmax : σmax < g)
    (hpos : 0 < y₁ * d₁ + y₂ * d₂) (hE : 0 ≤ E)
    (heq : y₁ * d₁ * (σ₁ - g) + y₂ * d₂ * (σ₂ - g) = 2 * E) : False := by
  nlinarith [mul_nonneg hy₁ hd₁.le, mul_nonneg hy₂ hd₂.le,
             mul_nonneg (mul_nonneg hy₁ hd₁.le) (sub_nonneg.mpr hs₁),
             mul_nonneg (mul_nonneg hy₂ hd₂.le) (sub_nonneg.mpr hs₂)]

/-- `g = 8` の階数 1 の原子族での実測 `σmax = 20/3`：間隙は `4/3`。 -/
theorem sigma_gap_g8 : (20:ℚ)/3 < 8 ∧ (8:ℚ) - 20/3 = 4/3 := by norm_num

/-! ### (4) `ΣSᵢ = gI` なら次数 8 は次数 6 から自動で従う -/

/-- adjunction の乗数が `gθ` に一致する場合、各成分の次数 8 の寄与は
`-(1/2)·zₖ·(gθ)` で、和は `-(g/2)θ·(Σ yₖ zₖ)`。すなわち次数 6 の等式
`Σ yₖ zₖ = G` から次数 8 の要求 `Σ yₖ ζₖ = -(g/2)θG` が**余次元 4 の補正なしで**従う。 -/
theorem deg8_from_deg6 (g θ G y₁ y₂ z₁ z₂ : ℚ)
    (hsum : y₁ * z₁ + y₂ * z₂ = G) :
    y₁ * (-(1/2) * z₁ * (g * θ)) + y₂ * (-(1/2) * z₂ * (g * θ)) = -(g/2) * θ * G := by
  rw [← hsum]; ring

/-- 三つの因子の類が `gI` に足し合わさること（`S₁+S₂+S₃ = gI`）は、乗数がちょうど `gΘ` になること
と同値で、そのとき `σ = g`（等号）である。 -/
theorem sigma_eq_g_of_sum {s₁ s₂ s₃ g d : ℚ} (hd : 0 < d) (h : s₁ + s₂ + s₃ = g * d) :
    (s₁ + s₂ + s₃) / d = g := by
  rw [h]; field_simp

/-! ### (5) 条件の数と切断の数 -/

/-- 表示に依らない漸近比：条件の数の主要項は `(g³/6)·J₆ = (g³/6)(30g³+1368g) = 5g⁶ + 228g⁴`、
切断は `g⁶`。ゆえに比は `5 + 228/g²` で、**すべての `g > 0` で 1 より大きい**。 -/
theorem conditions_exceed_sections {g : ℚ} (hg : 0 < g) :
    g^6 < (g^3/6) * (30*g^3 + 1368*g) := by
  nlinarith [pow_pos hg 6, pow_pos hg 4, sq_nonneg g]

theorem conditions_ratio (g : ℚ) (hg : 0 < g) :
    ((g^3/6) * (30*g^3 + 1368*g)) / g^6 = 5 + 228 / g^2 := by
  have h : g ≠ 0 := ne_of_gt hg
  field_simp; ring

/-- `g = 8` での実測比（次数 8 の証明書の 28 成分の厳密な条件数の和 `16192522880/8677`）。 -/
theorem ratio_g8 : (16192522880:ℚ)/8677 / 262144 > 7 := by norm_num

/-! ### (6) `R₁₀` の係数と `π_alg ≠ π_geo` -/

/-- `R₁₀ = (A²/2)G₆ + G₁₀`（`A = (g/2)Θ`・`g = 8`）の閉じた形の三つの係数。 -/
theorem R10_coeffs :
    (8:ℚ) * ((8:ℚ)^3/24) + (8:ℚ)^5/1920 = 2816/15 ∧
    (8:ℚ) * ((8:ℚ)*19/2) = 608 ∧
    -((8:ℚ)*19^2/8) = -361 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- `∫R₁₀·Θ = 205392`（`∫Θ⁶ = 720`・`∫Θ⁴W = 144`・`∫Θ²W² = 48` から）。 -/
theorem R10_degree :
    (2816:ℚ)/15 * 720 + 608 * 144 + (-361) * 48 = 205392 := by norm_num

/-- `π_alg := (Θ³-3ΘW)/6` と `π_geo := Θ₁Θ₂Θ₃` は、自己交叉（ともに 8）も `Θ³` との対（ともに 48）も
一致するが、互いの対は `128/19` である。ゆえに**同じ類ではない**（双線型形式の一般論）。 -/
theorem pi_alg_ne_pi_geo {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (a b : V)
    (h₁ : B b b = 8) (h₂ : B a b = 128/19) : a ≠ b := by
  intro h; rw [h] at h₂; rw [h₁] at h₂; norm_num at h₂

/-- 実際の数の食い違い。 -/
theorem pi_pairing_mismatch : (128:ℚ)/19 ≠ 8 := by norm_num

end CMHodgeIdealInDivisor

#print axioms CMHodgeIdealInDivisor.cube_alt_sum
#print axioms CMHodgeIdealInDivisor.koszul_condition_count
#print axioms CMHodgeIdealInDivisor.koszul_condition_count_g8
#print axioms CMHodgeIdealInDivisor.h0_gTheta
#print axioms CMHodgeIdealInDivisor.index_negative
#print axioms CMHodgeIdealInDivisor.lambda64_fails
#print axioms CMHodgeIdealInDivisor.thin_iff
#print axioms CMHodgeIdealInDivisor.sigma_gap_two
#print axioms CMHodgeIdealInDivisor.sigma_gap_g8
#print axioms CMHodgeIdealInDivisor.deg8_from_deg6
#print axioms CMHodgeIdealInDivisor.sigma_eq_g_of_sum
#print axioms CMHodgeIdealInDivisor.conditions_exceed_sections
#print axioms CMHodgeIdealInDivisor.conditions_ratio
#print axioms CMHodgeIdealInDivisor.ratio_g8
#print axioms CMHodgeIdealInDivisor.R10_coeffs
#print axioms CMHodgeIdealInDivisor.R10_degree
#print axioms CMHodgeIdealInDivisor.pi_alg_ne_pi_geo
#print axioms CMHodgeIdealInDivisor.pi_pairing_mismatch
