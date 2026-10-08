/-
  CM 型の退化した例外類 — イデアル層の族の Todd 補正の論理の芯（有限の代数だけ）

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元・`td(X) = 1`）、`Θ` は積の主偏極、
  `W := Θ ∧_{F₀} Θ`、`β := Θ·exp(-(q/2)W)`、`q = 19`。`D ∈ |gΘ|`・`A = D_S`・`Z ⊂ D` として
  `Ψ := (1-e^{-gΘ}) - g·β·e^{-A}`。Grothendieck–Riemann–Roch と `td(X) = 1` から
  `e^{-A}·ch(i_*O_Z(A)) = i_*td(Z)` で、要求は `Ψ_{2c} = (i_*td(Z))_{2c}`（`c = 2,3,4`）である。

  この頁で Lean にするのは次の七つで、いずれも**有限の代数の等式・不等式**である。
  幾何・層・変形理論・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) `2 sinh(gΘ/2)` の次数 3 の係数は `g³/24`（`(1-e^{-gΘ})e^{gΘ/2} = e^{gΘ/2}-e^{-gΘ/2}`）。
  (2) `∫G₆Θ³ = 30g³ + 1368g`（`∫Θ⁶ = 720`・`∫Θ⁴W = 144` から）。
  (3) 等方な場合（`S = (g/2)I`・`A = (g/2)Θ`）の `J₆`・`J₈` の値と、**恒等式 `J₈ = -(g/2)·J₆`**。
      これは「次数 8 の要求は次数 6 の類に `-(1/2)A` を掛けたもの」＝完全交叉の adjunction の形である。
  (4) 三重完全交叉の Todd 補正（adjunction）の代数の芯：
      `-(1/2)(c₁²c₂c₃+c₁c₂²c₃+c₁c₂c₃²) = -(1/2)(c₁c₂c₃)(c₁+c₂+c₃)`。
  (5) 階数 2 の nef 束の Schur 非負性の使い方：`0 ≤ c₂ ≤ c₁²` なら `0 ≤ 2c₁² - c₂`
      （余次元 2 の `Z` の次数 8 の補正 `(1/12)i_*(2c₁(N)²-c₂(N))` の符号）。
  (6) Khovanskii–Teissier の対数凹性から出る必要不等式：
      `J₄·(12J₈ + C₂) ≤ 8J₆²`（`C₂ = ∫Ψ₄²Θ²`・`J₆ = -(1/2)∫K_Zθ³`）。
  (7) **Todd 補正が先行の障害を無効にすること**：純余次元 2 の滑らかな `Z` では要求が
      `J₆ ≤ 0`・`J₈ ≥ 0` に反転するので、先行の `psd_obstruction`（`J₄ ≥ 0 ∧ J₆ ≥ 0 ⟹ J₈ < 0`）の
      前提が成り立たない。領域 `{s ≥ 0, J₄ ≥ 0, J₆ ≤ 0, J₈ ≥ 0, (6) の不等式}` は空でない
      （`g = 1`・`S = (17/5)I` の証人）。
-/
import Mathlib

namespace CMHodgeToddSecant

/-! ### 記号：`J` の閉じた形（先行の `∫` から） -/

/-- `J₄/g = 240e₁ - 360g` -/
def J4 (g e₁ : ℚ) : ℚ := g*(240*e₁ - 360*g)
/-- `J₆/g = 120g² - 24(e₁²+2e₂) + 1368` -/
def J6 (g e₁ e₂ : ℚ) : ℚ := g*(120*g^2 - 24*(e₁^2 + 2*e₂) + 1368)
/-- `J₈/g = -30g³ + 12(e₁e₂+e₃) - 456e₁` -/
def J8 (g e₁ e₂ e₃ : ℚ) : ℚ := g*(-30*g^3 + 12*(e₁*e₂ + e₃) - 456*e₁)

/-! ### (1) `2 sinh(gΘ/2)` の次数 3 の係数 -/

theorem sinh_deg3_coeff (g : ℚ) : 2*((g/2)^3/6) = g^3/24 := by ring

theorem sinh_deg1_coeff (g : ℚ) : 2*(g/2) = g := by ring

/-! ### (2) `∫G₆Θ³ = 30g³ + 1368g`（`G₆ = (g³/24)Θ³ + (19g/2)ΘW`） -/

theorem G6_pairing (g : ℚ) : (g^3/24)*720 + (19*g/2)*144 = 30*g^3 + 1368*g := by ring

/-! ### (3) 等方な場合の `J₆`・`J₈` と恒等式 `J₈ = -(g/2)J₆` -/

theorem isotropic_J6 (g : ℚ) :
    J6 g (3*g/2) (3*g^2/4) = g*(30*g^2 + 1368) := by
  unfold J6; ring

theorem isotropic_J8 (g : ℚ) :
    J8 g (3*g/2) (3*g^2/4) (g^3/8) = g*(-15*g^3 - 684*g) := by
  unfold J8; ring

/-- 等方な場合、次数 8 の要求は次数 6 の要求に `-(g/2)` を掛けたものである。
    これは `Ψ₈ = -(1/2)A·Ψ₆`（`A = (g/2)Θ`）の `∫·Θ²` 版で、完全交叉の adjunction の形。 -/
theorem isotropic_todd_ratio (g : ℚ) :
    J8 g (3*g/2) (3*g^2/4) (g^3/8) = -(g/2) * J6 g (3*g/2) (3*g^2/4) := by
  unfold J6 J8; ring

/-- 等方な場合の `J₄` は 0（`Ψ₄ = 0`・`Z` は純余次元 ≥ 3）。 -/
theorem isotropic_J4 (g : ℚ) : J4 g (3*g/2) = 0 := by unfold J4; ring

/-- 先行の `isotropic_obstruction` と整合：`g > 0` なら等方な場合の `J₈ < 0`。
    先行の議論ではこれが矛盾だったが、Todd 補正の下では**これが要求そのもの**である。 -/
theorem isotropic_J8_neg {g : ℚ} (hg : 0 < g) :
    J8 g (3*g/2) (3*g^2/4) (g^3/8) < 0 := by
  rw [isotropic_J8]
  have h : -15*g^3 - 684*g < 0 := by nlinarith [pow_pos hg 3, sq_nonneg g]
  exact mul_neg_of_pos_of_neg hg h

/-! ### (4) 三重完全交叉の Todd 補正（adjunction）の代数 -/

theorem adjunction_deg4 (c₁ c₂ c₃ : ℚ) :
    -(1/2)*(c₁^2*c₂*c₃ + c₁*c₂^2*c₃ + c₁*c₂*c₃^2)
      = -(1/2)*(c₁*c₂*c₃)*(c₁+c₂+c₃) := by ring

/-- 二重完全交叉（余次元 2）の Todd 補正：次数 6 の係数は `-(1/2)c₁c₂(c₁+c₂)`。 -/
theorem adjunction_deg3 (c₁ c₂ : ℚ) :
    -(1/2)*(c₁^2*c₂ + c₁*c₂^2) = -(1/2)*(c₁*c₂)*(c₁+c₂) := by ring

/-! ### (5) 階数 2 の nef 束の Schur 非負性の使い方 -/

theorem fl_rank2 {c1sq c2 : ℚ} (h0 : 0 ≤ c2) (h1 : c2 ≤ c1sq) :
    0 ≤ 2*c1sq - c2 := by linarith

/-! ### (6) Khovanskii–Teissier から出る必要不等式 -/

/-- 純余次元 2 の滑らかな `Z` では `J₆ = -(1/2)k₃`（`k₃ = ∫K_Zθ³ ≥ 0`）、
    `12J₈ = 2K₂ - C₂`（`K₂ = ∫c₁(N)²θ²`・`C₂ = ∫c₂(N)θ² = ∫Ψ₄²Θ²`）で、
    対数凹性 `a·K₂ ≤ k₃²`（`a = J₄ = ∫θ⁴`）から `J₄(12J₈ + C₂) ≤ 8J₆²`。 -/
theorem kt_obstruction {a K2 C2 k3 J6v J8v : ℚ}
    (ha : 0 ≤ a) (hlc : a*K2 ≤ k3^2) (hk : k3 = -2*J6v) (hJ8 : 12*J8v = 2*K2 - C2) :
    a*(12*J8v + C2) ≤ 8*J6v^2 := by
  have h1 : a*(12*J8v + C2) = 2*(a*K2) := by rw [hJ8]; ring
  have h2 : k3^2 = 4*J6v^2 := by rw [hk]; ring
  nlinarith [hlc, h1, h2]

/-! ### (7) Todd 補正の下での領域は空でない（`g = 1`・`S = (17/5)I` の証人） -/

/-- 純余次元 2 の滑らかな `Z` の必要条件は `J₄ ≥ 0`・`J₆ ≤ 0`（`K_Z` は nef）・
    `J₈ ≥ 0`（Schur 非負性）である。先行の障害は `J₆ ≥ 0` を仮定していたので効かない。
    証人：`g = 1`・`S = (17/5)I`（`e₁ = 51/5`・`e₂ = 867/25`・`e₃ = 4913/125`）。 -/
theorem todd_region_nonempty :
    0 ≤ J4 1 (51/5) ∧ J6 1 (51/5) (867/25) ≤ 0 ∧ 0 ≤ J8 1 (51/5) (867/25) (4913/125) := by
  refine ⟨by unfold J4; norm_num, by unfold J6; norm_num, by unfold J8; norm_num⟩

/-- その証人は (6) の不等式も満たす（`C₂ = 720u²g²`・`u = t - g/2 = 29/10`）。
    ゆえに Khovanskii–Teissier の不等式はこの領域を閉じない。 -/
theorem witness_satisfies_kt :
    J4 1 (51/5) * (12 * J8 1 (51/5) (867/25) (4913/125) + 720*(29/10)^2)
      ≤ 8 * (J6 1 (51/5) (867/25))^2 := by
  unfold J4 J6 J8; norm_num

/-- 先行の障害の前提（`J₆ ≥ 0`）はこの証人では破れている。 -/
theorem witness_breaks_416_hypothesis : ¬ (0 ≤ J6 1 (51/5) (867/25)) := by
  unfold J6; norm_num

end CMHodgeToddSecant

#print axioms CMHodgeToddSecant.sinh_deg3_coeff
#print axioms CMHodgeToddSecant.G6_pairing
#print axioms CMHodgeToddSecant.isotropic_J6
#print axioms CMHodgeToddSecant.isotropic_J8
#print axioms CMHodgeToddSecant.isotropic_todd_ratio
#print axioms CMHodgeToddSecant.isotropic_J4
#print axioms CMHodgeToddSecant.isotropic_J8_neg
#print axioms CMHodgeToddSecant.adjunction_deg4
#print axioms CMHodgeToddSecant.adjunction_deg3
#print axioms CMHodgeToddSecant.fl_rank2
#print axioms CMHodgeToddSecant.kt_obstruction
#print axioms CMHodgeToddSecant.todd_region_nonempty
#print axioms CMHodgeToddSecant.witness_satisfies_kt
#print axioms CMHodgeToddSecant.witness_breaks_416_hypothesis
