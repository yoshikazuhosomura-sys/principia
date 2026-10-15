/-
  一次元の鎖の Poincaré 定数を、8 サイトごとの区切り（粗い鎖）と、間の長さ 7 の凸な塊に分けて出す議論の、
  有限次元の代数の部分。
  (1) 一次元の共分散の比較（二重和の形）：0 ≤ (x_i-x_j)(φ_i-φ_j) ≤ c(x_i-x_j)² なら Σ p p (x-x)(φ-φ) ≤ c Σ p p (x-x)²。
  (2) 影響係数の評価の一行、(3) 三項の二乗、(4) 交差項、(5) 粗いサイトについての和、(6) 二層の合成、
  (7) 一サイトの熱浴の経路結合の一歩と縮小からの Poincaré、(8) 塊の端の Green 関数の連分数の値と合成の定数。
  解析の部分（Bakry–Émery・Brascamp–Lieb・FKG・Ollivier・微分の式・Fubini・連分数と逆行列の一致）は含まない。
-/
import Mathlib

namespace LatticeGauge.CoarseChainPoincare

open Finset

/-- 一次元の共分散の比較の二重和の形。 -/
theorem cov_le_lip_var {ι : Type*} (s : Finset ι) (p x φ : ι → ℝ) (c : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (x i - x j) * (φ i - φ j))
    (hlip : ∀ i ∈ s, ∀ j ∈ s, (x i - x j) * (φ i - φ j) ≤ c * (x i - x j) ^ 2) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, p i * p j * ((x i - x j) * (φ i - φ j)) ∧
    ∑ i ∈ s, ∑ j ∈ s, p i * p j * ((x i - x j) * (φ i - φ j)) ≤
      c * ∑ i ∈ s, ∑ j ∈ s, p i * p j * (x i - x j) ^ 2 := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hp i hi) (hp j hj)) (hmono i hi j hj)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hpp : 0 ≤ p i * p j := mul_nonneg (hp i hi) (hp j hj)
    have h := mul_le_mul_of_nonneg_left (hlip i hi j hj) hpp
    calc p i * p j * ((x i - x j) * (φ i - φ j)) ≤ p i * p j * (c * (x i - x j) ^ 2) := h
      _ = c * (p i * p j * (x i - x j) ^ 2) := by ring

/-- 影響係数 ρ = Cov/(εħ) の評価の一行：Cov ≤ c·Var なら ρ ≤ c·Var/(εħ)。 -/
theorem influence_le (cov var c e h : ℝ) (he : 0 < e) (hh : 0 < h) (hcov : cov ≤ c * var) :
    cov / (e * h) ≤ c * (var / (e * h)) := by
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right hcov (by positivity)

/-- 三項の二乗。 -/
theorem sq_three (u v w : ℝ) : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w)]

/-- 交差項：c² ≤ V_f V_h、V_f ≤ (ħ/κ)A、V_h ≤ ħ g なら (c/(εħ))² ≤ g A/(ε² κ)。 -/
theorem cross_term (c Vf Vh A g e h k : ℝ) (he : 0 < e) (hh : 0 < h) (hk : 0 < k)
    (hcs : c ^ 2 ≤ Vf * Vh) (hVf0 : 0 ≤ Vf) (hVf : Vf ≤ (h / k) * A)
    (hVh0 : 0 ≤ Vh) (hVh : Vh ≤ h * g) :
    (c / (e * h)) ^ 2 ≤ g * A / (e ^ 2 * k) := by
  have hA : 0 ≤ (h / k) * A := le_trans hVf0 hVf
  have h1 : Vf * Vh ≤ ((h / k) * A) * (h * g) := mul_le_mul hVf hVh hVh0 hA
  have h2 : ((h / k) * A) * (h * g) = h ^ 2 * (g * A / k) := by
    field_simp
  have h3 : c ^ 2 ≤ h ^ 2 * (g * A / k) := by linarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc c ^ 2 * (e ^ 2 * k) ≤ h ^ 2 * (g * A / k) * (e ^ 2 * k) := by
        apply mul_le_mul_of_nonneg_right h3
        positivity
    _ = g * A * (e * h) ^ 2 := by
        field_simp

/-- 粗いサイトについての和：各塊は高々二つの粗いサイトに接する。 -/
theorem coarse_grad_sum {ι : Type*} (s : Finset ι) (G B Al Ar : ι → ℝ) (c A : ℝ) (hc : 0 ≤ c)
    (hG : ∀ m ∈ s, G m ≤ 3 * B m + c * (Al m + Ar m))
    (hA : ∑ m ∈ s, (Al m + Ar m) ≤ 2 * A) :
    ∑ m ∈ s, G m ≤ 3 * ∑ m ∈ s, B m + 2 * c * A := by
  have h1 : ∑ m ∈ s, G m ≤ ∑ m ∈ s, (3 * B m + c * (Al m + Ar m)) := Finset.sum_le_sum hG
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 : c * ∑ m ∈ s, (Al m + Ar m) ≤ c * (2 * A) := mul_le_mul_of_nonneg_left hA hc
  linarith

/-- 二層の合成：Var = E₁ + V₂、E₁ ≤ a₁ D_x、V₂ ≤ C_c (3 D_y + c₆ D_x)、c₆ ≥ 3 なら Var ≤ (a₁ + C_c c₆)(D_x + D_y)。 -/
theorem two_level_assembly (Var E1 V2 a1 Cc c6 Dx Dy : ℝ)
    (hsplit : Var = E1 + V2) (hE1 : E1 ≤ a1 * Dx) (hV2 : V2 ≤ Cc * (3 * Dy + c6 * Dx))
    (hCc : 0 ≤ Cc) (hc6 : 3 ≤ c6) (hDy : 0 ≤ Dy) (ha1 : 0 ≤ a1) :
    Var ≤ (a1 + Cc * c6) * (Dx + Dy) := by
  have h0 : 3 * Dy ≤ c6 * Dy := mul_le_mul_of_nonneg_right hc6 hDy
  have h1 : Cc * (3 * Dy) ≤ Cc * (c6 * Dy) := mul_le_mul_of_nonneg_left h0 hCc
  have h2 : a1 * Dx ≤ a1 * (Dx + Dy) := mul_le_mul_of_nonneg_left (by linarith) ha1
  calc Var = E1 + V2 := hsplit
    _ ≤ a1 * Dx + Cc * (3 * Dy + c6 * Dx) := add_le_add hE1 hV2
    _ = a1 * Dx + Cc * (3 * Dy) + Cc * (c6 * Dx) := by ring
    _ ≤ a1 * (Dx + Dy) + Cc * (c6 * Dy) + Cc * (c6 * Dx) := by linarith
    _ = (a1 + Cc * c6) * (Dx + Dy) := by ring

/-- 一サイトの熱浴の経路結合の一歩（M 個の粗いサイト、隣への影響の和 ρ）。 -/
theorem path_coupling_site (M ρ d : ℝ) (hM : 0 < M) :
    (1 - 1 / M) * d + ρ * d / M = (1 - (1 - ρ) / M) * d := by
  field_simp
  ring

/-- 縮小率 (1-ρ)/M の隙間と一サイトの Poincaré（定数 C）から、粗い鎖の Poincaré C/(1-ρ)。M は消える。 -/
theorem poincare_of_site_contraction {ι : Type*} (s : Finset ι) (v e : ι → ℝ)
    (M C ρ Var E : ℝ) (hM : 0 < M) (hρ : ρ < 1)
    (hgap : ((1 - ρ) / M) * Var ≤ (1 / M) * ∑ m ∈ s, v m)
    (hv : ∀ m ∈ s, v m ≤ C * e m) (he : ∑ m ∈ s, e m = E) :
    Var ≤ C / (1 - ρ) * E := by
  have hsum : ∑ m ∈ s, v m ≤ C * E := by
    rw [← he, Finset.mul_sum]
    exact Finset.sum_le_sum hv
  have h1 : 0 < 1 - ρ := by linarith
  have key : (1 - ρ) * Var ≤ C * E := by
    have h3 : ((1 - ρ) / M) * Var = ((1 - ρ) * Var) / M := by ring
    have h4 : (1 / M) * ∑ m ∈ s, v m = (∑ m ∈ s, v m) / M := by ring
    rw [h3, h4] at hgap
    have h5 := (div_le_div_iff_of_pos_right hM).mp hgap
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  linarith

/-- 合成：C_c = C_site/(1-ρ) を入れた形。 -/
theorem coarse_chain_poincare (Var E1 V2 a1 Csite ρ c6 Dx Dy : ℝ)
    (hsplit : Var = E1 + V2) (hE1 : E1 ≤ a1 * Dx)
    (hV2 : V2 ≤ (Csite / (1 - ρ)) * (3 * Dy + c6 * Dx))
    (hCs : 0 ≤ Csite) (hρ : ρ < 1) (hc6 : 3 ≤ c6) (hDy : 0 ≤ Dy) (ha1 : 0 ≤ a1) :
    Var ≤ (a1 + c6 * Csite / (1 - ρ)) * (Dx + Dy) := by
  have hCc : 0 ≤ Csite / (1 - ρ) := div_nonneg hCs (by linarith)
  have h := two_level_assembly Var E1 V2 a1 (Csite / (1 - ρ)) c6 Dx Dy hsplit hE1 hV2 hCc hc6 hDy ha1
  calc Var ≤ (a1 + Csite / (1 - ρ) * c6) * (Dx + Dy) := h
    _ = (a1 + c6 * Csite / (1 - ρ)) * (Dx + Dy) := by ring

/-- 長さ 7 の塊の端の対角成分 (M⁻¹)₁₁、M = 2T₇ - (1/4)I の三重対角の Schur の漸化（連分数）の値。 -/
theorem g7_value :
    (1 : ℝ) / (15/4 - 4/(15/4 - 4/(15/4 - 4/(15/4 - 4/(15/4 - 4/(15/4 - 4/(15/4))))))) =
      1832324 / 1770735 := by
  norm_num

theorem g7_lt : (1832324 : ℝ) / 1770735 < 1035 / 1000 := by norm_num

/-- 合成の定数 6g/(ε²κ₀) < 497（g ≤ 1.035・κ₀ > 1/20・ε = 1/2）。 -/
theorem assembly_const (g k : ℝ) (hg : g ≤ 1035 / 1000) (hk : 1 / 20 < k) :
    6 * g / ((1 / 2) ^ 2 * k) < 497 := by
  have hkpos : 0 < k := by linarith
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

end LatticeGauge.CoarseChainPoincare

#print axioms LatticeGauge.CoarseChainPoincare.cov_le_lip_var
#print axioms LatticeGauge.CoarseChainPoincare.influence_le
#print axioms LatticeGauge.CoarseChainPoincare.sq_three
#print axioms LatticeGauge.CoarseChainPoincare.cross_term
#print axioms LatticeGauge.CoarseChainPoincare.coarse_grad_sum
#print axioms LatticeGauge.CoarseChainPoincare.two_level_assembly
#print axioms LatticeGauge.CoarseChainPoincare.path_coupling_site
#print axioms LatticeGauge.CoarseChainPoincare.poincare_of_site_contraction
#print axioms LatticeGauge.CoarseChainPoincare.coarse_chain_poincare
#print axioms LatticeGauge.CoarseChainPoincare.g7_value
#print axioms LatticeGauge.CoarseChainPoincare.g7_lt
#print axioms LatticeGauge.CoarseChainPoincare.assembly_const
