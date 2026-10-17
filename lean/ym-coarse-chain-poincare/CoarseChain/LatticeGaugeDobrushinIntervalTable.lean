/-
0+1 次元の二重井戸の粗い鎖の Dobrushin の影響 ρ(ħ) を、ħ の区間の表から窓の全体へ組み立てる代数の核。
本文：`millennium/bin-813-part10-dobrushin-intervals.md`（(A) 中心形・(B) 区間の表・(C) 判定）。
ここにあるもの：
* 中心形の恒等式 `centered_split`（傾き λG を基準のガウス・(λ−λ₀)G・λ₀(M − e) に分ける）と、
  幾何平均 λ₀ の周りの払い `geomean_dev`（λ₀² = λ₁λ₂・λ₁ = λ₂(1+δ) なら λ ∈ [λ₂,λ₁] で |λ − λ₀| ≤ (δ/2)λ₀）。
* 区間の積の角の上界 `mul_le_corners`（中心形の角の最大の正しさ）。
* 端点の値からの増え方 `steps_growth`・`one_add_pow_le_exp`（一歩ごとに (1+η) 倍以内なら k 歩で (1+η)^k ≤ exp(kη) 倍以内）。
* 区間の数 `geometric_cover_count`（h_{i+1} ≥ q·h_i なら h_m ≥ q^m·h_0）。
* 表の組み立て `cover_le`・`window_le_of_interval_table`・`column_lt_one_of_table`
  （各区間で ρ ≤ B_i を仮定に置き、窓の全体で ρ ≤ B、2B < 1 なら列和 ≤ 2ρ < 1）。
Lean の外：各区間の B_i そのもの（倍精度＋外向きの余裕の計算の出力・区間演算ではない）、補題 R・M の解析、
erf の閉じた式、b と u の尤度比の順序、CDF の上下から k の上下（有限版は既存の `LatticeGaugeInfluenceRecursion`）。
-/
import Mathlib

namespace LatticeGauge.DobrushinIntervalTable

/-- 中心形の恒等式：λG = λ₀(u − 2w) + (λ − λ₀)G + λ₀(M − e)、ただし G = u − 2w + M − e。 -/
theorem centered_split (lam lam0 u w M e : ℝ) :
    lam * (u - 2 * w + M - e) = lam0 * (u - 2 * w) + (lam - lam0) * (u - 2 * w + M - e) + lam0 * (M - e) := by
  ring

/-- 平方の比較から大小（仮定：0 ≤ y・x² ≤ y²）。 -/
theorem le_of_sq_le_sq_nonneg (x y : ℝ) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hc
  have hc' : y < x := lt_of_not_ge hc
  nlinarith [mul_pos (sub_pos.2 hc') (by linarith : (0 : ℝ) < x + y)]

/-- 幾何平均の周りの払い（仮定：0 < λ₂・0 ≤ δ・λ₁ = λ₂(1+δ)・0 ≤ λ₀・λ₀² = λ₁λ₂・λ₂ ≤ λ ≤ λ₁）：
`λ − λ₀ ≤ (δ/2)λ₀` かつ `λ₀ − λ ≤ (δ/2)λ₀`。 -/
theorem geomean_dev (lam1 lam2 lam0 lam δ : ℝ) (h2 : 0 < lam2) (hδ : 0 ≤ δ) (h1 : lam1 = lam2 * (1 + δ))
    (h0 : 0 ≤ lam0) (hsq : lam0 ^ 2 = lam1 * lam2) (hl : lam2 ≤ lam) (hu : lam ≤ lam1) :
    lam - lam0 ≤ δ / 2 * lam0 ∧ lam0 - lam ≤ δ / 2 * lam0 := by
  have hs : lam0 ^ 2 = lam2 ^ 2 * (1 + δ) := by rw [hsq, h1]; ring
  have hge : lam2 ≤ lam0 := le_of_sq_le_sq_nonneg lam2 lam0 h0 (by rw [hs]; nlinarith [sq_nonneg lam2])
  have hle : lam0 ≤ lam2 * (1 + δ / 2) :=
    le_of_sq_le_sq_nonneg lam0 (lam2 * (1 + δ / 2)) (by positivity) (by rw [hs]; nlinarith [sq_nonneg lam2, sq_nonneg δ, mul_nonneg (sq_nonneg lam2) (sq_nonneg δ)])
  have hup : lam2 * (1 + δ) ≤ lam0 * (1 + δ / 2) := by
    apply le_of_sq_le_sq_nonneg _ _ (by positivity)
    have : (lam0 * (1 + δ / 2)) ^ 2 = lam2 ^ 2 * (1 + δ) * (1 + δ / 2) ^ 2 := by rw [mul_pow, hs]
    rw [this]
    have hq : (1 + δ) ≤ (1 + δ / 2) ^ 2 := by nlinarith [sq_nonneg δ]
    have hp : 0 ≤ lam2 ^ 2 * (1 + δ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq hp]
  constructor
  · nlinarith
  · nlinarith

/-- 区間の積の角の上界：a ∈ [a₁,a₂]・g ∈ [g₁,g₂] なら a·g は四つの角の最大以下（中心形の角の最大の正しさ）。 -/
theorem mul_le_corners (a a1 a2 g g1 g2 : ℝ) (ha1 : a1 ≤ a) (ha2 : a ≤ a2) (hg1 : g1 ≤ g) (hg2 : g ≤ g2) :
    a * g ≤ max (max (a1 * g1) (a1 * g2)) (max (a2 * g1) (a2 * g2)) := by
  rcases le_total 0 g with hg | hg
  · have : a * g ≤ a2 * g := mul_le_mul_of_nonneg_right ha2 hg
    rcases le_total 0 a2 with ha | ha
    · have : a2 * g ≤ a2 * g2 := mul_le_mul_of_nonneg_left hg2 ha
      exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))
    · have : a2 * g ≤ a2 * g1 := mul_le_mul_of_nonpos_left hg1 ha
      exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
  · have : a * g ≤ a1 * g := mul_le_mul_of_nonpos_right ha1 hg
    rcases le_total 0 a1 with ha | ha
    · have : a1 * g ≤ a1 * g2 := mul_le_mul_of_nonneg_left hg2 ha
      exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_left _ _))
    · have : a1 * g ≤ a1 * g1 := mul_le_mul_of_nonpos_left hg1 ha
      exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_left _ _))

/-- 端点の値からの増え方（仮定：0 ≤ η・各段で x_{k+1} ≤ (1+η)x_k）：x_k ≤ (1+η)^k x_0。 -/
theorem steps_growth (x : ℕ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hstep : ∀ k, x (k + 1) ≤ (1 + η) * x k) : ∀ k, x k ≤ (1 + η) ^ k * x 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc x (k + 1) ≤ (1 + η) * x k := hstep k
      _ ≤ (1 + η) * ((1 + η) ^ k * x 0) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 + η) ^ (k + 1) * x 0 := by ring

/-- (1+η)^k ≤ exp(kη)（仮定：0 ≤ 1 + η。1 + η ≤ exp η と単調性）。 -/
theorem one_add_pow_le_exp (η : ℝ) (k : ℕ) (h : 0 ≤ 1 + η) : (1 + η) ^ k ≤ Real.exp (k * η) := by
  have h1 : 1 + η ≤ Real.exp η := by linarith [Real.add_one_le_exp η]
  calc (1 + η) ^ k ≤ (Real.exp η) ^ k := pow_le_pow_left₀ h h1 k
    _ = Real.exp (k * η) := by rw [← Real.exp_nat_mul]

/-- 区間の数（仮定：1 ≤ q・各段で q·h_i ≤ h_{i+1}）：q^m·h_0 ≤ h_m。
よって [A,B] を相対幅 ≥ q − 1 の区間で覆うには m ≥ log(B/A)/log q 個で足りる。 -/
theorem geometric_cover_count (h : ℕ → ℝ) (q : ℝ) (hq : 1 ≤ q)
    (hstep : ∀ i, q * h i ≤ h (i + 1)) : ∀ m, q ^ m * h 0 ≤ h m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    calc q ^ (k + 1) * h 0 = q * (q ^ k * h 0) := by ring
      _ ≤ q * h k := mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ h (k + 1) := hstep k

/-- 隣り合う区間 [b_i, b_{i+1}]（i ≤ m）の表から全体 [b_0, b_{m+1}] へ。 -/
theorem cover_le (f : ℝ → ℝ) (c : ℝ) (b : ℕ → ℝ) :
    ∀ m : ℕ, (∀ i, i < m + 1 → ∀ x, b i ≤ x → x ≤ b (i + 1) → f x ≤ c) →
      ∀ x, b 0 ≤ x → x ≤ b (m + 1) → f x ≤ c := by
  intro m
  induction m with
  | zero => intro H x h0 h1; exact H 0 (by omega) x h0 h1
  | succ k ih =>
    intro H x h0 h1
    rcases le_total x (b (k + 1)) with h | h
    · exact ih (fun i hi y hy1 hy2 => H i (by omega) y hy1 hy2) x h0 h
    · exact H (k + 1) (by omega) x h h1

/-- 表の組み立て（仮定：各区間 i ≤ m の全ての ħ で ρ(ħ) ≤ B_i、全ての B_i ≤ B）：窓 [b_0, b_{m+1}] の全てで ρ ≤ B。
B_i は計算の出力（区間演算ではない）を仮定に置いたもの。 -/
theorem window_le_of_interval_table (rho : ℝ → ℝ) (b B : ℕ → ℝ) (Bmax : ℝ) (m : ℕ)
    (htab : ∀ i, i < m + 1 → ∀ x, b i ≤ x → x ≤ b (i + 1) → rho x ≤ B i)
    (hmax : ∀ i, i < m + 1 → B i ≤ Bmax) :
    ∀ x, b 0 ≤ x → x ≤ b (m + 1) → rho x ≤ Bmax :=
  cover_le rho Bmax b m (fun i hi x h1 h2 => le_trans (htab i hi x h1 h2) (hmax i hi))

/-- 列和へ（仮定：表の組み立ての仮定・列和 ≤ 2ρ（定理 CC の ρ_col ≤ 2 sup ρ）・2·Bmax < 1）：窓の全てで列和 < 1。 -/
theorem column_lt_one_of_table (rho col : ℝ → ℝ) (b B : ℕ → ℝ) (Bmax : ℝ) (m : ℕ)
    (htab : ∀ i, i < m + 1 → ∀ x, b i ≤ x → x ≤ b (i + 1) → rho x ≤ B i)
    (hmax : ∀ i, i < m + 1 → B i ≤ Bmax) (hcol : ∀ x, col x ≤ 2 * rho x) (h2 : 2 * Bmax < 1) :
    ∀ x, b 0 ≤ x → x ≤ b (m + 1) → col x < 1 := by
  intro x h0 h1
  have := window_le_of_interval_table rho b B Bmax m htab hmax x h0 h1
  linarith [hcol x]

/-- 二つの窓をつなぐ（仮定：[A,C] と [C,D] で ρ ≤ B）：[A,D] で ρ ≤ B。 -/
theorem join_windows (rho : ℝ → ℝ) (A C D B : ℝ) (h1 : ∀ x, A ≤ x → x ≤ C → rho x ≤ B)
    (h2 : ∀ x, C ≤ x → x ≤ D → rho x ≤ B) : ∀ x, A ≤ x → x ≤ D → rho x ≤ B := by
  intro x hA hD
  rcases le_total x C with h | h
  · exact h1 x hA h
  · exact h2 x h hD

end LatticeGauge.DobrushinIntervalTable

#print axioms LatticeGauge.DobrushinIntervalTable.centered_split
#print axioms LatticeGauge.DobrushinIntervalTable.le_of_sq_le_sq_nonneg
#print axioms LatticeGauge.DobrushinIntervalTable.geomean_dev
#print axioms LatticeGauge.DobrushinIntervalTable.mul_le_corners
#print axioms LatticeGauge.DobrushinIntervalTable.steps_growth
#print axioms LatticeGauge.DobrushinIntervalTable.one_add_pow_le_exp
#print axioms LatticeGauge.DobrushinIntervalTable.geometric_cover_count
#print axioms LatticeGauge.DobrushinIntervalTable.cover_le
#print axioms LatticeGauge.DobrushinIntervalTable.window_le_of_interval_table
#print axioms LatticeGauge.DobrushinIntervalTable.column_lt_one_of_table
#print axioms LatticeGauge.DobrushinIntervalTable.join_windows
