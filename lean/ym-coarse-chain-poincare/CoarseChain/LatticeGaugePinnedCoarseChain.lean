/-
  命題 PIN（第 10 部 (T0′_P) の ħ ≤ 10⁻⁵）の代数の部分。
  三重対角 tridiag(−1, 15/8, −1) の首座小行列式 D n（漸化 D (n+2) = (15/8) D (n+1) − D n）、
  7 サイトの橋の逆行列の成分 h₁₁ = D 6 / D 7、h₁₇ = 1 / D 7、L_g = (h₁₁ + h₇₇ + 2h₁₇)/4、
  最後の不等式の組み立て。解析の部分（Brascamp–Lieb・部分積分・比較原理・指数分布の支配）は紙。
-/
import Mathlib

namespace LatticeGauge.PinnedCoarseChain

/-- tridiag(−1, 15/8, −1) の n 次の首座小行列式。 -/
def D : ℕ → ℚ
  | 0 => 1
  | 1 => 15 / 8
  | (n + 2) => 15 / 8 * D (n + 1) - D n

theorem D_seven : D 7 = 1770735 / 2097152 := by
  simp [D]; norm_num

theorem D_six : D 6 = 1832324 / 1048576 := by
  simp [D]; norm_num

/-- 7 サイトまでの首座小行列式は全て正（7 サイトの橋は一様に凸）。 -/
theorem D_pos_le_seven : ∀ n ≤ 7, 0 < D n := by
  intro n hn
  interval_cases n <;> simp [D] <;> norm_num

/-- 8 サイトでは負（共役長の境）。 -/
theorem D_eight_neg : D 8 = -2756159 / 16777216 ∧ D 8 < 0 := by
  constructor <;> simp [D] <;> norm_num

/-- 逆行列の (1,1) 成分＝ D 6 / D 7、(1,7) 成分＝ 1 / D 7（三重対角の余因子）。値。 -/
theorem h11_value : D 6 / D 7 = 3664648 / 1770735 := by
  rw [D_six, D_seven]; norm_num

theorem h17_value : 1 / D 7 = 2097152 / 1770735 := by
  rw [D_seven]; norm_num

/-- L_g = (h₁₁ + h₇₇ + 2 h₁₇)/4（対称なので h₇₇ = h₁₁）。 -/
theorem Lg_value :
    ((3664648 / 1770735 : ℚ) + 3664648 / 1770735 + 2 * (2097152 / 1770735)) / 4 = 1980 / 1217 := by
  norm_num

/-- 一次元の補題：λ L_g · 2/(λ d)² = 2 L_g (1/λ)/d²。 -/
theorem assemble (lam Lg d : ℝ) (hl : 0 < lam) (hd : 0 < d) :
    lam * Lg * (2 / (lam * d) ^ 2) = 2 * Lg * (1 / lam) / d ^ 2 := by
  field_simp

/-- 最後の不等式：0 < ħ ≤ 10⁻⁵、ε = 1/2、e² ≤ 7 h₇₇ ε ħ、d = D₀ − 2e（D₀ = 0.023126）なら
    2 L_g ε ħ / d² ≤ 0.437（したがって ρ_col ≤ 0.874）。 -/
theorem final_bound (hb e : ℝ) (h0 : 0 < hb) (h1 : hb ≤ 1 / 100000)
    (he2 : e ^ 2 ≤ 7 * (3664648 / 1770735) * (1 / 2) * hb) :
    2 * (1980 / 1217) * (1 / 2) * hb / (23126 / 1000000 - 2 * e) ^ 2 ≤ 437 / 1000 ∧
      0 < 23126 / 1000000 - 2 * e := by
  have hE : e ≤ 8512 / 1000000 := by
    by_contra h
    rw [not_le] at h
    have : (8512 / 1000000 : ℝ) ^ 2 < e ^ 2 := by
      apply pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    nlinarith
  have hd : (6102 / 1000000 : ℝ) ≤ 23126 / 1000000 - 2 * e := by linarith
  have hdpos : (0 : ℝ) < 23126 / 1000000 - 2 * e := by linarith
  refine ⟨?_, hdpos⟩
  rw [div_le_iff₀ (by positivity)]
  have hsq : (6102 / 1000000 : ℝ) ^ 2 ≤ (23126 / 1000000 - 2 * e) ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num) hd
  nlinarith

end LatticeGauge.PinnedCoarseChain

#print axioms LatticeGauge.PinnedCoarseChain.D_seven
#print axioms LatticeGauge.PinnedCoarseChain.D_six
#print axioms LatticeGauge.PinnedCoarseChain.D_pos_le_seven
#print axioms LatticeGauge.PinnedCoarseChain.D_eight_neg
#print axioms LatticeGauge.PinnedCoarseChain.h11_value
#print axioms LatticeGauge.PinnedCoarseChain.h17_value
#print axioms LatticeGauge.PinnedCoarseChain.Lg_value
#print axioms LatticeGauge.PinnedCoarseChain.assemble
#print axioms LatticeGauge.PinnedCoarseChain.final_bound
