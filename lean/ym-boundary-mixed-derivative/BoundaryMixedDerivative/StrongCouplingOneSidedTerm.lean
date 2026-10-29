import Mathlib

/-!
# 強結合の端：h = β_R − D_R の主項の符号（算術と不等式の段）

紙（bin-1020 §1）の段のうち、算術と不等式だけを確かめる。
展開の収束（剰余の評価 |R| ≤ C u^(3L+1)）と係数の値は仮定として受ける。
* 帯の片側の項：β_R ⊃ −2B/(6L² s)，B = 24 L² u^(3L)，s = sin(π/(2L²))。
* 上下を結ぶ筒の項：h ⊃ (1/(6L² s) − √2/(π D̂)) · A，A ≥ 0，D̂ ≤ 3。
-/

namespace StrongCouplingOneSided

open Real

/-- `L ≥ 4` なら `3L + L ≤ L²`。 -/
theorem four_mul_le_sq (L : ℕ) (hL : 4 ≤ L) : 3*L + L ≤ L^2 := by
  nlinarith

/-- 面積の項 `u^(L²)` は帯の項 `u^(3L)` より `u^L` だけ小さい。 -/
theorem area_le_strip (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) (L : ℕ) (hL : 4 ≤ L) :
    u^(L^2) ≤ u^(3*L) * u^L := by
  rw [← pow_add]
  exact pow_le_pow_of_le_one h0 h1 (four_mul_le_sq L hL)

/-- 帯の片側の項の β_R への寄与は `−(8/s) u^(3L)`。 -/
theorem strip_term_eq (L s u : ℝ) (n : ℕ) (hL : L ≠ 0) (hs : s ≠ 0) :
    -(2*(24*L^2*u^n))/(6*L^2*s) = -(8/s)*u^n := by
  field_simp
  ring

/-- `0 < s ≤ π/(2L²)` なら係数 `8/s ≥ 16L²/π`。 -/
theorem strip_coeff_lower (L s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (hsx : s ≤ π/(2*L^2)) : 16*L^2/π ≤ 8/s := by
  have hpi : 0 < π := pi_pos
  rw [div_le_div_iff₀ hpi hs]
  have h2 : s * (2*L^2) ≤ π := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2*L^2)).mp hsx
    linarith
  nlinarith

/-- 筒の項の係数は負：`1/(6L² s) < √2/(π D̂)`（`L ≥ 4`，`sin x > x − x³/4`，`0 < D̂ ≤ 3`）。 -/
theorem tube_coeff_neg (L s D : ℝ) (hL : 4 ≤ L)
    (hs : π/(2*L^2) - (π/(2*L^2))^3/4 < s) (hD0 : 0 < D) (hD : D ≤ 3) :
    1/(6*L^2*s) < √2/(π*D) := by
  have hpi : 0 < π := pi_pos
  have hpi4 : π < 4 := by linarith [pi_lt_d2]
  have hL2 : 0 < L^2 := by positivity
  set x := π/(2*L^2) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1/8 := by
    rw [hx, div_le_iff₀ (by positivity)]
    nlinarith
  have hxL : 6*L^2*x = 3*π := by
    rw [hx]; field_simp; ring
  have hs' : 3*π*(1 - x^2/4) < 6*L^2*s := by
    have : 6*L^2*(x - x^3/4) < 6*L^2*s := by
      apply mul_lt_mul_of_pos_left hs (by positivity)
    nlinarith
  have hspos : 0 < s := by nlinarith
  have hq : (0:ℝ) ≤ √2 := sqrt_nonneg 2
  have hq2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hr : (7:ℝ)/5 < √2 := by nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hx2 : x^2 ≤ 1/64 := by nlinarith
  have h1 : 3*π*(63/64) ≤ 3*π*(1 - x^2/4) := by nlinarith
  nlinarith

/-- 筒の項の h への寄与は非正（係数が負で `A ≥ 0`）。 -/
theorem tube_part_nonpos (c A : ℝ) (hc : c < 0) (hA : 0 ≤ A) : c * A ≤ 0 := by
  nlinarith

/-- 主項＋剰余：`|R| ≤ C u^(3L+1)` なら `h + K u^(3L)` は `C u · u^(3L)` 以内。 -/
theorem h_main_term (K C u R : ℝ) (L : ℕ)
    (hR : |R| ≤ C*u^(3*L+1)) :
    |(-K*u^(3*L) + R) - (-K*u^(3*L))| ≤ (C*u) * u^(3*L) := by
  have : (C*u) * u^(3*L) = C*u^(3*L+1) := by rw [pow_succ]; ring
  rw [this]; simpa using hR

/-- 収束域で `C u < K` なら `h = −K u^(3L) + G + R < 0`（筒の項 `G ≤ 0`）。 -/
theorem h_neg (K C u R G : ℝ) (L : ℕ) (hu : 0 < u)
    (hR : |R| ≤ C*u^(3*L+1)) (hCu : C*u < K) (hG : G ≤ 0) :
    -K*u^(3*L) + G + R < 0 := by
  have hp : 0 < u^(3*L) := pow_pos hu _
  have h1 : R ≤ C*u^(3*L+1) := le_trans (le_abs_self R) hR
  have h2 : C*u^(3*L+1) = (C*u)*u^(3*L) := by rw [pow_succ]; ring
  have h3 : (C*u)*u^(3*L) < K*u^(3*L) := mul_lt_mul_of_pos_right hCu hp
  linarith

/-- 収束域 `0 < u ≤ u₀` と `C u₀ < K` から、`(0,u₀]` の全体で h < 0。 -/
theorem h_neg_on_interval (K C u u₀ R G : ℝ) (L : ℕ) (hu : 0 < u) (hu0 : u ≤ u₀)
    (hC : 0 ≤ C) (hR : |R| ≤ C*u^(3*L+1)) (hCu0 : C*u₀ < K) (hG : G ≤ 0) :
    -K*u^(3*L) + G + R < 0 := by
  have : C*u ≤ C*u₀ := mul_le_mul_of_nonneg_left hu0 hC
  exact h_neg K C u R G L hu hR (lt_of_le_of_lt this hCu0) hG

end StrongCouplingOneSided

#print axioms StrongCouplingOneSided.four_mul_le_sq
#print axioms StrongCouplingOneSided.area_le_strip
#print axioms StrongCouplingOneSided.strip_term_eq
#print axioms StrongCouplingOneSided.strip_coeff_lower
#print axioms StrongCouplingOneSided.tube_coeff_neg
#print axioms StrongCouplingOneSided.tube_part_nonpos
#print axioms StrongCouplingOneSided.h_main_term
#print axioms StrongCouplingOneSided.h_neg
#print axioms StrongCouplingOneSided.h_neg_on_interval
