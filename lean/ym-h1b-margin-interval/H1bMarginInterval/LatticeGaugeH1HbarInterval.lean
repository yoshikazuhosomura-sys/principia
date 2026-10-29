/-
(H1) の (T1) の余白を ħ の部分区間 [ħ₁, ħ₂] の全てで：区間演算（float64＋外向きの幅）の出力を仮定にした算術と、
帯つき Muckenhoupt の指数を ħ の区間で押さえる段の初等的な不等式。解析（Muckenhoupt・FKG・TAU の補間の剰余）は仮定の外。
-/
import Mathlib

namespace LatticeGauge.H1HbarInterval

/-- 一つのセルの指数：`0 < ħ₁ ≤ ħ ≤ ħ₂` なら `min (U/ħ₁) (U/ħ₂) ≤ U/ħ`（U の符号によらない）。 -/
theorem cell_lower (U h1 h2 h : ℝ) (h1p : 0 < h1) (hh1 : h1 ≤ h) (hh2 : h ≤ h2) :
    min (U / h1) (U / h2) ≤ U / h := by
  have hp : 0 < h := lt_of_lt_of_le h1p hh1
  have h2p : 0 < h2 := lt_of_lt_of_le hp hh2
  rcases le_total 0 U with hU | hU
  · exact le_trans (min_le_right _ _) (div_le_div_of_nonneg_left hU hp hh2)
  · refine le_trans (min_le_left _ _) ?_
    rw [div_le_div_iff₀ h1p hp]
    nlinarith

/-- 一つのセルの指数の上の側：`U/ħ ≤ max (U/ħ₁) (U/ħ₂)`。 -/
theorem cell_upper (U h1 h2 h : ℝ) (h1p : 0 < h1) (hh1 : h1 ≤ h) (hh2 : h ≤ h2) :
    U / h ≤ max (U / h1) (U / h2) := by
  have := cell_lower (-U) h1 h2 h h1p hh1 hh2
  rw [neg_div, neg_div, neg_div, min_neg_neg] at this
  linarith [neg_le_neg_iff.mp this]

/-- 前向きの和：セルごとの下界の和は `Σ U_j/ħ` 以下。 -/
theorem sum_lower {ι : Type*} (S : Finset ι) (U : ι → ℝ) (h1 h2 h : ℝ) (h1p : 0 < h1) (hh1 : h1 ≤ h)
    (hh2 : h ≤ h2) : ∑ j ∈ S, min (U j / h1) (U j / h2) ≤ ∑ j ∈ S, U j / h :=
  Finset.sum_le_sum fun j _ => cell_lower (U j) h1 h2 h h1p hh1 hh2

/-- 前向きの和の上の側。 -/
theorem sum_upper {ι : Type*} (S : Finset ι) (U : ι → ℝ) (h1 h2 h : ℝ) (h1p : 0 < h1) (hh1 : h1 ≤ h)
    (hh2 : h ≤ h2) : ∑ j ∈ S, U j / h ≤ ∑ j ∈ S, max (U j / h1) (U j / h2) :=
  Finset.sum_le_sum fun j _ => cell_upper (U j) h1 h2 h h1p hh1 hh2

/-- `ħρ = ħ/(4B)` の下界：`ħ₁ ≤ ħ`・`0 < B ≤ Bbar` なら `ħ₁/(4 Bbar) ≤ ħ/(4B)`。 -/
theorem rho_lower (h1 h B Bbar : ℝ) (h1p : 0 < h1) (hh : h1 ≤ h) (hB : 0 < B) (hBB : B ≤ Bbar) :
    h1 / (4 * Bbar) ≤ h / (4 * B) := by
  have hBb : 0 < Bbar := lt_of_lt_of_le hB hBB
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- 小片の被覆：小片ごとの下界 `r p` の最小は、どの小片の ħ についても下界。 -/
theorem pieces_min {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (r : ι → ℝ) (f : ℝ → ℝ)
    (mem : ℝ → ι) (hmem : ∀ h, mem h ∈ S) (hr : ∀ h, r (mem h) ≤ f h) (h : ℝ) :
    S.inf' hS r ≤ f h :=
  le_trans (Finset.inf'_le r (hmem h)) (hr h)

/-- 部分区間ごとの余白（仮定：区間演算の出力 `r ≤ ħρ(ħ)`・`ħκ(ħ) ≤ k` が区間の全ての ħ で）。 -/
theorem margin_on_interval (hr hk : ℝ → ℝ) (r k h1 h2 : ℝ) (hm : 0.067 ≤ r - 2 * k)
    (h1r : ∀ h, h1 ≤ h → h ≤ h2 → r ≤ hr h) (h2k : ∀ h, h1 ≤ h → h ≤ h2 → hk h ≤ k) :
    ∀ h, h1 ≤ h → h ≤ h2 → 0.067 ≤ hr h - 2 * hk h := by
  intro h a b
  have := h1r h a b; have := h2k h a b; linarith

/-- 部分区間 I₁=[0.005/1.17, 0.005] の数（区間演算の出力 `ħρ ≥ 0.84797`〔Muckenhoupt 8 小片の min〕・`ħκ ≤ 0.38560`〔259560 箱の max〕）：
余白 `≥ 0.067`。仮定なし（数の検算）。 -/
theorem margin_I1 : (0.067 : ℝ) ≤ 0.84797 - 2 * 0.38560 := by norm_num

/-- 部分区間 I₂=[0.005/1.17², 0.005/1.17] の数（`ħρ ≥ 0.85245`・`ħκ ≤ 0.34907`〔354903 箱〕）：余白 `≥ 0.067`。 -/
theorem margin_I2 : (0.067 : ℝ) ≤ 0.85245 - 2 * 0.34907 := by norm_num

/-- 部分区間 I₃=[0.005/1.17³, 0.005/1.17²] の数（`ħρ ≥ 0.87360`・`ħκ ≤ 0.31665`〔閾の外 0 箱〕）：余白 `≥ 0.067`。 -/
theorem margin_I3 : (0.067 : ℝ) ≤ 0.87360 - 2 * 0.31665 := by norm_num

/-- 部分区間 I₄=[0.005/1.17⁴, 0.005/1.17³] の数（`ħρ ≥ 0.87539`・`ħκ ≤ 0.27705`〔665281 箱〕）：余白 `≥ 0.067`。 -/
theorem margin_I4 : (0.067 : ℝ) ≤ 0.87539 - 2 * 0.27705 := by norm_num

/-- 部分区間 I₅=[0.005/1.17⁵, 0.005/1.17⁴] の数（`ħρ ≥ 0.86653`・`ħκ ≤ 0.25695`）：余白 `≥ 0.067`。 -/
theorem margin_I5 : (0.067 : ℝ) ≤ 0.86653 - 2 * 0.25695 := by norm_num

/-- 部分区間 I₆=[0.005/1.17⁶, 0.005/1.17⁵] の数（`ħρ ≥ 0.85199`・`ħκ ≤ 0.24263`）：余白 `≥ 0.067`。 -/
theorem margin_I6 : (0.067 : ℝ) ≤ 0.85199 - 2 * 0.24263 := by norm_num

/-- 閾の算術：`ħκ ≤ (r − 0.067)/2` なら余白 `≥ 0.067`。 -/
theorem threshold (r k : ℝ) (hk : k ≤ (r - 0.067) / 2) : 0.067 ≤ r - 2 * k := by linarith

/-- 陰性対照：I₁ の本走だけ（細かい刻みの流し直しの前の max 4.33884）では余白は負。 -/
theorem margin_I1_coarse_fails : ¬ ((0.067 : ℝ) ≤ 0.84797 - 2 * 4.33884) := by norm_num

end LatticeGauge.H1HbarInterval

#print axioms LatticeGauge.H1HbarInterval.cell_lower
#print axioms LatticeGauge.H1HbarInterval.cell_upper
#print axioms LatticeGauge.H1HbarInterval.sum_lower
#print axioms LatticeGauge.H1HbarInterval.sum_upper
#print axioms LatticeGauge.H1HbarInterval.rho_lower
#print axioms LatticeGauge.H1HbarInterval.pieces_min
#print axioms LatticeGauge.H1HbarInterval.margin_on_interval
#print axioms LatticeGauge.H1HbarInterval.margin_I1
#print axioms LatticeGauge.H1HbarInterval.margin_I2
#print axioms LatticeGauge.H1HbarInterval.margin_I3
#print axioms LatticeGauge.H1HbarInterval.margin_I4
#print axioms LatticeGauge.H1HbarInterval.margin_I5
#print axioms LatticeGauge.H1HbarInterval.margin_I6
#print axioms LatticeGauge.H1HbarInterval.threshold
#print axioms LatticeGauge.H1HbarInterval.margin_I1_coarse_fails
