/-
  0+1 次元の二重井戸で比べる量 `R = C_P·m²` の有限の骨。

  模型（Lean の外）：`S[x] = ∫dτ [½ẋ² + V(x)]`・測度 `e^{−S/ħ}`・`m = Δ/ħ = 1/ξ`。
  Dirichlet 形は正準の `ℰ = ħ∫|δf/δx|²`、`C_P = sup Var/ℰ`、`R = C_P·m²`。
  ここで閉じるのは実数の代数と有限和の不等式だけである：
    (1) `R` の定義・自由場（`C_P = 1/m²`）で `R = 1`・正規化の変換 `R_x = ħ·R`
    (2) 時刻局所な加法的関数の Rayleigh 商：基底状態変換で `Var/T = 2⟨φ, A⁻¹φ⟩`・`ℰ/T = 2⟨φ, Aφ⟩`
        （`A = (H − E₀)/ħ` の固有分解は Lean の外）。対角形で `Σ c/a ≤ (Σ c·a)/a₁²`（`a ≥ a₁ > 0`・`c ≥ 0`）、
        したがって `R_loc ≤ 1`、`a₁` の固有空間に載れば等号
    (3) 冪の水準：`1 ≤ R ≤ K/ħ` と `ln ξ ≥ s/ħ` から `ln R / ln ξ → 0`（`ħ → 0+`）
  二重井戸の `C_P` の値・キンクの描像・仮定 H・質量ギャップについては何も言わない。
-/
import Mathlib

namespace LatticeGauge.DoubleWellTestbed

open Filter Topology Finset

/-! ### (1) 定義・自由場・正規化 -/

/-- 比べる量 `R = C_P·m²`（`m = 1/ξ`）。 -/
def ratioR (CP m : ℝ) : ℝ := CP * m ^ 2

/-- **`ratioR_free_eq_one`**（仮定：`C_P = 1/m²`・`m ≠ 0`）：自由場では `R = 1`。 -/
theorem ratioR_free_eq_one {CP m : ℝ} (hm : m ≠ 0) (hCP : CP = 1 / m ^ 2) : ratioR CP m = 1 := by
  unfold ratioR; rw [hCP]; field_simp

/-- **`ratioR_x_normalisation`**（仮定なし）：`ℰ_x = ℰ/ħ` の正規化では `C_P^{(x)} = ħ·C_P` なので `R_x = ħ·R`。 -/
theorem ratioR_x_normalisation (hb CP m : ℝ) : ratioR (hb * CP) m = hb * ratioR CP m := by
  unfold ratioR; ring

/-! ### (2) 時刻局所な加法的関数の Rayleigh 商 -/

/-- **`inv_le_div_sq_of_le`**（仮定：`0 < a₁ ≤ a`）：`1/a ≤ a/a₁²`。 -/
theorem inv_le_div_sq_of_le {a a1 : ℝ} (h1 : 0 < a1) (h : a1 ≤ a) : 1 / a ≤ a / a1 ^ 2 := by
  have ha : 0 < a := lt_of_lt_of_le h1 h
  rw [div_le_div_iff₀ ha (by positivity)]
  nlinarith

/-- **`resolvent_le_form_div_sq`**（仮定：`0 < a₁`・`s` の上で `a₁ ≤ a k`・`0 ≤ c k`）：
対角形の `⟨φ, A⁻¹φ⟩ = Σ c/a` は `⟨φ, Aφ⟩/a₁² = (Σ c·a)/a₁²` 以下。 -/
theorem resolvent_le_form_div_sq {ι : Type*} (s : Finset ι) (c a : ι → ℝ) {a1 : ℝ}
    (h1 : 0 < a1) (ha : ∀ k ∈ s, a1 ≤ a k) (hc : ∀ k ∈ s, 0 ≤ c k) :
    ∑ k ∈ s, c k / a k ≤ (∑ k ∈ s, c k * a k) / a1 ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have h := inv_le_div_sq_of_le h1 (ha k hk)
  calc c k / a k = c k * (1 / a k) := by ring
    _ ≤ c k * (a k / a1 ^ 2) := mul_le_mul_of_nonneg_left h (hc k hk)
    _ = c k * a k / a1 ^ 2 := by ring

/-- **`local_rayleigh_ratio_le_one`**（仮定：`0 < a₁ = m`・`s` の上で `m ≤ a k`・`0 ≤ c k`・`0 < Σ c·a`）：
時刻局所な加法的関数の Rayleigh 商 `(2Σ c/a)/(2Σ c·a)` に `m²` を掛けたものは `1` 以下（`R_loc ≤ 1`）。 -/
theorem local_rayleigh_ratio_le_one {ι : Type*} (s : Finset ι) (c a : ι → ℝ) {m : ℝ}
    (hm : 0 < m) (ha : ∀ k ∈ s, m ≤ a k) (hc : ∀ k ∈ s, 0 ≤ c k)
    (hpos : 0 < ∑ k ∈ s, c k * a k) :
    ratioR ((2 * ∑ k ∈ s, c k / a k) / (2 * ∑ k ∈ s, c k * a k)) m ≤ 1 := by
  unfold ratioR
  have h := resolvent_le_form_div_sq s c a hm ha hc
  have hm2 : 0 < m ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_one (by positivity)]
  have : (∑ k ∈ s, c k / a k) * m ^ 2 ≤ ∑ k ∈ s, c k * a k := by
    rw [le_div_iff₀ hm2] at h; exact h
  nlinarith

/-- **`local_rayleigh_attained`**（仮定：`m ≠ 0`・`c₀ ≠ 0`）：一つの固有値 `a = m` の上に載る `φ` では
Rayleigh 商が `1/m²` に等しく、`R_loc = 1`（`h = ψ₁/ψ₀` に当たる）。 -/
theorem local_rayleigh_attained {m c0 : ℝ} (hm : m ≠ 0) (hc : c0 ≠ 0) :
    ratioR ((2 * (c0 / m)) / (2 * (c0 * m))) m = 1 := by
  unfold ratioR; field_simp

/-! ### (3) 冪の水準：前因子が `ħ` の冪なら冪の判定は動かない -/

/-- **`power_level_log_ratio_tendsto_zero`**（仮定：`0 < K`・`0 < s`・`0 < δ`・`0 < ħ < δ` で `1 ≤ R ħ ≤ K/ħ` と
`s/ħ ≤ ln ξ(ħ)`）：`ln R / ln ξ → 0`（`ħ → 0+`）。`ln C_P/ln ξ = 2 + ln R/ln ξ` なので冪の H の `2` は動かない。 -/
theorem power_level_log_ratio_tendsto_zero (R ξ : ℝ → ℝ) {K s δ : ℝ} (hK : 0 < K) (hs : 0 < s)
    (hδ : 0 < δ) (hR1 : ∀ h, 0 < h → h < δ → 1 ≤ R h) (hRK : ∀ h, 0 < h → h < δ → R h ≤ K / h)
    (hξ : ∀ h, 0 < h → h < δ → s / h ≤ Real.log (ξ h)) :
    Tendsto (fun h => Real.log (R h) / Real.log (ξ h)) (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 < h ∧ h < δ := by
    have h1 : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 < h := self_mem_nhdsWithin
    have h2 : ∀ᶠ h in 𝓝[>] (0:ℝ), h < δ := nhdsWithin_le_nhds (Iio_mem_nhds hδ)
    exact h1.and h2
  have hml : Tendsto (fun h : ℝ => h * Real.log h) (𝓝 0) (𝓝 0) := by
    have := Real.continuous_mul_log.tendsto 0
    simpa using this
  have hlin : Tendsto (fun h : ℝ => h * Real.log K) (𝓝 0) (𝓝 0) := by
    have := (continuous_mul_const (Real.log K)).tendsto (0:ℝ)
    simpa using this
  have hup : Tendsto (fun h : ℝ => (h * Real.log K - h * Real.log h) / s) (𝓝[>] 0) (𝓝 0) := by
    have h3 := (hlin.sub hml).div_const s
    rw [show ((0:ℝ) - 0) / s = 0 by simp] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [hev] with h hh
    have hl : 0 ≤ Real.log (R h) := Real.log_nonneg (hR1 h hh.1 hh.2)
    have hx : 0 < Real.log (ξ h) := lt_of_lt_of_le (div_pos hs hh.1) (hξ h hh.1 hh.2)
    exact div_nonneg hl hx.le
  · filter_upwards [hev] with h hh
    have h0 := hh.1
    have hl : 0 ≤ Real.log (R h) := Real.log_nonneg (hR1 h hh.1 hh.2)
    have hsh : 0 < s / h := div_pos hs h0
    have hx := hξ h hh.1 hh.2
    have hlogR : Real.log (R h) ≤ Real.log K - Real.log h := by
      rw [← Real.log_div hK.ne' h0.ne']
      exact Real.log_le_log (by linarith [hR1 h hh.1 hh.2]) (hRK h hh.1 hh.2)
    have hne : h ≠ 0 := h0.ne'
    have hsne : s ≠ 0 := hs.ne'
    calc Real.log (R h) / Real.log (ξ h) ≤ Real.log (R h) / (s / h) :=
          div_le_div_of_nonneg_left hl hsh hx
      _ ≤ (Real.log K - Real.log h) / (s / h) := div_le_div_of_nonneg_right hlogR hsh.le
      _ = (h * Real.log K - h * Real.log h) / s := by field_simp

end LatticeGauge.DoubleWellTestbed

#print axioms LatticeGauge.DoubleWellTestbed.ratioR_free_eq_one
#print axioms LatticeGauge.DoubleWellTestbed.ratioR_x_normalisation
#print axioms LatticeGauge.DoubleWellTestbed.inv_le_div_sq_of_le
#print axioms LatticeGauge.DoubleWellTestbed.resolvent_le_form_div_sq
#print axioms LatticeGauge.DoubleWellTestbed.local_rayleigh_ratio_le_one
#print axioms LatticeGauge.DoubleWellTestbed.local_rayleigh_attained
#print axioms LatticeGauge.DoubleWellTestbed.power_level_log_ratio_tendsto_zero
