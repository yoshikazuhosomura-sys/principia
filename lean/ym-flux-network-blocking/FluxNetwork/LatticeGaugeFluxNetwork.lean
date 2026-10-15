import Mathlib

/-!
# 束の網の有限次元の代数（鞍点の主項の部品）

有限集合の上の実数値の束 `f` について、次の有限和の事実を示す。

* `sum_pow_four_le`・`ratio_le_max`：`∀ i, f i ^ 2 ≤ M` なら `∑ f⁴ ≤ M ∑ f²`、したがって `∑ f⁴ / ∑ f² ≤ M`
  （横の縮みの主項 `λ = ∑f⁴/∑f²` は最大の束の二乗以下）。
* `pow_four_sum_le`・`ratio_ge_of_unit_flux`：部分集合 `S` の上で `∑_S f = 1` なら
  `(∑_S f)⁴ ≤ |S|³ ∑_S f⁴`、したがって `1 / (|S|³ ∑ f²) ≤ ∑ f⁴ / ∑ f²`。
* `energy_split`：`∑ f ψ = 0` なら `∑ (θ f + ψ)² = θ² ∑ f² + ∑ ψ²`（最小点のまわりの直交分解）。
* `thomson_lower`・`thomson_attained`：`∑ u φ = θ`（`u ≠ 0`）なら `∑ φ² ≥ θ² / ∑ u²`、
  等号は `φ = θ u / ∑ u²` で達する（Thomson の原理の有限次元の核：Cauchy–Schwarz）。
* `minimizer_unique`：中点で閉じた集合の上で `∑ x²` の最小点は一つしかない（狭義凸性の有限版、Kirchhoff の一意性）。
* `constraint_midpoint`：部分空間 `V` と一次の拘束 `∑ s φ = θ` の交わりは中点で閉じる。
* `quad_lower`：`β > 0` なら `β/4 · x² − a x ≥ −a²/β`（木の水準の θ⁶ の剰余の評価に使う一行）。
* `chain_one_step`：重みつきノルムの一段の鎖（補題 A.6.1 の型）の実数の算術。

格子・群・測度は扱わない。ここにあるのは、紙の定理 F と補題 H で使う有限和の不等式だけ。
-/

namespace LatticeGauge.FluxNetwork

open Finset

variable {ι : Type*}

/-- 各 `f i ^ 2 ≤ M` なら `∑ f⁴ ≤ M ∑ f²`。 -/
theorem sum_pow_four_le (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (h : ∀ i ∈ s, f i ^ 2 ≤ M) :
    ∑ i ∈ s, f i ^ 4 ≤ M * ∑ i ∈ s, f i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h1 := h i hi
  have h0 : 0 ≤ f i ^ 2 := sq_nonneg _
  calc f i ^ 4 = f i ^ 2 * f i ^ 2 := by ring
    _ ≤ M * f i ^ 2 := mul_le_mul_of_nonneg_right h1 h0

/-- 横の縮みの主項は最大の束の二乗以下：`∑ f⁴ / ∑ f² ≤ M`。 -/
theorem ratio_le_max (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (h : ∀ i ∈ s, f i ^ 2 ≤ M) (hpos : 0 < ∑ i ∈ s, f i ^ 2) :
    (∑ i ∈ s, f i ^ 4) / (∑ i ∈ s, f i ^ 2) ≤ M := by
  rw [div_le_iff₀ hpos]
  exact sum_pow_four_le s f M h

/-- 冪平均：`(∑_S x)⁴ ≤ |S|³ ∑_S x⁴`。 -/
theorem pow_four_sum_le (S : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ S, x i) ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, x i ^ 4 := by
  have h1 : (∑ i ∈ S, x i) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, x i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : (∑ i ∈ S, x i ^ 2) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, (x i ^ 2) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2' : (∑ i ∈ S, x i ^ 2) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, x i ^ 4 := by
    have : ∀ i ∈ S, (x i ^ 2) ^ 2 = x i ^ 4 := fun i _ => by ring
    rw [Finset.sum_congr rfl this] at h2
    exact h2
  have hA : 0 ≤ (∑ i ∈ S, x i) ^ 2 := sq_nonneg _
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have h3 : ((∑ i ∈ S, x i) ^ 2) ^ 2 ≤ ((S.card : ℝ) * ∑ i ∈ S, x i ^ 2) ^ 2 :=
    pow_le_pow_left₀ hA h1 2
  calc (∑ i ∈ S, x i) ^ 4 = ((∑ i ∈ S, x i) ^ 2) ^ 2 := by ring
    _ ≤ ((S.card : ℝ) * ∑ i ∈ S, x i ^ 2) ^ 2 := h3
    _ = (S.card : ℝ) ^ 2 * (∑ i ∈ S, x i ^ 2) ^ 2 := by ring
    _ ≤ (S.card : ℝ) ^ 2 * ((S.card : ℝ) * ∑ i ∈ S, x i ^ 4) :=
        mul_le_mul_of_nonneg_left h2' (by positivity)
    _ = (S.card : ℝ) ^ 3 * ∑ i ∈ S, x i ^ 4 := by ring

/-- 単位の束（`∑_S f = 1`、`S ⊆ s`）なら `1 / (|S|³ ∑ f²) ≤ ∑ f⁴ / ∑ f²`。 -/
theorem ratio_ge_of_unit_flux [DecidableEq ι] (s S : Finset ι) (f : ι → ℝ) (hS : S ⊆ s)
    (hunit : ∑ i ∈ S, f i = 1) (hpos : 0 < ∑ i ∈ s, f i ^ 2) :
    1 / ((S.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 2) ≤ (∑ i ∈ s, f i ^ 4) / (∑ i ∈ s, f i ^ 2) := by
  have hpm := pow_four_sum_le S f
  rw [hunit] at hpm
  have hsub : ∑ i ∈ S, f i ^ 4 ≤ ∑ i ∈ s, f i ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => by positivity)
  have hcardpos : (0 : ℝ) < (S.card : ℝ) := by
    have hne : S.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hunit
      exact zero_ne_one hunit
    exact_mod_cast hne.card_pos
  have hn3 : (0 : ℝ) < (S.card : ℝ) ^ 3 := by positivity
  have key : 1 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, f i ^ 4 := hpm
      _ ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := mul_le_mul_of_nonneg_left hsub hn3.le
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

/-- 最小点のまわりの直交分解：`∑ f ψ = 0` なら `∑ (θ f + ψ)² = θ² ∑ f² + ∑ ψ²`。 -/
theorem energy_split (s : Finset ι) (f ψ : ι → ℝ) (θ : ℝ)
    (horth : ∑ i ∈ s, f i * ψ i = 0) :
    ∑ i ∈ s, (θ * f i + ψ i) ^ 2 = θ ^ 2 * ∑ i ∈ s, f i ^ 2 + ∑ i ∈ s, ψ i ^ 2 := by
  have h : ∀ i ∈ s, (θ * f i + ψ i) ^ 2
      = θ ^ 2 * f i ^ 2 + (2 * θ) * (f i * ψ i) + ψ i ^ 2 := fun i _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, horth]
  ring

/-- Thomson の原理の有限次元の核：`∑ u φ = θ` なら `θ² / ∑ u² ≤ ∑ φ²`。 -/
theorem thomson_lower (s : Finset ι) (u φ : ι → ℝ) (θ : ℝ)
    (hu : 0 < ∑ i ∈ s, u i ^ 2) (hc : ∑ i ∈ s, u i * φ i = θ) :
    θ ^ 2 / ∑ i ∈ s, u i ^ 2 ≤ ∑ i ∈ s, φ i ^ 2 := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq s u φ
  rw [hc] at cs
  rw [div_le_iff₀ hu]
  linarith [mul_comm (∑ i ∈ s, u i ^ 2) (∑ i ∈ s, φ i ^ 2)]

/-- 等号は `φ = θ u / ∑ u²` で達する：拘束を満たし、`∑ φ² = θ² / ∑ u²`。 -/
theorem thomson_attained (s : Finset ι) (u : ι → ℝ) (θ : ℝ)
    (hu : 0 < ∑ i ∈ s, u i ^ 2) :
    (∑ i ∈ s, u i * (θ * u i / ∑ j ∈ s, u j ^ 2) = θ) ∧
    (∑ i ∈ s, (θ * u i / ∑ j ∈ s, u j ^ 2) ^ 2 = θ ^ 2 / ∑ j ∈ s, u j ^ 2) := by
  set N := ∑ j ∈ s, u j ^ 2 with hN
  have hN0 : N ≠ 0 := ne_of_gt hu
  constructor
  · have h : ∀ i ∈ s, u i * (θ * u i / N) = (θ / N) * u i ^ 2 := fun i _ => by
      field_simp
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← hN]
    field_simp
  · have h : ∀ i ∈ s, (θ * u i / N) ^ 2 = (θ ^ 2 / N ^ 2) * u i ^ 2 := fun i _ => by
      field_simp
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← hN]
    field_simp

/-- 中点で閉じた集合の上で `∑ x²` の最小点は一つしかない。 -/
theorem minimizer_unique [Fintype ι] (A : Set (ι → ℝ))
    (hmid : ∀ φ ∈ A, ∀ ψ ∈ A, (fun i => (φ i + ψ i) / 2) ∈ A)
    (φ ψ : ι → ℝ) (hφA : φ ∈ A) (hψA : ψ ∈ A)
    (hφ : ∀ χ ∈ A, ∑ i, φ i ^ 2 ≤ ∑ i, χ i ^ 2)
    (hψ : ∀ χ ∈ A, ∑ i, ψ i ^ 2 ≤ ∑ i, χ i ^ 2) : φ = ψ := by
  have hm := hφ _ (hmid φ hφA ψ hψA)
  have h1 := hφ ψ hψA
  have h2 := hψ φ hφA
  have hsplit : ∑ i, ((φ i + ψ i) / 2) ^ 2
      = (∑ i, φ i ^ 2 + ∑ i, ψ i ^ 2) / 2 - (∑ i, (φ i - ψ i) ^ 2) / 4 := by
    have h : ∀ i ∈ (Finset.univ : Finset ι), ((φ i + ψ i) / 2) ^ 2
        = (φ i ^ 2 + ψ i ^ 2) / 2 - (φ i - ψ i) ^ 2 / 4 := fun i _ => by ring
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      Finset.sum_add_distrib]
  have hle : ∑ i, (φ i - ψ i) ^ 2 ≤ 0 := by
    have hm' : ∑ i, φ i ^ 2 ≤ ∑ i, ((φ i + ψ i) / 2) ^ 2 := hm
    rw [hsplit] at hm'
    linarith
  have hzero : ∑ i, (φ i - ψ i) ^ 2 = 0 :=
    le_antisymm hle (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at hzero
  funext i
  have := hzero i (Finset.mem_univ i)
  have h0 : φ i - ψ i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- 部分空間と一次の拘束の交わりは中点で閉じる。 -/
theorem constraint_midpoint [Fintype ι] (V : Submodule ℝ (ι → ℝ)) (s : ι → ℝ) (θ : ℝ) :
    ∀ φ ∈ {x : ι → ℝ | x ∈ V ∧ ∑ i, s i * x i = θ},
    ∀ ψ ∈ {x : ι → ℝ | x ∈ V ∧ ∑ i, s i * x i = θ},
      (fun i => (φ i + ψ i) / 2) ∈ {x : ι → ℝ | x ∈ V ∧ ∑ i, s i * x i = θ} := by
  rintro φ ⟨hφV, hφc⟩ ψ ⟨hψV, hψc⟩
  refine ⟨?_, ?_⟩
  · have e : (fun i => (φ i + ψ i) / 2) = (1 / 2 : ℝ) • (φ + ψ) := by
      funext i; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [e]
    exact V.smul_mem _ (V.add_mem hφV hψV)
  · have h : ∀ i ∈ (Finset.univ : Finset ι), s i * ((φ i + ψ i) / 2)
        = (s i * φ i) / 2 + (s i * ψ i) / 2 := fun i _ => by ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      hφc, hψc]
    ring

/-- `β > 0` なら `β/4 · x² − a x ≥ −a²/β`。 -/
theorem quad_lower (β a x : ℝ) (hβ : 0 < β) : -(a ^ 2 / β) ≤ β / 4 * x ^ 2 - a * x := by
  have key : β / 4 * x ^ 2 - a * x + a ^ 2 / β = (β * x / 2 - a) ^ 2 / β := by
    field_simp
    ring
  have hnn : 0 ≤ (β * x / 2 - a) ^ 2 / β := div_nonneg (sq_nonneg _) hβ.le
  linarith

/-- 一段の鎖の算術（補題 A.6.1 の型）：
`N ≤ E₁ ≤ ‖K‖·EG`、`EG ≤ G₀²·M`、`M ≤ B`、`G₀² ≤ G₊` なら `N ≤ ‖K‖·(G₊·B)`。 -/
theorem chain_one_step (N E1 normK EG G0 M Gp B : ℝ)
    (hK : 0 ≤ normK) (hB : 0 ≤ B)
    (h1 : N ≤ E1) (h2 : E1 ≤ normK * EG) (h3 : EG ≤ G0 ^ 2 * M)
    (h4 : M ≤ B) (h5 : G0 ^ 2 ≤ Gp) : N ≤ normK * (Gp * B) := by
  have hG2 : 0 ≤ G0 ^ 2 := sq_nonneg _
  have a1 : normK * EG ≤ normK * (G0 ^ 2 * M) := mul_le_mul_of_nonneg_left h3 hK
  have a2 : G0 ^ 2 * M ≤ G0 ^ 2 * B := mul_le_mul_of_nonneg_left h4 hG2
  have a3 : G0 ^ 2 * B ≤ Gp * B := mul_le_mul_of_nonneg_right h5 hB
  have a4 : normK * (G0 ^ 2 * M) ≤ normK * (Gp * B) :=
    mul_le_mul_of_nonneg_left (a2.trans a3) hK
  linarith

end LatticeGauge.FluxNetwork

#print axioms LatticeGauge.FluxNetwork.sum_pow_four_le
#print axioms LatticeGauge.FluxNetwork.ratio_le_max
#print axioms LatticeGauge.FluxNetwork.pow_four_sum_le
#print axioms LatticeGauge.FluxNetwork.ratio_ge_of_unit_flux
#print axioms LatticeGauge.FluxNetwork.energy_split
#print axioms LatticeGauge.FluxNetwork.thomson_lower
#print axioms LatticeGauge.FluxNetwork.thomson_attained
#print axioms LatticeGauge.FluxNetwork.minimizer_unique
#print axioms LatticeGauge.FluxNetwork.constraint_midpoint
#print axioms LatticeGauge.FluxNetwork.quad_lower
#print axioms LatticeGauge.FluxNetwork.chain_one_step
