import Mathlib

/-!
# 全ての粗い面を同時に固定したブロック化の有限和の部品

* `sq_sum_fin_four_le`・`block_energy_lower`・`fine_energy_lower`：粗い面 `P` の中の四枚の細かいプラケットの
  値の和が `θ_P` なら、細かいエネルギー `∑ ψ²` は `∑_P θ_P² / 4` 以上（粗い二次形式の固有値の下界 `1/4`）。
  四枚の組は互いに重ならない（`e` が単射）ことだけを使う。
* `equal_split_ratio`：四枚に等分した束 `f = 1/4` で `∑ f⁴ / ∑ f² = 1/16`（MK の値の算術）。
* `smooth_ratio`：一つの粗い面あたり `n` 枚の細かいプラケットが同じ値 `θ/4` を持つとき、
  四次と二次の比の比は `n` に依らず `1/16`。
* `quartic_expand`：`∑ (x + y)⁴` の対角と交差への分解。

格子・群・最小化そのものは扱わない。
-/

namespace LatticeGauge.AllFacesBlocking

open Finset

variable {ι κ : Type*}

/-- 四つの実数の和の二乗は二乗和の四倍以下。 -/
theorem sq_sum_fin_four_le (f : Fin 4 → ℝ) :
    (∑ i, f i) ^ 2 ≤ 4 * ∑ i, f i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4))) (f := f)
  simpa using h

/-- 粗い面ごとに四枚：`∑_P (∑_i φ_{P,i})² ≤ 4 ∑_P ∑_i φ_{P,i}²`。 -/
theorem block_energy_lower (s : Finset ι) (φ : ι → Fin 4 → ℝ) :
    ∑ P ∈ s, (∑ i, φ P i) ^ 2 ≤ 4 * ∑ P ∈ s, ∑ i, φ P i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun P _ => sq_sum_fin_four_le (φ P)

/-- 細かい場 `ψ` の上の下界：四枚の組が重ならず `T` に入るなら `∑_P θ_P² ≤ 4 ∑_{q∈T} ψ_q²`。 -/
theorem fine_energy_lower [DecidableEq κ] (s : Finset ι) (T : Finset κ)
    (e : ι × Fin 4 → κ) (he : Set.InjOn e ↑(s ×ˢ (Finset.univ : Finset (Fin 4))))
    (hT : ∀ x ∈ s ×ˢ (Finset.univ : Finset (Fin 4)), e x ∈ T) (ψ : κ → ℝ) :
    ∑ P ∈ s, (∑ i, ψ (e (P, i))) ^ 2 ≤ 4 * ∑ q ∈ T, ψ q ^ 2 := by
  have h1 := block_energy_lower s (fun P i => ψ (e (P, i)))
  have h2 : ∑ P ∈ s, ∑ i, ψ (e (P, i)) ^ 2
      = ∑ x ∈ s ×ˢ (Finset.univ : Finset (Fin 4)), ψ (e x) ^ 2 := by
    rw [Finset.sum_product]
  have h3 : ∑ x ∈ s ×ˢ (Finset.univ : Finset (Fin 4)), ψ (e x) ^ 2
      = ∑ q ∈ (s ×ˢ (Finset.univ : Finset (Fin 4))).image e, ψ q ^ 2 := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact he hx hy hxy
  have h4 : ∑ q ∈ (s ×ˢ (Finset.univ : Finset (Fin 4))).image e, ψ q ^ 2
      ≤ ∑ q ∈ T, ψ q ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact hT x hx
    · intro q _ _
      exact sq_nonneg _
  calc ∑ P ∈ s, (∑ i, ψ (e (P, i))) ^ 2
      ≤ 4 * ∑ P ∈ s, ∑ i, ψ (e (P, i)) ^ 2 := h1
    _ = 4 * ∑ q ∈ (s ×ˢ (Finset.univ : Finset (Fin 4))).image e, ψ q ^ 2 := by rw [h2, h3]
    _ ≤ 4 * ∑ q ∈ T, ψ q ^ 2 := by linarith

/-- 等分した束（MK の規約）：`∑ (1/4)⁴ / ∑ (1/4)² = 1/16`。 -/
theorem equal_split_ratio :
    (∑ _i : Fin 4, ((1 : ℝ) / 4) ^ 4) / (∑ _i : Fin 4, ((1 : ℝ) / 4) ^ 2) = 1 / 16 := by
  simp
  norm_num

/-- 滑らかな場の比：`n` 枚が同じ `θ/4` を持てば、四次の比と二次の比の比は `1/16`。 -/
theorem smooth_ratio (n θ : ℝ) (hn : n ≠ 0) (hθ : θ ≠ 0) :
    (n * (θ / 4) ^ 4 / θ ^ 4) / (n * (θ / 4) ^ 2 / θ ^ 2) = 1 / 16 := by
  field_simp
  ring

/-- 四次形式の対角と交差への分解。 -/
theorem quartic_expand (s : Finset ι) (x y : ι → ℝ) :
    ∑ q ∈ s, (x q + y q) ^ 4
      = ∑ q ∈ s, x q ^ 4 + 4 * ∑ q ∈ s, x q ^ 3 * y q + 6 * ∑ q ∈ s, x q ^ 2 * y q ^ 2
        + 4 * ∑ q ∈ s, x q * y q ^ 3 + ∑ q ∈ s, y q ^ 4 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

end LatticeGauge.AllFacesBlocking

#print axioms LatticeGauge.AllFacesBlocking.sq_sum_fin_four_le
#print axioms LatticeGauge.AllFacesBlocking.block_energy_lower
#print axioms LatticeGauge.AllFacesBlocking.fine_energy_lower
#print axioms LatticeGauge.AllFacesBlocking.equal_split_ratio
#print axioms LatticeGauge.AllFacesBlocking.smooth_ratio
#print axioms LatticeGauge.AllFacesBlocking.quartic_expand
