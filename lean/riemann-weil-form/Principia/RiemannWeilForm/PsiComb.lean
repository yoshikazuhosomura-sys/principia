/-
  `Ψ` 座標（アルキメデス密度の巻き数）と、歯と零点のマッチングの有限の核。

  背景（数学の側。本ファイルの主張には使わない）：
  明示公式のアルキメデス密度を `g(r) = Re ψ(1/4+ir/2) − log π` とし、その巻き数を
  `Ψ(r) = ∫_0^r g(u) du` と置くと `Ψ = 2θ`（θ は Riemann–Siegel の theta）であり、
  `Ψ` が減る区間は `g < 0` の帯 `[0, r₀)`（r₀ = 6.2898359888…）、`Ψ ≡ 0 (mod 2π)` の点は Gram 点である。
  「歯」（窓の自由度）に零点を入れるマッチングについて、次の二つだけが有限の事実である。

  * `PsiComb.strictAntiOn_of_neg` : 密度が負の区間で `Ψ` は狭義減少（＝歯が一本も無い区間）
  * `PsiComb.strictMonoOn_of_pos` : 密度が正の区間で `Ψ` は狭義増加（＝歯が等間隔に並ぶ座標）
  * `PsiComb.crowded_add_card`    : 混雑 + 歯の本数 = 零点の個数 + 空の歯の本数（恒等式）
  * `PsiComb.empty_eq_crowded_add_excess` : 空 = 混雑 + 余裕（容量 ≥ 需要 のとき）
  * `PsiComb.excess_not_determine_crowded` : 余裕が同じでも混雑は違う（`n(L)` と `c(L)` は別の量）

  Lean が言っていないこと：`g` の符号（`r₀` の一意性）・`Ψ = 2θ` の恒等式・
  零点の位置・Gram の法則・GUE・`n(L) = e^{2L} − 7/8`。
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PsiComb

open Finset

/-! ## 1. `Ψ` 座標の単調性 — 符号帯は「歯が無い区間」である -/

/-- 密度が正の区間では巻き数 `Ψ` は狭義増加。
    仮定 `hd` は微積分学の基本定理（`Ψ' = g`）を仮定として置いたもの。 -/
theorem strictMonoOn_of_pos {Ψ g : ℝ → ℝ} {r₀ : ℝ}
    (hd : ∀ x, HasDerivAt Ψ (g x) x) (hpos : ∀ x, r₀ < x → 0 < g x) :
    StrictMonoOn Ψ (Set.Ici r₀) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici r₀) ?_ ?_
  · exact fun x _ => ((hd x).differentiableAt.continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    exact hpos x hx

/-- 密度が負の区間では巻き数 `Ψ` は狭義減少。`[0, r₀)` がこれに当たり、
    そこには `Ψ ≡ 0 (mod 2π)` の歯が新たに生えない。 -/
theorem strictAntiOn_of_neg {Ψ g : ℝ → ℝ} {r₀ : ℝ}
    (hd : ∀ x, HasDerivAt Ψ (g x) x) (hneg : ∀ x, x < r₀ → g x < 0) :
    StrictAntiOn Ψ (Set.Iic r₀) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic r₀) ?_ ?_
  · exact fun x _ => ((hd x).differentiableAt.continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    rw [(hd x).deriv]
    exact hneg x hx

/-- 減少区間の像の幅は端点の差で決まる（低帯の `Ψ` 幅が `L` に依らない定数である、という
    計算の言明の有限の骨）。 -/
theorem anti_image_width {Ψ : ℝ → ℝ} {a r₀ : ℝ} (h : StrictAntiOn Ψ (Set.Iic r₀))
    (ha : a < r₀) : Ψ r₀ < Ψ a :=
  h (Set.mem_Iic.mpr ha.le) (Set.mem_Iic.mpr le_rfl) ha

/-! ## 2. マッチングの恒等式 — 「空の歯」と「混雑した零点」と「余裕」 -/

variable {ι : Type*} [DecidableEq ι]

/-- **恒等式**：`n j` を歯 `j` に入った零点の個数とすると
    `Σ_j (n j − 1)⁺ + (歯の本数) = (零点の個数) + (空の歯の本数)`。
    ℕ の切り捨て減法で書いてあるので減算は現れない。 -/
theorem crowded_add_card (T : Finset ι) (n : ι → ℕ) :
    (∑ j ∈ T, (n j - 1)) + T.card = (∑ j ∈ T, n j) + (T.filter (fun j => n j = 0)).card := by
  classical
  rw [card_filter, card_eq_sum_ones T, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  cases hj : n j with
  | zero => simp [hj]
  | succ k => simp [hj]

/-- 容量（歯の本数 `M`）が需要（零点の個数 `N`）以上のとき、
    `空の歯 = 混雑 + 余裕`。**`n(L)` は「余裕」の側であって「混雑」ではない。** -/
theorem empty_eq_crowded_add_excess (T : Finset ι) (n : ι → ℕ)
    (h : (∑ j ∈ T, n j) ≤ T.card) :
    (T.filter (fun j => n j = 0)).card
      = (∑ j ∈ T, (n j - 1)) + (T.card - (∑ j ∈ T, n j)) := by
  have := crowded_add_card T n
  omega

/-- 余裕（容量 − 需要）が同じでも混雑は違う：`M = 3`, `N = 2` の二つの配置で
    混雑が `0` と `1`。**したがって余裕から混雑は決まらない**——
    `n(L)`（余裕）と `c(L)`（混雑）は別の量である。 -/
theorem excess_not_determine_crowded :
    ∃ n₁ n₂ : ℕ → ℕ,
      (∑ j ∈ range 3, n₁ j) = (∑ j ∈ range 3, n₂ j) ∧
      (∑ j ∈ range 3, (n₁ j - 1)) = 0 ∧ (∑ j ∈ range 3, (n₂ j - 1)) = 1 := by
  refine ⟨fun j => if j = 2 then 0 else 1, fun j => if j = 0 then 2 else 0, ?_, ?_, ?_⟩ <;> decide

/-- 上の二つの配置で、恒等式の両辺が実際に合っていること（空の歯 1 個 対 2 個）。 -/
theorem excess_example_check :
    ((range 3).filter (fun j => (if j = 2 then 0 else 1) = 0)).card = 1 ∧
    ((range 3).filter (fun j => (if j = 0 then 2 else 0) = 0)).card = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

end PsiComb

#print axioms PsiComb.strictMonoOn_of_pos
#print axioms PsiComb.strictAntiOn_of_neg
#print axioms PsiComb.anti_image_width
#print axioms PsiComb.crowded_add_card
#print axioms PsiComb.empty_eq_crowded_add_excess
#print axioms PsiComb.excess_not_determine_crowded
#print axioms PsiComb.excess_example_check
