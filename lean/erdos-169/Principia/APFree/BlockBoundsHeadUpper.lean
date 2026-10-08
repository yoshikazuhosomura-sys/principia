/-
  続き — 逆数和の挟み込みの Lean 化。**数値の部分**（kernel 評価）。
  骨組みは `Principia.APFree.BlockBounds`。一つの `lake build` を 3 分以内に収めるためファイルを割った。
  葉は 2¹⁶ = 65536 個。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBounds

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

/-! ### 頭 Z₀ の上界（`hiI`。kernel 評価） -/

set_option maxHeartbeats 4000000 in
theorem head_hi_num : hiI 2 SC cfH 16 1 16 0 ≤ 3004209955304942 * 10 ^ 85 := by decide

theorem head_upper :
    ∑ s ∈ BlkF 2 16 0, (1 : ℚ) / (1 + s) ≤ (3004209955304942 : ℚ) / 10 ^ 15 := by
  have h := le_hiI 2 SC (by norm_num [SC]) (by norm_num) cfH card_BlkF_zero_le 16 1 16 0
    (by norm_num) (by norm_num)
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  simp only [Nat.cast_one] at h
  refine le_trans h ?_
  have hnum : ((hiI 2 SC cfH 16 1 16 0 : ℕ) : ℚ) ≤ ((3004209955304942 * 10 ^ 85 : ℕ) : ℚ) := by
    exact_mod_cast head_hi_num
  have heq : (3004209955304942 : ℚ) / 10 ^ 15
      = ((3004209955304942 * 10 ^ 85 : ℕ) : ℚ) / 10 ^ 100 := by push_cast; ring
  rw [heq]
  gcongr

/-- **頭 Z₀ の逆数和の上界**（Z₀ そのものについて）。 -/
theorem Z0F_upper : ∑ n ∈ Z0F, (1 : ℚ) / n ≤ (3004209955304942 : ℚ) / 10 ^ 15 := by
  rw [sum_Z0F]; exact head_upper

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.head_hi_num
