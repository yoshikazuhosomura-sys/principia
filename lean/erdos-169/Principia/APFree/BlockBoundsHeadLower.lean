/-
  続き — 逆数和の挟み込みの Lean 化。**数値の部分**（kernel 評価）。
  骨組みは `Principia.APFree.BlockBounds`。一つの `lake build` を 3 分以内に収めるためファイルを割った。
  葉は 2¹⁶ = 65536 個。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBounds

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

/-! ### 頭 Z₀ の下界（`loI`。kernel 評価 約 107 秒） -/

set_option maxHeartbeats 4000000 in
theorem head_lo_num : 3004209955304941 * 10 ^ 85 ≤ loI 2 SC cfH 16 1 16 0 := by decide

theorem head_lower :
    (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ s ∈ BlkF 2 16 0, (1 : ℚ) / (1 + s) := by
  have h := loI_le 2 SC (by norm_num [SC]) (by norm_num) cfH cfH_le 16 1 16 0 (by norm_num)
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  simp only [Nat.cast_one] at h
  refine le_trans ?_ h
  have hnum : ((3004209955304941 * 10 ^ 85 : ℕ) : ℚ) ≤ ((loI 2 SC cfH 16 1 16 0 : ℕ) : ℚ) := by
    exact_mod_cast head_lo_num
  have heq : (3004209955304941 : ℚ) / 10 ^ 15
      = ((3004209955304941 * 10 ^ 85 : ℕ) : ℚ) / 10 ^ 100 := by push_cast; ring
  rw [heq]
  gcongr

/-- **頭 Z₀ の逆数和の下界**（Z₀ そのものについて）。 -/
theorem Z0F_lower : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := by
  rw [sum_Z0F]; exact head_lower

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.head_lo_num
