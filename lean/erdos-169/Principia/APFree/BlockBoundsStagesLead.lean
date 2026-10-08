/-
  110 段の下界のチャンク 0：窓 #0〜#9（10 個・葉 49984）。
  骨組みは `Principia.APFree.BlockBoundsMixedDepth`（`totLoD` / `totLoD_le`）。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsMixedDepth

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

def winsG0 : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((4, 9, 4, 43046723), 7), ((4, 9, 4, 126441451), 6), ((4, 9, 4, 166789456), 6),
   ((4, 10, 5, 373926917), 6), ((4, 10, 5, 1030323481), 6), ((4, 10, 5, 1312793128), 6),
   ((6, 9, 12, 2908055903), 5), ((6, 9, 12, 8173995077), 4), ((6, 9, 12, 10531878348), 4),
   ((6, 10, 13, 24679339023), 5)]

theorem winsG0_ok : ∀ w ∈ winsG0, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

set_option maxHeartbeats 40000000 in
theorem winsG0_num : 37924688550629421041273070823940415524943515010446650481463083774329463469512659327712784563404660 ≤ totLoD SC winsG0 := by decide

theorem winsG0_lower : (37924688550629421041273070823940415524943515010446650481463083774329463469512659327712784563404660 : ℚ) / 10 ^ 100 ≤ sumWin (winsG0.map Prod.fst) := by
  have h := totLoD_le SC (by norm_num [SC]) winsG0 winsG0_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast winsG0_num

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.winsG0_num
