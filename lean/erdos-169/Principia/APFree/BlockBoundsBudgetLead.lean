/-
  混合深さ（葉の予算 150000）のチャンク 0：wins50 の窓 #0〜#12（13 個・葉 66640）。
  骨組みは `Principia.APFree.BlockBoundsMixedDepth`（`totLoD` / `totLoD_le`）。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsMixedDepth

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

def winsE0 : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((4, 9, 4, 43046723), 7), ((4, 9, 4, 126441451), 6), ((4, 9, 4, 166789456), 6),
   ((4, 10, 5, 373926917), 6), ((4, 10, 5, 1030323481), 6), ((4, 10, 5, 1312793128), 6),
   ((6, 9, 12, 2908055903), 5), ((6, 9, 12, 8173995077), 5), ((6, 9, 12, 10531878348), 4),
   ((6, 10, 13, 24679339023), 5), ((6, 10, 13, 76553415181), 4), ((6, 10, 13, 102490453260), 4),
   ((6, 11, 15, 258114453293), 5)]

theorem winsE0_ok : ∀ w ∈ winsE0, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

set_option maxHeartbeats 40000000 in
theorem winsE0_num : 40248988842043090407985781433689310936766843623238861186915309117375262410717999441245155358609172 ≤ totLoD SC winsE0 := by decide

theorem winsE0_lower : (40248988842043090407985781433689310936766843623238861186915309117375262410717999441245155358609172 : ℚ) / 10 ^ 100 ≤ sumWin (winsE0.map Prod.fst) := by
  have h := totLoD_le SC (by norm_num [SC]) winsE0 winsE0_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast winsE0_num

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.winsE0_num
