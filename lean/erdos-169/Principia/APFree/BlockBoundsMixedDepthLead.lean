/-
  **深さを上げた先頭 21 窓**（〜21段の頭。葉 31142）
  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsMixedDepth

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

def winsD50a : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((4, 9, 4, 43046723), 6), ((4, 9, 4, 126441451), 5), ((4, 9, 4, 166789456), 5),
   ((4, 10, 5, 373926917), 6), ((4, 10, 5, 1030323481), 5), ((4, 10, 5, 1312793128), 5),
   ((6, 9, 12, 2908055903), 4), ((6, 9, 12, 8173995077), 4), ((6, 9, 12, 10531878348), 4),
   ((6, 10, 13, 24679339023), 4), ((6, 10, 13, 76553415181), 4), ((6, 10, 13, 102490453260), 4),
   ((6, 11, 15, 258114453293), 4), ((8, 10, 26, 801539868573), 3), ((12, 9, 50, 2179726866075), 3),
   ((10, 10, 39, 6160565433961), 3), ((11, 10, 48, 18452092029077), 3), ((12, 10, 57, 53584055641997), 3),
   ((10, 11, 43, 148594272569193), 3), ((11, 11, 54, 413678594943801), 3), ((12, 11, 63, 1177634672848741), 3)]

theorem winsD50a_ok : ∀ w ∈ winsD50a, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

set_option maxHeartbeats 16000000 in
theorem winsD50a_num : 42815263220933204914746019542392588485849598196462345611012826354462464167697216729151737521665776 ≤ totLoD SC winsD50a := by decide

theorem winsD50a_lower : (42815263220933204914746019542392588485849598196462345611012826354462464167697216729151737521665776 : ℚ) / 10 ^ 100 ≤ sumWin (winsD50a.map Prod.fst) := by
  have h := totLoD_le SC (by norm_num [SC]) winsD50a winsD50a_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast winsD50a_num

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.winsD50a_num
