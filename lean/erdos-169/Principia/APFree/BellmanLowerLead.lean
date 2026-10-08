/-

  エルデシュ問題 #169。**窓分離ベルマン政策 84 段（外の表）の
  逆数和を Lean に載せる。**チャンク a（窓 10 個・葉 37952）。

  骨組みは既存のまま使う（新しい証明の道具は入れていない）：
    `APFree.BlockBounds.totLoD` / `totLoD_le`（APFreeBlockBoundsMixedDepth・窓ごとに深さを変えた下界）
    `APFree.BlockBounds.loI` / `window_lower`（APFreeBlockBounds・APFreeBlockBoundsDigitCount・一窓の下界）
  本ファイルがするのは **kernel 評価一つ**である。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.WindowsDisjoint

namespace APFree.BellmanLower

open APFree.BlockBounds

set_option maxRecDepth 4000000

def wins939a : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((4, 9, 4, 43046723), 6), ((4, 9, 4, 126441451), 6),
   ((4, 9, 4, 166789456), 6), ((4, 10, 5, 373926917), 6),
   ((4, 10, 5, 1030323481), 6), ((4, 10, 5, 1312793128), 5),
   ((6, 9, 12, 2908055903), 5), ((6, 9, 12, 8173995077), 4),
   ((6, 9, 12, 10531878348), 4), ((6, 10, 13, 24679339023), 5)]

theorem wins939a_ok : ∀ w ∈ wins939a, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

set_option maxHeartbeats 40000000 in
theorem wins939a_num : 37924666165427113428187689763969464349141715971032471707513576607346637567564783658796733178297800 ≤ totLoD SC wins939a := by decide

theorem wins939a_lower :
    (37924666165427113428187689763969464349141715971032471707513576607346637567564783658796733178297800 : ℚ) / 10 ^ 100 ≤ sumWin (wins939a.map Prod.fst) := by
  have h := totLoD_le SC (by norm_num [SC]) wins939a wins939a_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast wins939a_num

end APFree.BellmanLower

/-! ### 公理の確認 -/

#print axioms APFree.BellmanLower.wins939a_lower
