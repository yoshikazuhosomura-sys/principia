/-

  エルデシュ問題 #169。**窓分離ベルマン政策 84 段（外の表）の
  逆数和を Lean に載せる。**チャンク b（窓 15 個・葉 38953）。

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

def wins939b : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((6, 10, 13, 76553415181), 4), ((6, 10, 13, 102490453260), 4),
   ((6, 11, 15, 258114453293), 5), ((8, 10, 26, 801539868573), 4),
   ((9, 10, 32, 2179726866075), 4), ((10, 10, 39, 6375447277021), 3),
   ((11, 10, 48, 18881855715197), 3), ((12, 10, 57, 54443583014237), 3),
   ((14, 10, 80, 178101767759292), 3), ((9, 12, 39, 572357988790548), 3),
   ((10, 12, 46, 1970325472742526), 3), ((14, 11, 86, 6153963679531407), 3),
   ((12, 12, 69, 19890796879257982), 3), ((13, 12, 81, 61696203615730123), 3),
   ((14, 12, 93, 182997050928563111), 3)]

theorem wins939b_ok : ∀ w ∈ wins939b, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

set_option maxHeartbeats 40000000 in
theorem wins939b_num : 5193896371181394461429645092806851781618421393167778746084975161125641212418883378886243355841776 ≤ totLoD SC wins939b := by decide

theorem wins939b_lower :
    (5193896371181394461429645092806851781618421393167778746084975161125641212418883378886243355841776 : ℚ) / 10 ^ 100 ≤ sumWin (wins939b.map Prod.fst) := by
  have h := totLoD_le SC (by norm_num [SC]) wins939b wins939b_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast wins939b_num

end APFree.BellmanLower

/-! ### 公理の確認 -/

#print axioms APFree.BellmanLower.wins939b_lower
