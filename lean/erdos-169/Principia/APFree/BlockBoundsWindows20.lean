/-
  続き — ブロック側の数値。**最初の 20 段の窓（25 個）を深さ 2 で展開**し、
  頭 Z₀（`APFreeBlockBoundsHeadLower`）と足すと **記録 3.00849 を超える**ことを機械検査する。

  ここまでで使うのは `APFreeBlockBoundsDigitCount` の `totLo_le`（＝桁 DP の表から個数を取る一般形）だけで、
  外から与える証明義務は無い。sorry 0・native_decide 不使用。

  窓の一覧は (p, q, r, a)。a は Wróblewski 構成の offset。
  段は 20 段（M=1 の段は窓 1 個、M=3 の段は窓 3 個なので、窓は全部で 25 個）。
-/
import Principia.APFree.BlockBoundsDigitCount
import Principia.APFree.BlockBoundsHeadLower

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

/-- 最初の 20 段ぶんの窓（25 個）。 -/
def wins20 : List (ℕ × ℕ × ℕ × ℕ) :=
  [(4, 9, 4, 43046723), (4, 9, 4, 126441451), (4, 9, 4, 166789456),
   (4, 10, 5, 373926917), (4, 10, 5, 1030323481), (4, 10, 5, 1312793128),
   (6, 9, 12, 2908055903), (6, 9, 12, 8173995077), (6, 9, 12, 10531878348),
   (6, 10, 13, 24679339023), (6, 10, 13, 76553415181), (6, 10, 13, 102490453260),
   (6, 11, 15, 258114453293), (8, 10, 26, 801539868573), (12, 9, 50, 2179726866075),
   (10, 10, 39, 6160565433961), (11, 10, 48, 18452092029077),
   (12, 10, 57, 53584055641997), (10, 11, 43, 148594272569193),
   (11, 11, 54, 413678594943801), (12, 11, 63, 1177634672848741),
   (13, 11, 75, 3308078148107035), (14, 11, 86, 9000341985504435),
   (12, 12, 69, 23559740513247861), (13, 12, 81, 69034090883709881)]

theorem wins20_ok : ∀ w ∈ wins20, 1 ≤ w.1 ∧ 0 < w.2.2.2 := by decide

set_option maxHeartbeats 4000000 in
/-- kernel 評価（葉は深さ 2、桁 DP の表は各 (p,q) につき一度）。 -/
theorem blocks20_num :
    42984636511592348461750952954335943986604914338742261103165671484416031770457065779688310009489536
      ≤ totLo SC 2 wins20 := by decide

theorem blocks20_lower :
    (42984636511592348461750952954335943986604914338742261103165671484416031770457065779688310009489536 : ℚ)
      / 10 ^ 100 ≤ sumWin wins20 := by
  have h := totLo_le SC (by norm_num [SC]) 2 wins20 wins20_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  have hnum :
      ((42984636511592348461750952954335943986604914338742261103165671484416031770457065779688310009489536 : ℕ) : ℚ)
        ≤ ((totLo SC 2 wins20 : ℕ) : ℚ) := by exact_mod_cast blocks20_num
  gcongr
  exact_mod_cast blocks20_num

/-- **本組の結論（検証待ちの候補ではなく、機械検査済みの下界）**：
    頭 Z₀ と最初の 20 段の窓だけで、逆数和は Wróblewski 1984 の記録 3.00849 を超える。 -/
theorem record_beaten :
    (300849 : ℚ) / 10 ^ 5 < (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins20 := by
  have h1 : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := Z0F_lower
  have h2 := blocks20_lower
  have h3 : (300849 : ℚ) / 10 ^ 5
      < (3004209955304941 : ℚ) / 10 ^ 15
        + (42984636511592348461750952954335943986604914338742261103165671484416031770457065779688310009489536
            : ℚ) / 10 ^ 100 := by
    norm_num
  linarith

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.blocks20_num
#print axioms APFree.BlockBounds.record_beaten
