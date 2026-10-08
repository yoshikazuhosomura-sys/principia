/-
  結び — **窓ごとに深さを配った版の下界**。
  頭 Z₀（`APFreeBlockBoundsHeadLower`、深さ 16 の全展開）＋ wins50 の先頭 21 窓（深さを上げた）
  ＋ wins50 の残り 57 窓（深さ 2）＋ wins100b の 93 窓（深さ 2、`APFreeBlockBoundsWindows100` を再利用）。
  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsMixedDepthLead
import Principia.APFree.BlockBoundsMixedDepthRest
import Principia.APFree.BlockBoundsWindows50
import Principia.APFree.BlockBoundsWindows100

namespace APFree.BlockBounds

/-- 深さの札を外すと、元の窓の一覧 `wins50` に戻る。 -/
theorem winsD50_map : winsD50a.map Prod.fst ++ winsD50b.map Prod.fst = wins50 := by rfl

/-- wins50 の逆数和の下界（混合深さ版）。 -/
theorem blocksD50_lower :
    (43283948856857867420511550325534660371680914834526227400134364648222938331259787100238701883091696 : ℚ) / 10 ^ 100 ≤ sumWin wins50 := by
  have h : sumWin wins50 = sumWin (winsD50a.map Prod.fst) + sumWin (winsD50b.map Prod.fst) := by
    rw [← winsD50_map, sumWin_append]
  rw [h]
  have ha := winsD50a_lower
  have hb := winsD50b_lower
  have : (43283948856857867420511550325534660371680914834526227400134364648222938331259787100238701883091696 : ℚ) / 10 ^ 100 = (42815263220933204914746019542392588485849598196462345611012826354462464167697216729151737521665776 : ℚ) / 10 ^ 100 + (468685635924662505765530783142071885831316638063881789121538293760474163562570371086964361425920 : ℚ) / 10 ^ 100 := by norm_num
  rw [this]
  exact add_le_add ha hb

/-- **本ファイルの結論**：ロールアウト政策 100 段の Wróblewski 構成の逆数和は
    **3.0085383518390 を超える**。（APFreeBlockBoundsDigitCount の `total_lower` の 3.0085286163 からの改良。
    上げたのは接頭辞展開の深さだけで、対象の集合は同一である。） -/
theorem total_lower3 :
    (30085383518390 : ℚ) / 10 ^ 13
      < (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins50 + sumWin wins100b := by
  have h1 : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := Z0F_lower
  have h2 := blocksD50_lower
  have h3 := blocks100b_lower
  have h4 : (30085383518390 : ℚ) / 10 ^ 13
      < (3004209955304941 : ℚ) / 10 ^ 15
        + (43283948856857867420511550325534660371680914834526227400134364648222938331259787100238701883091696 : ℚ) / 10 ^ 100
        + (16484531567385067650538697947409403393169352146330921496288812445275830441250329638192807936 : ℚ) / 10 ^ 100 := by
    norm_num
  linarith

/-- 記録 3.00849 との比較（`total_lower3` の系）。 -/
theorem record_3_00849' :
    (300849 : ℚ) / 10 ^ 5 < (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins50 + sumWin wins100b := by
  have h := total_lower3
  have : (300849 : ℚ) / 10 ^ 5 < (30085383518390 : ℚ) / 10 ^ 13 := by norm_num
  linarith

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.total_lower3
#print axioms APFree.BlockBounds.record_3_00849'
