/-
  結び — 混合深さ（葉の予算 150000）での逆数和の下界。
  頭 Z₀（深さ 16 の全展開）＋ wins50 の 2 チャンク（深さを配った）＋ wins100b（深さ 2）。
  APFreeBlockBoundsMixedDepth の `total_lower3`（3.0085383518390）をさらに押した版。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsBudgetLead
import Principia.APFree.BlockBoundsBudgetRest
import Principia.APFree.BlockBoundsWindows50
import Principia.APFree.BlockBoundsWindows100

namespace APFree.BlockBounds

/-- 深さの札を外すと、元の窓の一覧 `wins50` に戻る。 -/
theorem winsE_map : winsE0.map Prod.fst ++ winsE1.map Prod.fst = wins50 := by rfl

theorem blocksE50_lower : (43284244468095212535650764376331465229472132574172031712364375959152488652625996128290426205769812 : ℚ) / 10 ^ 100 ≤ sumWin wins50 := by
  have h : sumWin wins50 = sumWin (winsE0.map Prod.fst) + sumWin (winsE1.map Prod.fst) := by
    rw [← winsE_map, sumWin_append]
  rw [h]
  have he : (43284244468095212535650764376331465229472132574172031712364375959152488652625996128290426205769812 : ℚ) / 10 ^ 100 = (40248988842043090407985781433689310936766843623238861186915309117375262410717999441245155358609172 : ℚ) / 10 ^ 100 + (3035255626052122127664982942642154292705288950933170525449066841777226241907996687045270847160640 : ℚ) / 10 ^ 100 := by norm_num
  rw [he]
  have h0 := winsE0_lower
  have h1 := winsE1_lower
  exact add_le_add h0 h1

/-- **本ファイルの到達点**：ロールアウト政策 100 段の Wróblewski 構成の逆数和は **3.0085383814002 を超える**。
    Python の挟み込み（jmax = 600000）3.0085383885637 との差は 7.16e-09 である。 -/
theorem total_lower4 :
    (30085383814002 : ℚ) / 10 ^ 13
      < (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins50 + sumWin wins100b := by
  have h1 : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := Z0F_lower
  have h2 := blocksE50_lower
  have h3 := blocks100b_lower
  have h4 : (30085383814002 : ℚ) / 10 ^ 13
      < (3004209955304941 : ℚ) / 10 ^ 15
        + (43284244468095212535650764376331465229472132574172031712364375959152488652625996128290426205769812 : ℚ) / 10 ^ 100
        + (16484531567385067650538697947409403393169352146330921496288812445275830441250329638192807936 : ℚ) / 10 ^ 100 := by
    norm_num
  linarith

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.total_lower4
