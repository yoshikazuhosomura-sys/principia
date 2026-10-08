/-
  結び — **100 段すべて**の窓とその頭 Z₀ を合わせた、逆数和の機械検査済みの下界。
  `APFreeBlockBoundsHeadLower`（頭）・`APFreeBlockBoundsWindows50`（〜50段）・`APFreeBlockBoundsWindows100`（〜100段）を足すだけ。
  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsWindows50
import Principia.APFree.BlockBoundsWindows100

namespace APFree.BlockBounds

/-- **本ファイルの結論**：ロールアウト政策 100 段の Wróblewski 構成の逆数和は
    **3.0085286163 を超える**。とくに Wróblewski 1984 の記録 **3.00849 を超える**。
    （頭 Z₀ は `APFreeBlockBoundsHeadLower`、ブロックは深さ 2 の接頭辞展開＋桁 DP の表。すべて kernel 評価。） -/
theorem total_lower :
    (30085286163 : ℚ) / 10 ^ 10
      < (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins50 + sumWin wins100b := by
  have h1 : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := Z0F_lower
  have h2 := blocks50_lower
  have h3 := blocks100b_lower
  have h4 : (30085286163 : ℚ) / 10 ^ 10
      < (3004209955304941 : ℚ) / 10 ^ 15
        + (43186594426047909037485327285886450590907364648618651131920393748013061546682393613679261480657280 : ℚ) / 10 ^ 100
        + (16484531567385067650538697947409403393169352146330921496288812445275830441250329638192807936 : ℚ) / 10 ^ 100 := by
    norm_num
  linarith

/-- 記録 3.00849 との比較（`total_lower` の系）。 -/
theorem record_3_00849 :
    (300849 : ℚ) / 10 ^ 5 < (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins50 + sumWin wins100b := by
  have h := total_lower
  have : (300849 : ℚ) / 10 ^ 5 < (30085286163 : ℚ) / 10 ^ 10 := by norm_num
  linarith

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.total_lower
#print axioms APFree.BlockBounds.record_3_00849
