/-
  尾のチャンク 1：段 4〜6（3 個・葉 47972）。`totLoP`（詰め込み個数 `cfP`）の kernel 評価。
  `外の生成器` が生成。sorry 0・native_decide 不使用。
-/
import Principia.APFree.FourTermBlockCount

namespace APFree.FourTermRecord

open APFree.BlockBounds

set_option maxRecDepth 100000

/-- 窓 `((p, q, r, a), W, d)`：詰め込み幅 `W`（`p^q < 2^W`）、深さ `d`。 -/
def tailG1 : List ((ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) :=
  [(((128, 15, 10033, 59677741029629964289916678501398751), 120, 2)),
   (((112, 16, 8203, 1372793047997888086352767435507361971), 120, 2)),
   (((138, 16, 12463, 40146120589026058845511762592851142451), 128, 2))]

theorem tailG1_ok : ∀ w ∈ tailG1, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

theorem tailG1_num : 566712570977974702498547245589735501722258670413783921596129875608610413043492771901202178048 ≤ totLoP (10 ^ 100) tailG1 := by
  decide +kernel

theorem tailG1_lower : (566712570977974702498547245589735501722258670413783921596129875608610413043492771901202178048 : ℚ) / 10 ^ 100 ≤ sumWin (tailG1.map Prod.fst) := by
  have h := totLoP_le (10 ^ 100) (by norm_num) tailG1 tailG1_ok
  have hc : ((10 ^ 100 : ℕ) : ℚ) = 10 ^ 100 := by norm_num
  rw [hc] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast tailG1_num

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.tailG1_num
