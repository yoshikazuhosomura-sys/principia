/-
  尾のチャンク 0：段 1〜3（3 個・葉 22496）。`totLoP`（詰め込み個数 `cfP`）の kernel 評価。
  `外の生成器` が生成。sorry 0・native_decide 不使用。
-/
import Principia.APFree.FourTermBlockCount

namespace APFree.FourTermRecord

open APFree.BlockBounds

set_option maxRecDepth 100000

/-- 窓 `((p, q, r, a), W, d)`：詰め込み幅 `W`（`p^q < 2^W`）、深さ `d`。 -/
def tailG0 : List ((ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) :=
  [(((68, 15, 2833, 4527528777914432254565203631367), 104, 2)),
   (((84, 15, 4318, 99213526382892320721589343421783), 112, 2)),
   (((104, 15, 6628, 2389955271945492376354262646007153), 112, 2))]

theorem tailG0_ok : ∀ w ∈ tailG0, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

theorem tailG0_num : 2025349202092829718291646178344522456434343454516869592458830569500471744380566187451976196096 ≤ totLoP (10 ^ 100) tailG0 := by
  decide +kernel

theorem tailG0_lower : (2025349202092829718291646178344522456434343454516869592458830569500471744380566187451976196096 : ℚ) / 10 ^ 100 ≤ sumWin (tailG0.map Prod.fst) := by
  have h := totLoP_le (10 ^ 100) (by norm_num) tailG0 tailG0_ok
  have hc : ((10 ^ 100 : ℕ) : ℚ) = 10 ^ 100 := by norm_num
  rw [hc] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast tailG0_num

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.tailG0_num
