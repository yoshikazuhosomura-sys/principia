/-
  110 段の下界のチャンク 1：窓 #10〜#26（17 個・葉 69688）。
  骨組みは `Principia.APFree.BlockBoundsMixedDepth`（`totLoD` / `totLoD_le`）。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsMixedDepth

namespace APFree.BlockBounds

set_option maxRecDepth 4000000

def winsG1 : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((12, 8, 44, 76796023404), 4), ((6, 11, 15, 258599669739), 5), ((8, 10, 26, 802510301465), 4),
   ((9, 10, 32, 2181667731859), 4), ((10, 10, 39, 6379329008589), 4), ((11, 10, 48, 18889619178333), 3),
   ((12, 10, 57, 54459109940509), 3), ((10, 11, 43, 150344381166217), 3), ((11, 11, 54, 417178812137849), 3),
   ((12, 11, 63, 1184635107236837), 3), ((13, 11, 75, 3322079016883227), 3), ((11, 12, 58, 9028343723056819), 3),
   ((12, 12, 69, 25412514760218753), 3), ((13, 12, 81, 72739639377651665), 3), ((14, 12, 93, 205083922452406195), 3),
   ((12, 13, 75, 560262414161518925), 3), ((13, 13, 90, 1624561154663602833), 3)]

theorem winsG1_ok : ∀ w ∈ winsG1, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := by decide

set_option maxHeartbeats 40000000 in
theorem winsG1_num : 5199981032954784321553881424152533573103688763700539159266128322754619532313630296084153465664304 ≤ totLoD SC winsG1 := by decide

theorem winsG1_lower : (5199981032954784321553881424152533573103688763700539159266128322754619532313630296084153465664304 : ℚ) / 10 ^ 100 ≤ sumWin (winsG1.map Prod.fst) := by
  have h := totLoD_le SC (by norm_num [SC]) winsG1 winsG1_ok
  have hSC : ((SC : ℕ) : ℚ) = 10 ^ 100 := by norm_num [SC]
  rw [hSC] at h
  refine le_trans ?_ h
  gcongr
  exact_mod_cast winsG1_num

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.winsG1_num
