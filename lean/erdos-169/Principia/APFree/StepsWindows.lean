/-
  **100 段（ロールアウト）の窓の一覧が、100 段そのものから出ていること。**

  `APFreeStepsRegroupedLower` の §4 で 110 段について閉じたことの、100 段版である。

  【なぜ要るか】
    `APFreeBlockBoundsWindows50.wins50` と `APFreeBlockBoundsWindows100.wins100b`（合わせて窓 171 個）は Python が書き出した
    リテラルである。それが `APFreePolicyRollout` の段（`steps793` の (z,t,M)）とブロック（`blocks793` の
    (p,q,r,t,桁)）から**置き方の規則どおりに出る**ことは、これまで `外の生成器` が確かめた
    きりで、Lean の中には無かった。`APFreeChainRecord.chain844` は「窓と段の (p,n,r,t) が一致し、
    窓が次の箱に収まり、段ごとの (W) が通る」ことを見るが、**offset が規則から出た値である
    ことは見ていない**（見ているのは「その offset で (W) が通る」ことである）。
    表が配布物と合っていないのと同じ型の穴なので埋める。

  【置き方の規則は二度書かない】
    `winsOfStep` は `APFreeStepsRegroupedLower`（110 段）のものをそのまま使う。M=3 の枝が
    `APFree.WindowSeparationM3.W3` の左端そのものであることも、ここで示す（`winsOfStep_M3_eq_W3`）。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.StepsRegroupedLower
import Principia.APFree.PolicyRollout
import Principia.APFree.BlockBoundsWindows50
import Principia.APFree.BlockBoundsWindows100

namespace APFree.StepsWindows

open APFree.BlockBounds APFree.StepsRegrouped

set_option maxRecDepth 4000000

/-- `winsOfStep` の `M = 3` の枝が `APFree.WindowSeparationM3.W3` の左端そのものであること
    （置き方の規則を二度書いていないことの確認）。 -/
theorem winsOfStep_M3_eq_W3 (z t : ℤ) (p q r : ℕ) (hz : 0 ≤ z) (ht : 0 ≤ t) :
    ((winsOfStep (z, t, 3) (p, q, r)).map fun w => ((w.2.2.2 : ℕ) : ℤ))
      = [(APFree.WindowSeparationM3.W3 z t).l 1, (APFree.WindowSeparationM3.W3 z t).l 2, (APFree.WindowSeparationM3.W3 z t).l 3] := by
  obtain ⟨h1, h2, h3⟩ := APFree.WindowSeparationM3.M3_offsets z t
  have hm : (0 : ℤ) ≤ max z t := le_max_of_le_left hz
  rw [h1, h2, h3]
  simp only [winsOfStep, List.map_cons, List.map_nil]
  norm_num
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- 100 段の段とブロックの対（`APFreePolicyRollout` の二つの表）。 -/
def stepsPaired100 : List ((ℤ × ℤ × ℕ) × (ℕ × ℕ × ℕ)) :=
  List.zip APFree.PolicyRollout.steps793 (APFree.PolicyRollout.blocks793.map fun s => (s.1, s.2.1, s.2.2.1))

theorem stepsPaired100_length : stepsPaired100.length = 100 := by decide

/-- **`APFree.PolicyRollout` の二つの表の t は 100 段すべてで一致する**
    （`steps793` は鎖と (W) の出所、`blocks793` は maxelt の出所）。 -/
theorem t_agree100 :
    (List.zip APFree.PolicyRollout.steps793 APFree.PolicyRollout.blocks793).all
      (fun x => decide (x.1.2.1 = (x.2.2.2.2.1 : ℤ))) = true := by decide

/-- **M は 1, 2, 3 のいずれかである**（`winsOfStep` の空の枝に落ちる段が無い）。 -/
theorem M_le_three :
    APFree.PolicyRollout.steps793.all (fun s => decide (s.2.2 = 1 ∨ s.2.2 = 2 ∨ s.2.2 = 3)) = true := by
  decide

/-- **本ファイルの結論**：`wins50 ++ wins100b` は、100 段の鎖とブロックから
    置き方の規則どおりに出てくる（171 窓が逐語一致）。 -/
theorem wins100_from_steps :
    (stepsPaired100.flatMap fun x => winsOfStep x.1 x.2) = wins50 ++ wins100b := by decide

/-- ゆえに `APFreeWindowsDisjoint.winsAll`（頭 ＋ 171 窓）も 100 段そのものから出る。 -/
theorem winsAll_from_steps :
    (2, 16, 0, 1) :: (stepsPaired100.flatMap fun x => winsOfStep x.1 x.2)
      = APFree.WindowsDisjoint.winsAll := by
  rw [wins100_from_steps, APFree.WindowsDisjoint.winsAll]

end APFree.StepsWindows

/-! ### 公理の確認 -/

#print axioms APFree.StepsWindows.wins100_from_steps
#print axioms APFree.StepsWindows.winsAll_from_steps
#print axioms APFree.StepsWindows.winsOfStep_M3_eq_W3
#print axioms APFree.StepsWindows.t_agree100
#print axioms APFree.StepsWindows.M_le_three
#print axioms APFree.StepsWindows.stepsPaired100_length
