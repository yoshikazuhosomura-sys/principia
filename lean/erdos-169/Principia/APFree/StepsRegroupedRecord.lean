/-
  その2 — **110 段の setA と 3-AP-free を一本の定理にする。**

  100 段では `APFreeChainRecord` が同じことをしている（`setA_apfree_and_lower`）。
  110 段にはこの層が無かった。
  骨組み（`regroup` / `stepChk` / `chainChk` / `growZ` / `grow_apfree` /
  `unionWZ_eq_coe` / 頭 Z₀ の補題）は `APFreeChainRecord` のものを一つも書き換えずに使う。
  違うのは流し込むデータだけ：

    段とブロック : `APFree.StepsSeparated.steps`（鎖と (W) の 110 段）× `APFree.StepsMaxElement.steps`（maxelt の 110 段）
    窓 : `APFree.StepsRegrouped.wins110`（128 個。`APFreeStepsRegroupedWindows`）

  `chainChk` が呼ぶ `APFree.PolicyRollout.nextZ793` は置き方の式そのもの（M=1,2,3 の三式）なので、
  100 段でも 110 段でも同じものが使える。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.ChainRecord
import Principia.APFree.StepsRegroupedLower

namespace APFree.StepsRegrouped

open APFree.WindowSeparation APFree.StepsMaxElement APFree.BlockBounds APFree.ChainRecord

set_option maxRecDepth 4000000

/-- 110 段ぶんの (段 × ブロック × 窓)。**窓は `APFreeStepsRegroupedWindows` のもの、
    段とブロックは `APFreeStepsSeparated` と `APFreeStepsMaxElement` のもの**——三つの表がここで一つになる。 -/
def groups1105 : List Group :=
  regroup (List.zip APFree.StepsSeparated.steps APFree.StepsMaxElement.steps) wins110

set_option maxHeartbeats 4000000 in
/-- **機械検査**（鎖の整合・最大元・照合・箱・窓分離をまとめて一つの `decide`）。 -/
theorem chain1105 : chainChk groups1105 21523361 = true := by decide

theorem groups1105_flat : groups1105.flatMap (fun g => g.2) = wins110 := by
  refine regroup_flat _ _ ?_
  decide

theorem grow_eq_setA110 :
    growZ (winZ (2, 16, 0, 1)) groups1105 = {x : ℤ | ∃ n ∈ setA110, x = (n : ℤ)} := by
  rw [growZ_eq, groups1105_flat]
  have hw : winZ (2, 16, 0, 1) ∪ unionWZ wins110 = unionWZ winsAll110 := rfl
  rw [hw, setA110]
  exact unionWZ_eq_coe winsAll110 winsAll110_p

/-- **110 段の構成 A は 3-AP を含まない**
    （Wróblewski 1984 Lemma 1 ＋ 定理W ＋ 110 段の鎖）。 -/
theorem setA110_apfree : IsThreeAPFree {x : ℤ | ∃ n ∈ setA110, x = (n : ℤ)} := by
  rw [← grow_eq_setA110]
  exact grow_apfree groups1105 (winZ (2, 16, 0, 1)) 21523361 head_apfree head_box chain1105

/-- **本ファイルの主定理（110 段の機械検証を単一の型に）**：
    率基準 110 段の構成 A は 3-AP-free であり、かつその逆数和は
    **3.0085326654815 を超える**。 -/
theorem setA110_apfree_and_lower :
    IsThreeAPFree {x : ℤ | ∃ n ∈ setA110, x = (n : ℤ)} ∧
      (30085326654815 : ℚ) / 10 ^ 13 < ∑ x ∈ setA110, (1 : ℚ) / x :=
  ⟨setA110_apfree, setA110_lower⟩

/-- 記録との比較まで含めた形。 -/
theorem setA110_apfree_and_beats_record :
    IsThreeAPFree {x : ℤ | ∃ n ∈ setA110, x = (n : ℤ)} ∧
      (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ setA110, (1 : ℚ) / x :=
  ⟨setA110_apfree, setA110_beats_record⟩

end APFree.StepsRegrouped

/-! ### 公理の確認 -/

#print axioms APFree.StepsRegrouped.setA110_apfree_and_beats_record
#print axioms APFree.StepsRegrouped.setA110_apfree_and_lower
#print axioms APFree.StepsRegrouped.setA110_apfree
#print axioms APFree.StepsRegrouped.chain1105
