/-

  エルデシュ問題 #169。**窓分離ベルマン政策 84 段について、
  「3-AP-free であること」と「逆数和の下界」を一本の定理にする。**

  【ここまでの位置】
    ・`APFreeBellmanPolicy`：84 段の (W)〈窓分離〉と maxelt〈t が Blk の最大元〉を通した。
    ・`APFreeBellmanLower`：84 段の集合 `setA939` の逆数和が 3.0085385 を超えることを通した。
    しかし二つは**別の定理**であり、`APFreeChainRecord` が 100 段について持っているような
    **「IsThreeAPFree setA ∧ 3.00849 < Σ1/x」という単一の主定理は 84 段には無かった**
    （報告 §APFreeBellmanLower (6) が「残した宿題」と書いた点）。本ファイルがそこを閉じる。

  【何を新しく書いたか】**新しい証明の道具は一つも入れていない。**
    `APFreeChainRecord` の `regroup` / `stepChk` / `chainChk` / `grow_apfree` / `unionWZ_eq_coe` を
    そのまま使い、流し込むデータだけを 84 段のものに替えた：
      段と ブロック = `APFree.BellmanPolicy.steps` と `APFree.BellmanPolicy.steps774`（84 段）
      窓 = `APFree.BellmanLower.wins939`（160 個）
    したがって本ファイルの中身は **kernel 評価二つ（`chain959` と `groups_flat959`）＋結び**である。

  【走らせる前に Python で照合を先に見た】`exp/外の生成器`：
    Σ M = 160 = 窓の数／鎖の整合／(p,q,r) の一致／a + t ≤ nextZ／sepL の (M+1)³ 三つ組、
    **破れ 0 件**。Lean はそれを kernel で見直す。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.ChainRecord
import Principia.APFree.BellmanPolicy
import Principia.APFree.BellmanLower

namespace APFree.BellmanRecord

open APFree.WindowSeparation APFree.StepsMaxElement APFree.BlockBounds APFree.ChainRecord

set_option maxRecDepth 4000000

/-! ## 1. 84 段のデータを `APFreeChainRecord` の型に流し込む -/

/-- 段 `(z,t,M)`（`APFreeBellmanPolicy`）× ブロック `(p,q,r,t,桁)`（`APFreeBellmanPolicy`）× 窓（`APFreeBellmanLower`）。
    窓の一覧は段ごとの M で切り分けられる（Σ M = 160 = 窓の数）。 -/
def groups959 : List APFree.ChainRecord.Group :=
  APFree.ChainRecord.regroup (List.zip APFree.BellmanPolicy.steps APFree.BellmanPolicy.steps774) APFree.BellmanLower.wins939

set_option maxHeartbeats 4000000 in
/-- **本ファイルの機械検査**（鎖の整合・最大元・段と窓の照合・箱の入れ子・窓分離 (W) を
    まとめて一つの `decide`）。頭の 21523361 は Z₀ = 1 + B(2,16,0) の最大元 (3¹⁶−1)/2 + 1。 -/
theorem chain959 : APFree.ChainRecord.chainChk groups959 21523361 = true := by decide

/-- 切り分けは窓の一覧をちょうど使い切る。 -/
theorem groups_flat959 : groups959.flatMap (fun g => g.2) = APFree.BellmanLower.wins939 := by
  refine APFree.ChainRecord.regroup_flat _ _ ?_
  decide

/-! ## 2. 継いで得られる集合が `APFreeBellmanLower` の `setA939` であること -/

theorem grow_eq_setA959 :
    APFree.ChainRecord.growZ (winZ (2, 16, 0, 1)) groups959
      = {x : ℤ | ∃ n ∈ APFree.BellmanLower.setA939, x = (n : ℤ)} := by
  rw [APFree.ChainRecord.growZ_eq, groups_flat959]
  have hw : winZ (2, 16, 0, 1) ∪ unionWZ APFree.BellmanLower.wins939
      = unionWZ APFree.BellmanLower.winsAll939 := rfl
  rw [hw, APFree.BellmanLower.setA939]
  exact APFree.ChainRecord.unionWZ_eq_coe APFree.BellmanLower.winsAll939 APFree.BellmanLower.winsAll939_p

/-! ## 3. 3-AP-free 性 -/

/-- **窓分離ベルマン 84 段の集合 A は 3-AP を含まない。**
    （Wróblewski 1984 Lemma 1 の Lean 化 `APFreeChainRecordCore.Blk_apfree` ＋ 定理W ＋ 84 段の鎖。） -/
theorem setA939_apfree : IsThreeAPFree {x : ℤ | ∃ n ∈ APFree.BellmanLower.setA939, x = (n : ℤ)} := by
  rw [← grow_eq_setA959]
  exact APFree.ChainRecord.grow_apfree groups959 (winZ (2, 16, 0, 1)) 21523361
    APFree.ChainRecord.head_apfree APFree.ChainRecord.head_box chain959

/-! ## 4. 主定理（`APFreeChainRecord` の七訂版と同じ型） -/

/-- **本ファイルの主定理**：窓分離ベルマン 84 段が定める集合 A は 3-AP-free であり、
    かつその逆数和は **3.0085385 を超える**。
    （公表記録 3.00849〈Wróblewski 1984〉との差は +4.85×10⁻⁵。
      Python の厳密挟み込み 3.008538522178115 との差は 1.2×10⁻⁸。
      **Lean が保証しているのは 3.0085385 であって 3.008538522178115 ではない。**） -/
theorem setA939_apfree_and_lower :
    IsThreeAPFree {x : ℤ | ∃ n ∈ APFree.BellmanLower.setA939, x = (n : ℤ)} ∧
      (30085385 : ℚ) / 10 ^ 7 < ∑ x ∈ APFree.BellmanLower.setA939, (1 : ℚ) / x :=
  ⟨setA939_apfree, APFree.BellmanLower.setA939_lower⟩

/-- 公表記録との比較まで含めた形（`APFreeChainRecord.setA_apfree_and_beats_record` の 84 段版）。 -/
theorem setA939_apfree_and_beats_record :
    IsThreeAPFree {x : ℤ | ∃ n ∈ APFree.BellmanLower.setA939, x = (n : ℤ)} ∧
      (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ APFree.BellmanLower.setA939, (1 : ℚ) / x :=
  ⟨setA939_apfree, APFree.BellmanLower.setA939_beats_record⟩

/-- **存在形**（構成に触れない）：3-AP を含まない正整数の有限集合で、
    逆数和が 3.00849 を超えるものが存在する。`APFreeRecordStatement.erdos169_lower_record` の 84 段版。 -/
theorem erdos169_lower_record_939 :
    ∃ A : Finset ℕ, IsThreeAPFree {x : ℤ | ∃ n ∈ A, x = (n : ℤ)} ∧
      (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ A, (1 : ℚ) / x :=
  ⟨APFree.BellmanLower.setA939, setA939_apfree_and_beats_record⟩

/-- 同じ形で 3.0085385 の側。 -/
theorem erdos169_lower_3_0085385 :
    ∃ A : Finset ℕ, IsThreeAPFree {x : ℤ | ∃ n ∈ A, x = (n : ℤ)} ∧
      (30085385 : ℚ) / 10 ^ 7 < ∑ x ∈ A, (1 : ℚ) / x :=
  ⟨APFree.BellmanLower.setA939, setA939_apfree_and_lower⟩

end APFree.BellmanRecord

-- 公理の点検
#print axioms APFree.BellmanRecord.chain959
#print axioms APFree.BellmanRecord.setA939_apfree
#print axioms APFree.BellmanRecord.setA939_apfree_and_lower
#print axioms APFree.BellmanRecord.setA939_apfree_and_beats_record
#print axioms APFree.BellmanRecord.erdos169_lower_record_939
#print axioms APFree.BellmanRecord.erdos169_lower_3_0085385

/-! ### 公理の確認 -/

#print axioms APFree.BellmanRecord.chain959
#print axioms APFree.BellmanRecord.grow_eq_setA959
#print axioms APFree.BellmanRecord.setA939_apfree
#print axioms APFree.BellmanRecord.setA939_apfree_and_lower
#print axioms APFree.BellmanRecord.setA939_apfree_and_beats_record
#print axioms APFree.BellmanRecord.erdos169_lower_record_939
#print axioms APFree.BellmanRecord.erdos169_lower_3_0085385
