/-
  結び —
  エルデシュ問題 #169。**窓分離ベルマン政策 84 段の集合 A の逆数和の下界を Lean で出す。**

  【何を新しく通したか】
    の `APFreeBellmanPolicy` は、この 84 段について**段依存の前提二つ**
    （窓分離 (W)・t が Blk の最大元）を通した。**逆数和そのものは Python の
    整数演算（SCALE = 10^120 の床・天井）に依ったままだった。**
    本ファイルはそこを埋める：**集合 A = Z₀ ∪ ⋃(a_i + B_i) の上の Σ 1/x が
    3.0085385 を超える**ことを、kernel 評価だけで示す。

  【構成】頭 Z₀ = 1 + B(2,16,0)（APFreeBlockBounds の `Z0_eq_block`。z = 21523361）に
    84 段（M=1 が 37 段・M=2 が 18 段・M=3 が 29 段）の窓 160 個を継ぐ。
    窓の深さは混合（130 個が深さ 2、残り 30 個が深さ 3〜6。葉は合計 112,150）。

  【何を通していないか（ここを混ぜない）】
    ・本ファイルは **3-AP-free 性を主張しない。**APFreeBellmanPolicy が通したのは
      (W) と maxelt の二つで、`APFreeChainRecord` のような
      「IsThreeAPFree ∧ 逆数和」の**単一の主定理**は 84 段については**まだ無い**。
    ・したがって帳簿には **「84 段の逆数和が Lean を通った」**とだけ書ける。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BellmanLowerLead
import Principia.APFree.BellmanLowerMid
import Principia.APFree.BellmanLowerRest

namespace APFree.BellmanLower

open APFree.BlockBounds

set_option maxRecDepth 4000000

/-- 深さの札を外した窓の一覧（160 個）。 -/
def wins939 : List (ℕ × ℕ × ℕ × ℕ) :=
  wins939a.map Prod.fst ++ (wins939b.map Prod.fst ++ wins939c.map Prod.fst)

/-- **構成そのもの**：頭 Z₀ と 84 段 160 個の窓を一本の一覧にする。 -/
def winsAll939 : List (ℕ × ℕ × ℕ × ℕ) := (2, 16, 0, 1) :: wins939

/-- 構成が覆う集合 A（ベルマン 84 段版）。 -/
def setA939 : Finset ℕ := APFree.WindowsDisjoint.unionW winsAll939

theorem winsAll939_p : ∀ w ∈ winsAll939, 1 ≤ w.1 := by decide

set_option maxHeartbeats 4000000 in
/-- **窓は互いに素である**（161 個・kernel 評価）。 -/
theorem winsAll939_ord : APFree.WindowsDisjoint.ordWB winsAll939 = true := by decide

/-- 集合 A の上の逆数和は、頭と窓の逆数和の総和に等しい。 -/
theorem sum_setA939 :
    ∑ x ∈ setA939, (1 : ℚ) / x
      = (∑ n ∈ Z0F, (1 : ℚ) / n)
        + sumWin (wins939a.map Prod.fst)
        + sumWin (wins939b.map Prod.fst)
        + sumWin (wins939c.map Prod.fst) := by
  have h := APFree.WindowsDisjoint.sum_set_eq winsAll939 winsAll939_p winsAll939_ord
  rw [setA939, h, winsAll939, wins939, sumWin, sumWin_append, sumWin_append,
    APFree.WindowsDisjoint.Z0F_eq_winF, APFree.WindowsDisjoint.sum_winF]
  ring

/-- **本ファイルの結論**：窓分離ベルマン政策 84 段が定める 3-AP-free 集合 A の
    逆数和は **3.0085385 を超える**。
    （Python の厳密挟み込み 3.008538522178115 との差は 1.2×10⁻⁸。
      公表記録 3.00849〈Wróblewski 1984〉との差は +4.85×10⁻⁵。） -/
theorem setA939_lower : (30085385 : ℚ) / 10 ^ 7 < ∑ x ∈ setA939, (1 : ℚ) / x := by
  rw [sum_setA939]
  have h0 : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := Z0F_lower
  have ha := wins939a_lower
  have hb := wins939b_lower
  have hc := wins939c_lower
  have hnum : (30085385 : ℚ) / 10 ^ 7
      < (3004209955304941 : ℚ) / 10 ^ 15
        + (37924666165427113428187689763969464349141715971032471707513576607346637567564783658796733178297800 : ℚ) / 10 ^ 100
        + (5193896371181394461429645092806851781618421393167778746084975161125641212418883378886243355841776 : ℚ) / 10 ^ 100
        + (166988481064848888388522265228347187355009527992735570616212480725604869682563415901655825051520 : ℚ) / 10 ^ 100 := by norm_num
  linarith

/-- 公表記録 3.00849 との比較（同じ集合について）。 -/
theorem setA939_beats_record : (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ setA939, (1 : ℚ) / x := by
  have h := setA939_lower
  have : (300849 : ℚ) / 10 ^ 5 < (30085385 : ℚ) / 10 ^ 7 := by norm_num
  linarith

/-- 存在形（構成に触れない）。 -/
theorem erdos169_bellman_lower :
    ∃ A : Finset ℕ, (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ A, (1 : ℚ) / x :=
  ⟨setA939, setA939_beats_record⟩

end APFree.BellmanLower

-- 公理の点検（本ファイルの主要な定理）
#print axioms APFree.BellmanLower.winsAll939_ord
#print axioms APFree.BellmanLower.sum_setA939
#print axioms APFree.BellmanLower.setA939_lower
#print axioms APFree.BellmanLower.setA939_beats_record
#print axioms APFree.BellmanLower.erdos169_bellman_lower

/-! ### 公理の確認 -/

#print axioms APFree.BellmanLower.winsAll939_p
#print axioms APFree.BellmanLower.winsAll939_ord
#print axioms APFree.BellmanLower.sum_setA939
#print axioms APFree.BellmanLower.setA939_lower
#print axioms APFree.BellmanLower.setA939_beats_record
#print axioms APFree.BellmanLower.erdos169_bellman_lower
