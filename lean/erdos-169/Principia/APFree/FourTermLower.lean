/-
  集合 `A = A₀ ∪ ⋃ (a_j + B_j)` と、その上の Σ 1/x の下界。Walker の `H(K(S,55)+1)` の上界を超える。
  `外の生成器` が生成。sorry 0・native_decide 不使用。
-/
import Principia.APFree.FourTermTailStagesOneToThree
import Principia.APFree.FourTermTailStagesFourToSix
import Principia.APFree.FourTermTailStagesSevenToSixteen
import Principia.APFree.FourTermTailStagesToTwentyEight
import Principia.APFree.FourTermTailStagesToThirtyEight
import Principia.APFree.FourTermStages

namespace APFree.FourTermRecord

open APFree.BlockBounds APFree.WindowsDisjoint

set_option maxRecDepth 100000

theorem tailG_map : tailG0.map Prod.fst ++ tailG1.map Prod.fst ++ tailG2.map Prod.fst ++ tailG3.map Prod.fst ++ tailG4.map Prod.fst = wins4 := by
  unfold wins4; rfl

theorem wins4_lower : (2822475794322959335245829034795457534791247591303030879242357936670709939872208926854089785344 : ℚ) / 10 ^ 100 ≤ sumWin wins4 := by
  have h : sumWin wins4 = sumWin (tailG0.map Prod.fst) + sumWin (tailG1.map Prod.fst) + sumWin (tailG2.map Prod.fst) + sumWin (tailG3.map Prod.fst) + sumWin (tailG4.map Prod.fst) := by
    rw [← tailG_map, sumWin_append, sumWin_append, sumWin_append, sumWin_append]
  rw [h]
  have he : (2822475794322959335245829034795457534791247591303030879242357936670709939872208926854089785344 : ℚ) / 10 ^ 100 = (2025349202092829718291646178344522456434343454516869592458830569500471744380566187451976196096 : ℚ) / 10 ^ 100 + (566712570977974702498547245589735501722258670413783921596129875608610413043492771901202178048 : ℚ) / 10 ^ 100 + (226933485434956862296603917489669847369452280131312141724488924095633220682834155720006270976 : ℚ) / 10 ^ 100 + (3469481382592216008602529943488395056054404076720217939660329864599283822337523682324250624 : ℚ) / 10 ^ 100 + (11054434605836150429163428041334209138782164345005523248237601395277942978288098580889600 : ℚ) / 10 ^ 100 := by norm_num
  rw [he]
  have h0 := tailG0_lower
  have h1 := tailG1_lower
  have h2 := tailG2_lower
  have h3 := tailG3_lower
  have h4 := tailG4_lower
  exact add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4

/-- **構成そのもの**：頭 `A₀` と 38 段の窓の合併。 -/
def setA4 : Finset ℕ := head4 ∪ unionW wins4

theorem wins4_p : ∀ w ∈ wins4, 1 ≤ w.1 := by decide +kernel

/-- **窓は互いに素**（38 窓、右端は `a + mxv p q`）。 -/
theorem wins4_ord : ordWB wins4 = true := by decide +kernel

theorem wins4_lb : ∀ w ∈ wins4, 4527528777914432254565203631367 ≤ w.2.2.2 := by decide +kernel

theorem head4_disj : Disjoint head4 (unionW wins4) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  have h1 : x ≤ 2263764388957216127282601815683 := (head4_mem x hx).2.1
  have h2 : 4527528777914432254565203631367 ≤ x := unionW_lb wins4 _ wins4_lb x hx2
  clear hx hx2
  omega

theorem sum_setA4 :
    ∑ x ∈ setA4, (1 : ℚ) / x = (∑ x ∈ head4, (1 : ℚ) / x) + sumWin wins4 := by
  rw [setA4, Finset.sum_union head4_disj, sum_set_eq wins4 wins4_p wins4_ord]

/-- **集合 `A` の上の Σ 1/x の下界**（SC = 10^100 の整数で）。 -/
theorem setA4_lower_full : (44397534742156205102381072818669242045024979587395110985773412630780363649899884757212715867228715863 : ℚ) / 10 ^ 100 ≤ ∑ x ∈ setA4, (1 : ℚ) / x := by
  rw [sum_setA4]
  have h1 := head4_lower
  have h2 := wins4_lower
  have h3 : (44397534742156205102381072818669242045024979587395110985773412630780363649899884757212715867228715863 : ℚ) / 10 ^ 100 = (44397531919680410779421737572840207249567444796147519682742533388422426979189944885003789013138930519 : ℚ) / 10 ^ 100 + (2822475794322959335245829034795457534791247591303030879242357936670709939872208926854089785344 : ℚ) / 10 ^ 100 := by norm_num
  rw [h3]
  exact add_le_add h1 h2

/-- **本ファイルの結論**：`A` の逆数和は **4.439753474215620 を超える**。 -/
theorem setA4_lower : (4439753474215620 : ℚ) / 10 ^ 15 < ∑ x ∈ setA4, (1 : ℚ) / x := by
  have h := setA4_lower_full
  have : (4439753474215620 : ℚ) / 10 ^ 15 < (44397534742156205102381072818669242045024979587395110985773412630780363649899884757212715867228715863 : ℚ) / 10 ^ 100 := by norm_num
  linarith

/-- **Walker の集合を超える**：`H(K(S,55)+1) < 4.439753369254541`（Walker 2025 の値の上界、
    Python の厳密な挟み込み `H_hi = 4.43975336925454064…`）に対し、`A` の逆数和は
    4.439753369254541 を超える。 -/
theorem setA4_beats_walker : (4439753369254541 : ℚ) / 10 ^ 15 < ∑ x ∈ setA4, (1 : ℚ) / x := by
  have h := setA4_lower
  have : (4439753369254541 : ℚ) / 10 ^ 15 < (4439753474215620 : ℚ) / 10 ^ 15 := by norm_num
  linarith

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.setA4_lower_full
