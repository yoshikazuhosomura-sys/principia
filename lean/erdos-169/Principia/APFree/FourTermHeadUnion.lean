/-
  頭 `A₀ = (K(S,55)+1) ∩ [1, r₀]` を塊の合併として置き、並び・桁・箱・下界を閉じる。
  `外の生成器` が生成。sorry 0・native_decide 不使用。
-/
import Principia.APFree.FourTermHeadLead
import Principia.APFree.FourTermHeadMid
import Principia.APFree.FourTermHeadRest

namespace APFree.FourTermRecord

set_option maxRecDepth 100000

/-- 切り所 `r₀`。`r₀ − 1 = max{k ∈ K(S,55) : k ≤ 10^30.5}`。 -/
def r0 : ℕ := 2263764388957216127282601815683

/-- 頭の塊の一覧（685 個。左端の昇順）。 -/
def pieces4 : List (ℕ × ℕ × ℕ) := piecesK1 ++ piecesK2 ++ piecesK3

theorem pieces4_length : pieces4.length = 685 := by decide

/-- **塊は互いに素**（隣接の右端 < 次の左端）。 -/
theorem pieces4_ord : ordK 55 47 pieces4 = true := by decide +kernel

/-- **全塊の接頭辞の桁は S**。 -/
theorem pieces4_dig : pieces4.all (fun w => digB 55 S55 40 w.1) = true := by decide +kernel

/-- **全塊は `[1, r₀]` に収まる**。 -/
theorem pieces4_ub : pieces4.all (fun w => decide (hiK 55 47 w ≤ r0)) = true := by decide +kernel

theorem S55_s1 : ∑ e ∈ S55, e = 433 := by decide
theorem S55_s2 : ∑ e ∈ S55, e ^ 2 = 13899 := by decide
theorem S55_s3 : ∑ e ∈ S55, e ^ 3 = 518857 := by decide

/-- 頭 `A₀`（Finset）。 -/
def head4 : Finset ℕ := unionK 55 S55 pieces4

theorem head4_num : 44397531919680410779421737572840207249567444796147519682742533388422426979189944885003789013138930519 ≤ totK 55 (10 ^ 100) 21 433 13899 518857 S55 pieces4 := by
  have h : totK 55 (10 ^ 100) 21 433 13899 518857 S55 pieces4 = totK 55 (10 ^ 100) 21 433 13899 518857 S55 piecesK1 + totK 55 (10 ^ 100) 21 433 13899 518857 S55 piecesK2 + totK 55 (10 ^ 100) 21 433 13899 518857 S55 piecesK3 := by
    simp only [pieces4, totK_append]
  rw [h]
  have h0 := piecesK1_num
  have h1 := piecesK2_num
  have h2 := piecesK3_num
  omega

/-- **頭の逆数和の下界**：4.4397531919680（Python の挟み込み 4.4397531920675 との差 -9.95e-11）。 -/
theorem head4_lower : (44397531919680410779421737572840207249567444796147519682742533388422426979189944885003789013138930519 : ℚ) / 10 ^ 100 ≤ ∑ x ∈ head4, (1 : ℚ) / x := by
  have h := totK_le 55 S55 S55_lt 47 S55_le 21 433 13899 518857 S55_card S55_s1 S55_s2 S55_s3
    (10 ^ 100) (by norm_num) pieces4 pieces4_ord
  refine le_trans ?_ h
  have hc : ((10 ^ 100 : ℕ) : ℚ) = 10 ^ 100 := by norm_num
  rw [hc]
  gcongr
  exact_mod_cast head4_num

theorem head4_mem : ∀ x ∈ head4, 1 ≤ x ∧ x ≤ r0 ∧ DigIn 55 S55 (x - 1) := by
  intro x hx
  have h1 := unionK_digIn 55 S55 (by norm_num) S55_lt S55_zero 40 pieces4 pieces4_dig x hx
  have h2 := unionK_ub 55 S55 47 S55_le r0 pieces4 pieces4_ub x hx
  exact ⟨h1.1, h2, h1.2⟩

/- 以後 `head4` は展開しない（`x ∈ head4` の defeq 検査で elaborator が集合を評価しに行き、
   再帰の深さを使い切る——の実測）。kernel の評価には影響しない。 -/
attribute [irreducible] head4

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.head4_lower
