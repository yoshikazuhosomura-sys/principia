/-
  鎖 —
  エルデシュ問題 #169、`k = 4`。**倍加税だけで継ぐ鎖の機械検査（補題 2 の核 `core_strong`）。**

  【一段】前段までの集合 `S ⊆ [1, cur]` が 4-AP-free、窓 `a + B(p,q,r)`（3-AP-free、
    `[a, a+t]` に収まる。`t` は最大元の証明書 `APFreeStepsMaxElement.stepOK` で）、倍加税 `a > 2·cur`
    ⟹ `S ∪ 窓` は 4-AP-free（`APFreeNesting.core_strong`、`k = 4`）で `[1, a+t]` に収まる。
    窓の長さへの条件はない（補題 2）。
  【鎖】`chainChk4` は段ごとに `stepOK`・`0 < cur`・`2·cur < a` を見て `a + t` を次に渡す。
    `grow4_apfree` はその Bool 検査から合併の 4-AP-free 性を出す（`APFreeChainRecord.grow_apfree` の型。
    `APFreeNesting.lemma2_four` の ℕ 添字の族を有限リストに畳んだもの）。
  sorry 0・native_decide 不使用。
-/
import Principia.APFree.Nesting
import Principia.APFree.ChainRecord

namespace APFree.FourTermRecord

open APFree.WindowSeparation APFree.StepsMaxElement APFree.ChainRecord APFree.Nesting

/-- 段：ブロックの証明書 `(p, q, r, t, 桁)` と offset `a`。 -/
abbrev Stage := (ℕ × ℕ × ℕ × ℕ × List ℕ) × ℕ

/-- 段の窓 `(p, q, r, a)`。 -/
def winOf (s : Stage) : ℕ × ℕ × ℕ × ℕ := (s.1.1, s.1.2.1, s.1.2.2.1, s.2)

/-- 一段の検査：`p ≥ 2`、最大元の証明書、`0 < cur`、倍加税 `2·cur < a`。 -/
def stageChk (s : Stage) (cur : ℤ) : Bool :=
  decide (2 ≤ s.1.1) && APFree.StepsMaxElement.stepOK s.1 && decide ((0 : ℤ) < cur) &&
    decide (2 * cur < (s.2 : ℤ))

/-- 鎖の検査。次の `cur` は `a + t`。 -/
def chainChk4 : List Stage → ℤ → Bool
  | [], _ => true
  | s :: ss, cur => stageChk s cur && chainChk4 ss ((s.2 : ℤ) + (s.1.2.2.2.1 : ℤ))

/-- 段を継いで得られる集合。 -/
def growZ4 (S : Set ℤ) : List Stage → Set ℤ
  | [] => S
  | s :: ss => growZ4 (S ∪ winZ (winOf s)) ss

theorem growZ4_eq : ∀ (ss : List Stage) (S : Set ℤ),
    growZ4 S ss = S ∪ unionWZ (ss.map winOf) := by
  intro ss
  induction ss with
  | nil => intro S; simp [growZ4, unionWZ]
  | cons s ss ih =>
      intro S
      simp [growZ4, ih, unionWZ, Set.union_assoc]

/-- **鎖の定理**：検査を通る鎖を継いで得られる集合は 4-AP-free。 -/
theorem grow4_apfree : ∀ (ss : List Stage) (S : Set ℤ) (cur : ℤ),
    APFreeK 4 S → (∀ x ∈ S, (0 : ℤ) < x ∧ x ≤ cur) → chainChk4 ss cur = true →
    APFreeK 4 (growZ4 S ss) := by
  intro ss
  induction ss with
  | nil => intro S cur hS _ _; exact hS
  | cons s ss ih =>
      intro S cur hS hbox hchk
      obtain ⟨⟨p, q, r, tb, ds⟩, a⟩ := s
      simp only [chainChk4, stageChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨hp2, hsok⟩, hcur⟩, htax⟩, hrest⟩ := hchk
      have hgreat : IsGreatest (Blk p q r) tb := APFree.StepsMaxElement.maxelt_of_stepOK (p, q, r, tb, ds) hsok
      have hwbox : ∀ x ∈ winZ (winOf ((p, q, r, tb, ds), a)),
          ((a : ℕ) : ℤ) ≤ x ∧ x ≤ ((a : ℕ) : ℤ) + (tb : ℤ) := by
        intro x hx
        exact winZ_box (winOf ((p, q, r, tb, ds), a)) tb hgreat x hx
      have hwfree : APFreeK 3 (winZ (winOf ((p, q, r, tb, ds), a))) :=
        (apFreeK_three_iff _).mpr (winZ_apfree _ (by simp [winOf]; omega))
      have hnew : APFreeK 4 (S ∪ winZ (winOf ((p, q, r, tb, ds), a))) :=
        core_strong (le_refl 4) hbox (fun x hx => (hwbox x hx).1) hS hwfree htax
      have hnewbox : ∀ x ∈ S ∪ winZ (winOf ((p, q, r, tb, ds), a)),
          (0 : ℤ) < x ∧ x ≤ (a : ℤ) + (tb : ℤ) := by
        rintro x (hx | hx)
        · have := hbox x hx
          have h0 : (0 : ℤ) ≤ (tb : ℤ) := Int.natCast_nonneg _
          constructor <;> omega
        · have := hwbox x hx
          constructor <;> omega
      exact ih _ _ hnew hnewbox hrest

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.grow4_apfree
#print axioms APFree.FourTermRecord.growZ4_eq
