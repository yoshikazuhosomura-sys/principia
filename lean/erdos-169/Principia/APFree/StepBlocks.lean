/-
  Principia.APFree.StepBlocks — ・C

  （APFreeChainRecord）で `APFree.ChainRecord.Blk_apfree` / `APFree.ChainRecord.winZ_apfree` が立ち、
  「ブロック B(p,q,r) は 3-AP-free である」が初めて Lean の定理になった。
  ところが `APFree.StepsSeparated.step_M1_apfree` / `step_M2_apfree` / `APFree.WindowSeparationM3.step_M3_apfree` は
  いまも `(hfree : ∀ i, IsThreeAPFree (A i))` を**仮定として受け取ったまま**である。

  本ファイルは、その仮定を**外から埋めた系**を新しい名前で置く。
  A 0 は前段までの集合（頭）なので `IsThreeAPFree` は仮定として残す（帰納法の仮定にあたる）。
  A 1, A 2, A 3 はブロック窓なので `winZ_apfree` で埋まる。
  ⟹ **本ファイルの三定理には、もう `hfree` が無い。**

  既存ファイルは一切編集していない（読んで使うだけ）。
-/
import Mathlib.Tactic
import Principia.APFree.StepsSeparated
import Principia.APFree.WindowSeparationM3
import Principia.APFree.ChainRecordCore

namespace APFree.StepBlocks

open APFree.WindowSeparation APFree.ChainRecord

/-- 頭 `H` と、窓の一覧 `ws` からブロック窓の族を作る（`A 0 = H`）。 -/
def headBlk {n : ℕ} (H : Set ℤ) (w : Fin n → ℕ × ℕ × ℕ × ℕ) : Fin (n + 1) → Set ℤ :=
  fun i => match i with
    | ⟨0, _⟩ => H
    | ⟨k + 1, hk⟩ => winZ (w ⟨k, Nat.succ_lt_succ_iff.mp hk⟩)

/-- `headBlk` の各成分は 3-AP-free（頭は仮定、ブロック窓は `winZ_apfree`）。 -/
theorem headBlk_apfree {n : ℕ} (H : Set ℤ) (hH : IsThreeAPFree H)
    (w : Fin n → ℕ × ℕ × ℕ × ℕ) (hp : ∀ j, 1 ≤ (w j).1) :
    ∀ i, IsThreeAPFree (headBlk H w i) := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact hH
  | succ m => exact winZ_apfree _ (hp _)

/-- **M = 1 の段（`hfree` を埋めた形）。** -/
theorem step_M1_apfree_blk (z t a : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (h1 : 2 * z < a) (h2 : z + t < a)
    (H : Set ℤ) (hH : IsThreeAPFree H) (w : Fin 1 → ℕ × ℕ × ℕ × ℕ) (hp : ∀ j, 1 ≤ (w j).1)
    (hbox : ∀ i, ∀ x ∈ headBlk H w i,
      (APFree.StepsSeparated.W1 z t a).l i ≤ x ∧ x ≤ (APFree.StepsSeparated.W1 z t a).r i) :
    IsThreeAPFree (⋃ i, headBlk H w i) :=
  APFree.StepsSeparated.step_M1_apfree z t a hz ht h1 h2 _ hbox (headBlk_apfree H hH w hp)

/-- **M = 2 の段（`hfree` を埋めた形）。** -/
theorem step_M2_apfree_blk (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (h3 : 3 * t < z)
    (H : Set ℤ) (hH : IsThreeAPFree H) (w : Fin 2 → ℕ × ℕ × ℕ × ℕ) (hp : ∀ j, 1 ≤ (w j).1)
    (hbox : ∀ i, ∀ x ∈ headBlk H w i,
      (APFree.StepsSeparated.W2 z t).l i ≤ x ∧ x ≤ (APFree.StepsSeparated.W2 z t).r i) :
    IsThreeAPFree (⋃ i, headBlk H w i) :=
  APFree.StepsSeparated.step_M2_apfree z t hz ht h3 _ hbox (headBlk_apfree H hH w hp)

/-- **M = 3 の段（`hfree` を埋めた形）。**Wróblewski の三窓の配置。 -/
theorem step_M3_apfree_blk (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (H : Set ℤ) (hH : IsThreeAPFree H) (w : Fin 3 → ℕ × ℕ × ℕ × ℕ) (hp : ∀ j, 1 ≤ (w j).1)
    (hbox : ∀ i, ∀ x ∈ headBlk H w i,
      (APFree.WindowSeparationM3.W3 z t).l i ≤ x ∧ x ≤ (APFree.WindowSeparationM3.W3 z t).r i) :
    IsThreeAPFree (⋃ i, headBlk H w i) :=
  APFree.WindowSeparationM3.step_M3_apfree z t hz ht _ hbox (headBlk_apfree H hH w hp)

end APFree.StepBlocks

/-! ### 公理の確認 -/

#print axioms APFree.StepBlocks.step_M1_apfree_blk
#print axioms APFree.StepBlocks.step_M2_apfree_blk
#print axioms APFree.StepBlocks.step_M3_apfree_blk
#print axioms APFree.StepBlocks.headBlk_apfree
