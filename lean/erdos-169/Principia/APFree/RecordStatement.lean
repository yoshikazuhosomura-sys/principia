/-

  エルデシュ問題 #169。**一本化した主定理を、構成に触れずに読める形にする。**

  【なぜ要るか】
    APFreeChainRecord の `setA_apfree_and_beats_record` は正しいが、読むのに
    `APFree.WindowsDisjoint.setA`（＝ `unionW winsAll`）という**内部の対象**が要る。
    エルデシュ #169 が訊いているのは
      「3-AP を含まない正整数の有限集合で、逆数和はいくつまで行けるか」
    である。本ファイルはそれを**存在言明**に畳み、
    構成・窓・鎖のどれにも触れずに読める一行にする。

  【本ファイルで踏んだ穴（H2-244）】
    最初は `setA_pos` / `setA_no_3ap` を **`APFree.WindowsDisjoint.setA` を名指ししたまま tactic で**書いた。
    どれも `whnf` で 200000 heartbeats を超え、maxHeartbeats を 5 倍にしても
    **3 分で終わらなかった**。原因は、`⟨a, ha, rfl⟩` の期待型を単一化するときに
    elaborator が `setA = unionW winsAll` を delta で開き、**172 窓の Finset を実際に評価**すること。
    同じ証明を「集合を変数 `A` にした一般補題」として書き、あとから項として当てると **4.4 秒**で通る。
    ⟹ **具体的な巨大オブジェクトは、証明の中に置かず、証明の外から当てる。**
    （壁21 の同型：紙では同じ一行が、機械では 40 倍以上の差になる。）

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.ChainRecord

namespace APFree.RecordStatement

open APFree.WindowSeparation APFree.BlockBounds

set_option maxRecDepth 4000000

/-! ## 1. 一般補題（**集合を変数に置く**。ここが速さの鍵） -/

/-- ℤ の `IsThreeAPFree` から ℕ の言葉へ。 -/
theorem apfree_nat (A : Finset ℕ) (h : IsThreeAPFree {x : ℤ | ∃ n ∈ A, x = (n : ℤ)}) :
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = 2 * b → a = b := by
  intro a ha b hb c hc habc
  have h1 := h (a : ℤ) ⟨a, ha, rfl⟩ (b : ℤ) ⟨b, hb, rfl⟩ (c : ℤ) ⟨c, hc, rfl⟩
    (by exact_mod_cast habc)
  exact_mod_cast h1

/-- 窓の offset がすべて 1 以上なら、覆う集合の元は正。 -/
theorem unionW_pos (ws : List (ℕ × ℕ × ℕ × ℕ)) (h : ∀ w ∈ ws, 1 ≤ w.2.2.2) :
    ∀ n ∈ APFree.WindowsDisjoint.unionW ws, 0 < n := by
  intro n hn
  have h1 := APFree.WindowsDisjoint.unionW_lb ws 1 h n hn
  omega

/-- 三項等差数列が自明だけなら、三つとも等しい。 -/
theorem no_3ap_triv (A : Finset ℕ)
    (h : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = 2 * b → a = b) :
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = 2 * b → a = b ∧ b = c := by
  intro a ha b hb c hc habc
  have h1 := h a ha b hb c hc habc
  exact ⟨h1, by omega⟩

/-! ## 2. 実際の構成に当てる -/

theorem winsAll_offsets : ∀ w ∈ APFree.WindowsDisjoint.winsAll, 1 ≤ w.2.2.2 := by decide

theorem setA_pos : ∀ n ∈ APFree.WindowsDisjoint.setA, 0 < n :=
  unionW_pos APFree.WindowsDisjoint.winsAll winsAll_offsets

/-- **setA は 3-AP を含まない**（ℤ を経由しない、ℕ の言葉での形）。 -/
theorem setA_no_3ap : ∀ a ∈ APFree.WindowsDisjoint.setA, ∀ b ∈ APFree.WindowsDisjoint.setA, ∀ c ∈ APFree.WindowsDisjoint.setA,
    a + c = 2 * b → a = b :=
  apfree_nat APFree.WindowsDisjoint.setA APFree.ChainRecord.setA_apfree

theorem setA_no_3ap' : ∀ a ∈ APFree.WindowsDisjoint.setA, ∀ b ∈ APFree.WindowsDisjoint.setA, ∀ c ∈ APFree.WindowsDisjoint.setA,
    a + c = 2 * b → a = b ∧ b = c :=
  no_3ap_triv APFree.WindowsDisjoint.setA setA_no_3ap

/-! ## 3. エルデシュ #169 の下界（構成に触れない形） -/

/-- **エルデシュ問題 #169 の下界（記録 3.00849 超え）**。
    「3-AP を含まない正整数の有限集合で、逆数和が 3.00849 を超えるものが存在する」。
    ★ **検証待ちの候補である**（壁19）。Lean が言っているのは
    「この構成が 3-AP-free であること」と「逆数和の下界」であって、査読ではない。 -/
theorem erdos169_lower_record :
    ∃ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) ∧
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = 2 * b → a = b) ∧
      (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ A, (1 : ℚ) / x :=
  ⟨APFree.WindowsDisjoint.setA, setA_pos, setA_no_3ap, APFree.WindowsDisjoint.setA_beats_record⟩

/-- 同じ言明の、本ファイルで到達した精度の版。 -/
theorem erdos169_lower_sharp :
    ∃ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) ∧
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = 2 * b → a = b) ∧
      (30085383814002 : ℚ) / 10 ^ 13 < ∑ x ∈ A, (1 : ℚ) / x :=
  ⟨APFree.WindowsDisjoint.setA, setA_pos, setA_no_3ap, APFree.WindowsDisjoint.setA_lower⟩

end APFree.RecordStatement

/-! ### 公理の確認 -/

#print axioms APFree.RecordStatement.setA_no_3ap
#print axioms APFree.RecordStatement.erdos169_lower_record
#print axioms APFree.RecordStatement.erdos169_lower_sharp
#print axioms APFree.RecordStatement.setA_pos
