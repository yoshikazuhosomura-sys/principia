/-
  **主定理**：`A` は 4-AP-free であり、その逆数和は Walker の `H(K(S,55)+1)` を超える。
  `外の生成器` が生成。sorry 0・native_decide 不使用。
-/
import Principia.APFree.FourTermLower

namespace APFree.FourTermRecord

open APFree.WindowSeparation APFree.ChainRecord APFree.Nesting

set_option maxRecDepth 100000

/-- 頭 `A₀`（ℤ の部分集合として）。 -/
def headZ : Set ℤ := {x : ℤ | ∃ n ∈ head4, x = (n : ℤ)}

/-- 頭は `K(S,55) + 1` の部分集合。 -/
theorem headZ_sub : headZ ⊆ KSet 55 S55 := by
  rintro x ⟨n, hn, rfl⟩
  obtain ⟨h1, _, h3⟩ := head4_mem n hn
  refine ⟨n - 1, h3, ?_⟩
  push_cast [h1]
  ring

/-- **頭は 4-AP-free**（Walker の Theorem 1.2）。 -/
theorem headZ_apfree : APFreeK 4 headZ := apFreeK_mono headZ_sub KSet55_apfree

theorem headZ_box : ∀ x ∈ headZ, (0 : ℤ) < x ∧ x ≤ (r0 : ℤ) := by
  rintro x ⟨n, hn, rfl⟩
  obtain ⟨h1, h2, _⟩ := head4_mem n hn
  constructor <;> omega

theorem grow_eq_setA4 :
    growZ4 headZ stages4 = {x : ℤ | ∃ n ∈ setA4, x = (n : ℤ)} := by
  rw [growZ4_eq]
  have hw : stages4.map winOf = wins4 := by unfold wins4; rfl
  rw [hw, unionWZ_eq_coe wins4 wins4_p]
  ext x
  simp only [headZ, setA4, Set.mem_union, Set.mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · exact ⟨n, Or.inl hn, rfl⟩
    · exact ⟨n, Or.inr hn, rfl⟩
  · rintro ⟨n, (hn | hn), rfl⟩
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr ⟨n, hn, rfl⟩

/-- **構成 `A` は 4-AP を含まない**（Walker の Theorem 1.2 ＋ Wróblewski の Lemma 1 ＋
     補題 2（`core_strong`）＋ 38 段の鎖）。 -/
theorem setA4_apfree : APFreeK 4 {x : ℤ | ∃ n ∈ setA4, x = (n : ℤ)} := by
  rw [← grow_eq_setA4]
  exact grow4_apfree stages4 headZ (r0 : ℤ) headZ_apfree headZ_box chain4

/-- **主定理（記録を単一の型に）**：`A` は 4-AP-free であり、かつその逆数和は
    **4.439753369254541 を超える**——Walker 2025 の `H(K(S,55)+1) = 4.43975336925454064…` より大きい。 -/
theorem setA4_apfree_and_beats_walker :
    APFreeK 4 {x : ℤ | ∃ n ∈ setA4, x = (n : ℤ)} ∧
      (4439753369254541 : ℚ) / 10 ^ 15 < ∑ x ∈ setA4, (1 : ℚ) / x :=
  ⟨setA4_apfree, setA4_beats_walker⟩

/-- 下界そのものを添えた形（4.439753474215620）。 -/
theorem setA4_apfree_and_lower :
    APFreeK 4 {x : ℤ | ∃ n ∈ setA4, x = (n : ℤ)} ∧
      (4439753474215620 : ℚ) / 10 ^ 15 < ∑ x ∈ setA4, (1 : ℚ) / x :=
  ⟨setA4_apfree, setA4_lower⟩

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.setA4_apfree_and_beats_walker
#print axioms APFree.FourTermRecord.setA4_apfree_and_lower
#print axioms APFree.FourTermRecord.setA4_apfree
