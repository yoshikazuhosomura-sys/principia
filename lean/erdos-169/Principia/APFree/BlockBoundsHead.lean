/-
  結び — 頭 Z₀ の逆数和の**厳密な挟み込み**。
  `APFreeBlockBoundsHeadLower`（下界）と `APFreeBlockBoundsHeadUpper`（上界）を合わせるだけ。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsHeadLower
import Principia.APFree.BlockBoundsHeadUpper

namespace APFree.BlockBounds

/-- **本組の結論**：
    `3.004209955304941 ≤ Σ_{n ∈ Z₀} 1/n ≤ 3.004209955304942`。
    Z₀ = 1 + B(2,16,0)（`Z0F_eq`）、|Z₀| = 65536（`Z0F_card`）。 -/
theorem head_bracket :
    (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n ∧
      ∑ n ∈ Z0F, (1 : ℚ) / n ≤ (3004209955304942 : ℚ) / 10 ^ 15 :=
  ⟨Z0F_lower, Z0F_upper⟩

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.head_bracket
