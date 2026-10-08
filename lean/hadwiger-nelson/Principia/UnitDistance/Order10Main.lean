import Mathlib
import Principia.UnitDistance.Order10Cert00
import Principia.UnitDistance.Order10Cert01
import Principia.UnitDistance.Order10Cert02
import Principia.UnitDistance.Order10Cert03
import Principia.UnitDistance.Order10Cert04
import Principia.UnitDistance.Order10Cert05
import Principia.UnitDistance.Order10Cert06
import Principia.UnitDistance.Order10Cert07
import Principia.UnitDistance.Order10Cert08
import Principia.UnitDistance.Order10Cert09
/-
  総括：`n=16`・`α ≤ 4` の連鎖（Lean の外の列挙）が
  「`H` が平面に実現しない」として捨てた `L₃[10]` の **296 類**（`R`）は、
  いずれも平面に単位距離で実現しない。

  * `no_realization`：296 類すべて。**辺は距離 1・非辺は制約なし・10 点は相異なる**。
  * `no_edges`：296 類すべて。**単射性すら使わない、より強い形**
      （この段の `n=16` では平行四辺形の段のため 7 類でこれが崩れたが、
        この段は 296 類すべてが素の三辺測量＋箱の二分だけで閉じた）。

  **これで `H` フィルタの段は Lean の証明書に乗った**：`H` は `G` の誘導部分グラフなので、
  `H` が実現しないならその `H` を持つ `G` も実現しない。`H` フィルタの段（Lean の外）が 571 類から 275 類に
  絞った根拠のうち、**「捨てた 296 類は実現しない」という幾何の主張が Lean の中にある**。

  **Lean の外に残るもの**（この段の対象外）：
  * `L₃[10]` が `α ≤ 3` の 10 点グラフの同型類 666 個の**全部**であること（列挙の完全性）
  * `H` の最小次数 `≥ 3`（`δ(G) ≥ 5` と `K_{2,3}`-free から。組合せの議論）
  * 同型判定（`L₃[10]` の 666 が互いに非同型であること）
  * `A`-`H` 二部グラフの組み上げ（`Order16` の段 §6.1）
-/

namespace UnitDistance.Order10

set_option maxRecDepth 100000

/-- `H` フィルタの段（Lean の外）の `H` フィルタが捨てた `L₃[10]` の 296 類の辺集合（添字の昇順）。 -/
def candsH : List (List (ℕ × ℕ)) := cs00 ++ cs01 ++ cs02 ++ cs03 ++ cs04 ++ cs05 ++ cs06 ++ cs07 ++ cs08 ++ cs09

/-- **この段の主定理**：`candsH` のどの辺集合も平面に単位距離で実現しない。 -/
theorem no_realization : ∀ E ∈ candsH, ∀ p : Fin 10 → ℝ × ℝ, ¬ Realiz E p := by
  simp only [candsH, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨noR00, noR01⟩, noR02⟩, noR03⟩, noR04⟩, noR05⟩, noR06⟩, noR07⟩, noR08⟩, noR09⟩

/-- 辺の条件だけの版（単射性を使わない・より強い）。 -/
theorem no_edges : ∀ E ∈ candsH, ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y := by
  simp only [candsH, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨noE00, noE01⟩, noE02⟩, noE03⟩, noE04⟩, noE05⟩, noE06⟩, noE07⟩, noE08⟩, noE09⟩

theorem candsH_card : candsH.length = 296 := by
  simp only [candsH, List.length_append]
  rfl

end UnitDistance.Order10

#print axioms UnitDistance.Order10.no_realization
#print axioms UnitDistance.Order10.no_edges
#print axioms UnitDistance.Order10.candsH_card
