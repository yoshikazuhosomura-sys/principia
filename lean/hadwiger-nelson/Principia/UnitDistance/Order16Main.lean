import Mathlib
import Principia.UnitDistance.Order16Cert00
import Principia.UnitDistance.Order16Cert01
import Principia.UnitDistance.Order16Cert02
import Principia.UnitDistance.Order16Cert03
import Principia.UnitDistance.Order16Cert04
import Principia.UnitDistance.Order16Cert05
import Principia.UnitDistance.Order16Cert06
import Principia.UnitDistance.Order16Cert07
import Principia.UnitDistance.Order16Cert08
import Principia.UnitDistance.Order16Cert09
import Principia.UnitDistance.Order16Cert10
import Principia.UnitDistance.Order16Cert11
import Principia.UnitDistance.Order16Cert12
import Principia.UnitDistance.Order16Cert13
import Principia.UnitDistance.Order16Cert14
import Principia.UnitDistance.Order16Cert15
import Principia.UnitDistance.Order16Parallelogram
/-
  総括：`n=16`・`α ≤ 4` の候補（Lean の外の列挙が列挙した 2,100 類）は
  いずれも平面に単位距離で実現しない。

  * `no_realization`：2,100 類すべて。**辺は距離 1・非辺は制約なし・16 点は相異なる**。
  * `no_edges`：2,093 類。単射性すら使わない、より強い形
      （残る 7 類は平行四辺形の段が点の相異を使うので `Realiz` の側だけ。`Erdos1185p`）。

  **Lean の外に残すもの**：この 2,100 が候補の全部であること（列挙の完全性・
  `H` の実現性フィルタの健全性・同型判定。Lean の外の列挙の Python）。
  Lean が言うのは「`cands16` に並べた辺集合は、どれも平面に単位距離で実現しない」
  という**存在の否定**だけである。したがって **`f(4) ≤ 15` そのものは Lean の中では閉じていない**。
-/

namespace UnitDistance.Order16

set_option maxRecDepth 100000

/-- 素の三辺測量で閉じた 2,093 類の辺集合（同型類ごとに束ねた順）。 -/
def cands16e : List (List (ℕ × ℕ)) :=
  cs00 ++ cs01 ++ cs02 ++ cs03 ++ cs04 ++ cs05 ++ cs06 ++ cs07 ++ cs08 ++ cs09 ++ cs10 ++ cs11 ++ cs12 ++ cs13 ++ cs14 ++ cs15

/-- Lean の外の列挙の候補 2,100 類の辺集合。 -/
def cands16 : List (List (ℕ × ℕ)) := cands16e ++ csp

/-- **この段の主定理**：`cands16` のどの辺集合も平面に単位距離で実現しない。 -/
theorem no_realization : ∀ E ∈ cands16, ∀ p : Fin 16 → ℝ × ℝ, ¬ Realiz E p := by
  simp only [cands16, cands16e, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨noR00, noR01⟩, noR02⟩, noR03⟩, noR04⟩, noR05⟩, noR06⟩, noR07⟩, noR08⟩, noR09⟩, noR10⟩, noR11⟩, noR12⟩, noR13⟩, noR14⟩, noR15⟩, noRp⟩

/-- 辺の条件だけの版（単射性を使わない・より強い）。平行四辺形の段を要した 7 類を除く。 -/
theorem no_edges : ∀ E ∈ cands16e, ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y := by
  simp only [cands16e, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨noE00, noE01⟩, noE02⟩, noE03⟩, noE04⟩, noE05⟩, noE06⟩, noE07⟩, noE08⟩, noE09⟩, noE10⟩, noE11⟩, noE12⟩, noE13⟩, noE14⟩, noE15⟩

theorem cands16e_card : cands16e.length = 2093 := by
  simp only [cands16e, List.length_append]
  rfl

theorem cands16_card : cands16.length = 2100 := by
  simp only [cands16, List.length_append, cands16e_card]
  rfl

end UnitDistance.Order16

#print axioms UnitDistance.Order16.cands16_card
#print axioms UnitDistance.Order16.cands16e_card
#print axioms UnitDistance.Order16.no_realization
#print axioms UnitDistance.Order16.no_edges
