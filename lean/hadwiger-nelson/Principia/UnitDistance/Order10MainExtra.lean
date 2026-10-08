import Mathlib
import Principia.UnitDistance.Order10CertExtra00
import Principia.UnitDistance.Order10CertExtra01
import Principia.UnitDistance.Order10CertExtra02
import Principia.UnitDistance.Order10CertExtra03
import Principia.UnitDistance.Order10CertExtra04
/-
  おまけ：`H` フィルタは **275 類から 172 類に締められる**。

  `H` フィルタの段（Lean の外）は `L₃[10]` の最小次数 `≥ 3` の 571 類のうち 296 類を棄却し、
  **275 類を「実現しうる」として `n=16` の列挙に回した**。
  この段の機械（起点辺を両向き全部・隣接錨を優先する貪欲の plan）をその 275 類に当てると
  **さらに 103 類が落ちた**（`erdos1189cal.py` の校正 (2)）。
  その 103 類（`R₂`）の非実現を Lean で閉じたのが本ファイルである。

  * `no_realization2`：103 類すべて。辺は距離 1・非辺は制約なし・10 点は相異なる。
  * `no_edges2`：103 類すべて。単射性を使わない、より強い形。

  **これは連鎖の穴ではない**（`n=16` の連鎖は 275 類を回して全滅を出しているので、
  103 類を余分に回しただけで結論は変わらない）。**次の列挙を軽くする材料**であり、
  紙の草稿の「平行四辺形の段」「平行四辺形の段を `H` の 275 類に当て直す」が CPU に入らず
  残していた宿題に、平行四辺形の段を使わずに答えた形になる。
  `H` フィルタの段（Lean の外）が「実現する」と観測した 11 類（#232/274/276/281/285/354/357/359/360/363/371）は
  **一つも落ちていない**（落ちたら証明器の不健全を疑うところである）。

  合わせて `H` フィルタは **571 → 172 類**。`R ∪ R₂` の 399 類が Lean で閉じている。
-/

namespace UnitDistance.Order10

set_option maxRecDepth 100000

/-- `H` フィルタの段（Lean の外）の `H` フィルタが捨てた `L₃[10]` の 296 類の辺集合（添字の昇順）。 -/
def candsH2 : List (List (ℕ × ℕ)) := xs00 ++ xs01 ++ xs02 ++ xs03 ++ xs04

/-- **この段の主定理**：`candsH2` のどの辺集合も平面に単位距離で実現しない。 -/
theorem no_realization2 : ∀ E ∈ candsH2, ∀ p : Fin 10 → ℝ × ℝ, ¬ Realiz E p := by
  simp only [candsH2, List.forall_mem_append]
  exact ⟨⟨⟨⟨noR200, noR201⟩, noR202⟩, noR203⟩, noR204⟩

/-- 辺の条件だけの版（単射性を使わない・より強い）。 -/
theorem no_edges2 : ∀ E ∈ candsH2, ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y := by
  simp only [candsH2, List.forall_mem_append]
  exact ⟨⟨⟨⟨noE200, noE201⟩, noE202⟩, noE203⟩, noE204⟩

theorem candsH2_card : candsH2.length = 103 := by
  simp only [candsH2, List.length_append]
  rfl

end UnitDistance.Order10

#print axioms UnitDistance.Order10.no_realization2
#print axioms UnitDistance.Order10.no_edges2
#print axioms UnitDistance.Order10.candsH2_card
