import Principia.DistinctCircumradii.Unrealizable.Core
import Principia.DistinctCircumradii.Unrealizable.Orientation1
import Principia.DistinctCircumradii.Unrealizable.Orientation2
import Principia.DistinctCircumradii.Unrealizable.Orientation3
import Principia.DistinctCircumradii.Unrealizable.Orientation4
import Principia.DistinctCircumradii.Unrealizable.Orientation5
import Principia.DistinctCircumradii.Unrealizable.Orientation6
import Principia.DistinctCircumradii.Unrealizable.Orientation7
import Principia.DistinctCircumradii.Unrealizable.Radical2
import Principia.DistinctCircumradii.Unrealizable.Radical3
import Principia.DistinctCircumradii.Unrealizable.Radical4
import Principia.DistinctCircumradii.Unrealizable.Radical5
import Principia.DistinctCircumradii.Unrealizable.Radical6
import Principia.DistinctCircumradii.Unrealizable.Radical7
import Principia.DistinctCircumradii.Unrealizable.Radical8
import Principia.DistinctCircumradii.Unrealizable.Radical10
import Principia.DistinctCircumradii.Unrealizable.Radical11
import Principia.DistinctCircumradii.Unrealizable.Radical12
import Principia.DistinctCircumradii.Unrealizable.Branches10
import Principia.DistinctCircumradii.Unrealizable.Branches11
import Principia.DistinctCircumradii.Unrealizable.Branches12
import Principia.DistinctCircumradii.Unrealizable.Branches13
import Principia.DistinctCircumradii.Census.Tree373

/-!
# `n_4 = 7` — 一本の言明

土台は `Principia.DistinctCircumradii.Basic` で、その上に `Census.Statement` →
`SixPoints` → `SevenPoints` → 22 本の部品を載せてある。どの部品も、土台の宣言を
`import` で引き、自分の受け持つ類だけを残した版である。

* `censusComplete`（35 類の全数性）は `Principia.DistinctCircumradii.Census.Tree373` から。
* 34 類の非実現は `restUnrealizable` でここに集める。
* 下界 `7 ≤ n_4` は `seven_le_sInf_isGood_and_sInf_isGood_le_nine`。
-/

namespace DistinctCircumradii

/-- **34 類の非実現。**　一般の位置の 6 点は `censusRest` のどの覆いも担わない。 -/
theorem restUnrealizable : QU0.RestUnrealizableCarries := by
  intro p hgp w hw hc
  simp only [censusRest, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact QU1.not_carries_k1 p hgp hc
  · exact QU0.not_carries_k2 p hgp hc
  · exact QR6.not_carries_k3 p hgp hc
  · exact QR7.not_carries_k4 p hgp hc
  · exact QR8.not_carries_k5 p hgp hc
  · exact QR4.not_carries_k6 p hgp hc
  · exact QU0.not_carries_k7 p hgp hc
  · exact QU0.not_carries_k8 p hgp hc
  · exact QU0.not_carries_k9 p hgp hc
  · exact QU0.not_carries_k10 p hgp hc
  · exact QU2.not_carries_k11 p hgp hc
  · exact QU0.not_carries_k12 p hgp hc
  · exact QR5.not_carries_k13 p hgp hc
  · exact QR3.not_carries_k14 p hgp hc
  · exact QU0.not_carries_k15 p hgp hc
  · exact QU4.not_carries_k16 p hgp hc
  · exact QU4.not_carries_k17 p hgp hc
  · exact QU0.not_carries_k18 p hgp hc
  · exact QU0.not_carries_k19 p hgp hc
  · exact QU6.not_carries_k20 p hgp hc
  · exact QU7.not_carries_k21 p hgp hc
  · exact QR10.not_carries_k22 p hgp hc
  · exact QU5.not_carries_k23 p hgp hc
  · exact QB13.not_carries_k24 p hgp hc
  · exact QU3.not_carries_k25 p hgp hc
  · exact QU3.not_carries_k26 p hgp hc
  · exact QB12.not_carries_k27 p hgp hc
  · exact QR2.not_carries_k28 p hgp hc
  · exact QR11.not_carries_k29 p hgp hc
  · exact QU0.not_carries_k30 p hgp hc
  · exact QB10.not_carries_k31 p hgp hc
  · exact QR12.not_carries_k32 p hgp hc
  · exact QU2.not_carries_k33 p hgp hc
  · exact QB11.not_carries_k34 p hgp hc

/-- **八面体の仮定。**　一般の位置の悪い 6 点は八面体型である。 -/
theorem octahedralHypothesis :
    ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → OctahedralSix q :=
  QU0.octahedral_hypothesis_carries
    (fun {q} hgp hw => octahedralSix_of_supports_K0 hgp hw)
    censusComplete restUnrealizable

/-- `n_4 ≤ 7`。 -/
theorem isGoodSeven : IsGood 7 :=
  isGood_seven_of_octahedral_six octahedralHypothesis

/-- **`n_4 = 7`。**　一般の位置の 7 点は必ず、四つの三角形の外接半径が
相異なる 4 点を含み、6 点ではそうならない配置がある。 -/
theorem sInf_isGood_eq_seven : sInf {N : ℕ | IsGood N} = 7 :=
  le_antisymm
    (sInf_isGood_le_seven_of_octahedral_six octahedralHypothesis)
    seven_le_sInf_isGood_and_sInf_isGood_le_nine.1

end DistinctCircumradii

#print axioms DistinctCircumradii.restUnrealizable
#print axioms DistinctCircumradii.octahedralHypothesis
#print axioms DistinctCircumradii.isGoodSeven
#print axioms DistinctCircumradii.sInf_isGood_eq_seven
