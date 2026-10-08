import Mathlib
import Principia.UnitDistance.Order11
/-
  一般部：`n = 16` の単位距離実現と、証明書を候補ごとに使い回す二つの補題。

  核（区間演算・`trilat_core`・`lam_box`・`triStep_sound`・`chk`・`chk_sound`・
  `normalize`・`close_edges`）は`UnitDistance.Order11` をそのまま使う
  （`Erdos1178a`・`Erdos1178b` は編集していない。どちらも頂点の個数に依らない）。
  この段で足すのは三つだけである：

  * `Realiz`（`Fin 16` 版）と `close_realiz`
  * `no_edges_sub`：`F` の辺がすべて `E` の辺なら、`F` の非実現から `E` の非実現が出る
      （辺が増えれば条件は強くなるだけ）。辺の向きは `isEdge` が吸収する。
  * `no_edges_map`：頂点の名前を `σ : ℕ → ℕ` で貼り替えても非実現は保たれる。

  この二つを合わせた `close_relabel` で、**同型な候補は代表の証明書を使い回せる**。
  同型不変性を Lean の中で述べるのではなく、**候補ごとに頂点写像 σ を証明書として差し出し、
  包含を `decide` で検める**形である（2,100 類の真の同型類数は 993 なので、
  証明書を持つのは 995 類だけで足りる）。

  sorry 0・native_decide 不使用。
-/

namespace UnitDistance.Order16

/-! ## 1. `Fin 16` の単位距離実現 -/

def emb (n : ℕ) : Fin 16 := ⟨n % 16, Nat.mod_lt _ (by norm_num)⟩

/-- `E` を辺集合とする 16 点グラフの平面単位距離実現：
  辺は距離 1・**非辺は制約なし**・異なる頂点は異なる点。 -/
def Realiz (E : List (ℕ × ℕ)) (p : Fin 16 → ℝ × ℝ) : Prop :=
  (∀ e ∈ E, ((p (emb e.1)).1 - (p (emb e.2)).1)^2
      + ((p (emb e.1)).2 - (p (emb e.2)).2)^2 = 1) ∧ Function.Injective p

lemma realiz_edges {E : List (ℕ × ℕ)} {p : Fin 16 → ℝ × ℝ} (h : Realiz E p) :
    UnitDistance.Order11.Edges E (fun n => (p (emb n)).1) (fun n => (p (emb n)).2) := h.1

/-- 辺の条件の版から実現の非存在へ（単射性は使わない）。 -/
theorem close_realiz (E : List (ℕ × ℕ))
    (h : ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y) :
    ∀ p : Fin 16 → ℝ × ℝ, ¬ Realiz E p := fun _ hp => h _ _ (realiz_edges hp)

/-! ## 2. 証明書を使い回す二つの補題 -/

/-- **部分集合**：`F` の辺がどれも `E` の辺（向きは問わない）なら、
  `F` が実現しないことから `E` が実現しないことが出る。 -/
theorem no_edges_sub (E F : List (ℕ × ℕ))
    (hsub : ∀ e ∈ F, UnitDistance.Order11.isEdge E e.1 e.2 = true)
    (h : ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges F x y) :
    ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y := by
  intro x y hh
  exact h x y (fun e he => UnitDistance.Order11.edge_eq hh (hsub e he))

/-- **貼り替え**：頂点の名前を `σ` で付け替えても非実現は保たれる。 -/
theorem no_edges_map (F : List (ℕ × ℕ)) (σ : ℕ → ℕ)
    (h : ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges F x y) :
    ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges (F.map (fun e => (σ e.1, σ e.2))) x y := by
  intro x y hh
  refine h (fun n => x (σ n)) (fun n => y (σ n)) ?_
  intro e he
  exact hh (σ e.1, σ e.2) (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- 頂点写像を有限列で与える（範囲外は 0。証明書としてはこれで十分）。 -/
def pm (l : List ℕ) (n : ℕ) : ℕ := l.getD n 0

/-- **同型な候補を代表の証明書で閉じる道具**：`l` は代表 `F` の頂点を候補 `E` の頂点へ
  送る列。`hsub` は「`σ` で写した `F` の辺がどれも `E` の辺」という決定可能な検査。 -/
theorem close_relabel (E F : List (ℕ × ℕ)) (l : List ℕ)
    (hsub : ∀ e ∈ F.map (fun e => (pm l e.1, pm l e.2)),
      UnitDistance.Order11.isEdge E e.1 e.2 = true)
    (h : ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges F x y) :
    ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y :=
  no_edges_sub E _ hsub (no_edges_map F (pm l) h)

end UnitDistance.Order16

#print axioms UnitDistance.Order16.no_edges_sub
#print axioms UnitDistance.Order16.no_edges_map
#print axioms UnitDistance.Order16.close_relabel
#print axioms UnitDistance.Order16.realiz_edges
#print axioms UnitDistance.Order16.close_realiz
