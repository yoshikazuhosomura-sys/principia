import Mathlib
import Principia.UnitDistance.Order11
/-
  一般部：`n = 10` の単位距離実現と、起点辺の向きを問わない正規化。

  的は `f(4) ≤ 15` の連鎖に残っていた穴の一つ、**`H` の実現性フィルタ**である。
  `H` フィルタの段（Lean の外）は `L₃[10]`（`α ≤ 3` の 10 点グラフ 666 類）のうち最小次数 `≥ 3` の 571 類に
  素の三辺測量＋区間演算を当て、**296 類を「平面に単位距離で実現しない」として捨てた**。
  残る 275 類だけが `n=16` の列挙（Lean の外の列挙）に回された。
  この段はその 296 類（`R`）の非実現を Lean の中で閉じる。

  核（区間演算・`trilat_core`・`lam_box`・`triStep_sound`・`chk`・`chk_sound`・
  `normalize`・`holds_st0`）は`UnitDistance.Order11` をそのまま使う
  （`Erdos1178a`・`Erdos1178b` は編集していない。どちらも頂点の個数に依らない）。
  この段が足すのは二つだけである：

  * `Realiz`（`Fin 10` 版）と `close_realiz`
  * `normalize'` / `close_edges'`：起点辺を `isEdge E a b = true`（向きを問わない）で
      受ける版。`Order11` の段の `close_edges` は `(a, b) ∈ E` という**順序つき**の membership を
      求めるので、証明器が `a > b` の向きを起点に選んだ類が閉じられなかった。

  sorry 0・native_decide 不使用。
-/

namespace UnitDistance.Order10

/-! ## 1. `Fin 10` の単位距離実現 -/

def emb (n : ℕ) : Fin 10 := ⟨n % 10, Nat.mod_lt _ (by norm_num)⟩

/-- `E` を辺集合とする 10 点グラフの平面単位距離実現：
  辺は距離 1・**非辺は制約なし**・異なる頂点は異なる点。 -/
def Realiz (E : List (ℕ × ℕ)) (p : Fin 10 → ℝ × ℝ) : Prop :=
  (∀ e ∈ E, ((p (emb e.1)).1 - (p (emb e.2)).1)^2
      + ((p (emb e.1)).2 - (p (emb e.2)).2)^2 = 1) ∧ Function.Injective p

lemma realiz_edges {E : List (ℕ × ℕ)} {p : Fin 10 → ℝ × ℝ} (h : Realiz E p) :
    UnitDistance.Order11.Edges E (fun n => (p (emb n)).1) (fun n => (p (emb n)).2) := h.1

/-- 辺の条件の版から実現の非存在へ（単射性は使わない）。 -/
theorem close_realiz (E : List (ℕ × ℕ))
    (h : ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y) :
    ∀ p : Fin 10 → ℝ × ℝ, ¬ Realiz E p := fun _ hp => h _ _ (realiz_edges hp)

/-! ## 2. 起点辺の向きを問わない正規化 -/

/-- **正規化**（向きを問わない版）：辺 `ab` があれば、回転と平行移動で
  `a = (0,0)`・`b = (1,0)` にできる。`Order11` の段の `normalize` の
  `(a, b) ∈ E` を `isEdge E a b = true` に緩めただけで、証明は逐語に同じである。 -/
lemma normalize' (E : List (ℕ × ℕ)) (a b : ℕ) (hab : UnitDistance.Order11.isEdge E a b = true)
    (x y : ℕ → ℝ) (h : UnitDistance.Order11.Edges E x y) :
    ∃ X Y : ℕ → ℝ, UnitDistance.Order11.Edges E X Y ∧ X a = 0 ∧ Y a = 0 ∧ X b = 1 ∧ Y b = 0 := by
  have hnorm : (x b - x a)^2 + (y b - y a)^2 = 1 := by
    linear_combination UnitDistance.Order11.edge_eq h hab
  refine ⟨fun n => (x n - x a) * (x b - x a) + (y n - y a) * (y b - y a),
          fun n => -((x n - x a) * (y b - y a)) + (y n - y a) * (x b - x a), ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hh := h e he
    linear_combination ((x b - x a)^2 + (y b - y a)^2) * hh + hnorm
  · ring
  · ring
  · linear_combination hnorm
  · ring

/-- **候補を閉じる道具**（向きを問わない版）：証明書 `t`・平面 `pl` の検査が通れば
  辺の条件を満たす座標は無い。 -/
theorem close_edges' (E : List (ℕ × ℕ)) (a b : ℕ)
    (hab : UnitDistance.Order11.isEdge E a b = true) (t : UnitDistance.Order11.Tr)
    (pl : List (ℕ × ℕ × ℕ))
    (hchk : UnitDistance.Order11.chk E t pl (UnitDistance.Order11.st0 a b) = true) :
    ∀ x y : ℕ → ℝ, ¬ UnitDistance.Order11.Edges E x y := by
  intro x y h
  obtain ⟨X, Y, hXY, h1, h2, h3, h4⟩ := normalize' E a b hab x y h
  exact UnitDistance.Order11.chk_sound E X Y hXY t pl (UnitDistance.Order11.st0 a b)
    (UnitDistance.Order11.holds_st0 h1 h2 h3 h4) hchk

end UnitDistance.Order10

#print axioms UnitDistance.Order10.close_realiz
#print axioms UnitDistance.Order10.normalize'
#print axioms UnitDistance.Order10.close_edges'
#print axioms UnitDistance.Order10.realiz_edges
