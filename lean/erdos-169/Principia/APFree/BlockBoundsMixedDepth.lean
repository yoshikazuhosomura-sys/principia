/-

  エルデシュ問題 #169。**逆数和の下界を、窓ごとに違う深さで取る。**

  APFreeBlockBoundsDigitCount の `totLo` は窓の族に**一つの深さ d** を使う。ところがAPFreeBlockBoundsMixedDepth の寸法取りで
  「d=2→3 の利得の 99.8% は先頭 20 窓（早い段・小さい p）に集中する」ことが分かった。
  ⟹ 深さを一律に上げる（葉 40 万）のは無駄で、**利得/葉 の比で配る**方がはるかに安い。

  本ファイルは窓ごとの深さを持つ版 `totLoD` と、その下界の定理 `totLoD_le` を置く。
  リストの要素は `((p, n, r, a), d)`。`List.map Prod.fst` で窓の一覧に戻る。
  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsDigitCount

namespace APFree.BlockBounds

/-- 窓ごとに深さ `d` を指定した下界の総和（SC 倍・整数）。 -/
def totLoD (SC : ℕ) : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) → ℕ
  | [] => 0
  | ((p, n, r, a), d) :: ws => loI p SC (cfT p) d a n r + totLoD SC ws

/-- 窓の族の逆数和はリストの連結について足し算になる。 -/
theorem sumWin_append : ∀ l₁ l₂ : List (ℕ × ℕ × ℕ × ℕ),
    sumWin (l₁ ++ l₂) = sumWin l₁ + sumWin l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp [sumWin]
  | cons w l₁ ih =>
      intro l₂
      obtain ⟨p, n, r, a⟩ := w
      simp only [List.cons_append, sumWin, ih l₂]
      ring

/-- **窓ごとに深さを変えた下界**。`window_lower` を各窓に当てるだけ。 -/
theorem totLoD_le (SC : ℕ) (hSC : 0 < SC) :
    ∀ ws : List ((ℕ × ℕ × ℕ × ℕ) × ℕ),
      (∀ w ∈ ws, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2) →
      ((totLoD SC ws : ℕ) : ℚ) / SC ≤ sumWin (ws.map Prod.fst) := by
  intro ws
  induction ws with
  | nil => intro _; simp [totLoD, sumWin]
  | cons w ws ih =>
      intro h
      obtain ⟨⟨p, n, r, a⟩, d⟩ := w
      have hw := h ((p, n, r, a), d) (by simp)
      have hrest : ∀ w ∈ ws, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := fun w hw => h w (by simp [hw])
      have h1 : ((loI p SC (cfT p) d a n r : ℕ) : ℚ) / SC
          ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) :=
        window_lower p SC hSC hw.1 d a n r hw.2
      have h2 := ih hrest
      simp only [totLoD, List.map_cons, sumWin]
      rw [Nat.cast_add, add_div]
      exact add_le_add h1 h2

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.totLoD_le
