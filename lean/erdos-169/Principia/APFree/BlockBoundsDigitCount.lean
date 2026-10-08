/-

  エルデシュ問題 #169。**逆数和の挟み込みの Lean 化（ブロック側の橋）**。

  APFreeBlockBounds で骨組み（`BlkF` / `loI` / `hiI` / `loI_le` / `le_hiI`）と頭 Z₀ は閉じた。
  ブロック側に残っていた穴はただ一つ：
    `loI` の葉が要求する **個数 `cf n r ≤ (BlkF p n r).card`** をどこから取るか。
  頭は p = 2 で重みが恒等的に 0 だから `2^n` で済んだが、一般の p ではそうはいかない。
  `(BlkF p n r).card` を素朴な再帰で数えると p^n 通りになり、kernel では動かない。

  本ファイルはその穴を **桁 DP の行（`cntTab`）** で埋める。
    `cntTab p n : List ℕ` は「n 桁・各桁 < p・重み和 r の個数」を r = 0,1,2,… と並べた行。
    一段の畳み込み `nextRow p row = Σ_{k<p} (T p k 個の 0) ++ row`（成分ごとの和）で作る。
  そして
    **`cntTab_card : (cntTab p n).getD r 0 = (BlkF p n r).card`**
  を証明する。これで `cf := fun n r => (cntTab p n).getD r 0` が `loI_le` にそのまま入り、
  **ブロック側の数学的な穴は閉じる**（残るのは kernel の実行時間だけになる）。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBounds

namespace APFree.BlockBounds

open APFree.StepsMaxElement

set_option maxRecDepth 4000000

/-! ## 1. 行の演算 -/

/-- 成分ごとの和（長さが違えば長い方に合わせる）。 -/
def addL : List ℕ → List ℕ → List ℕ
  | [], y => y
  | x, [] => x
  | a :: x, b :: y => (a + b) :: addL x y

/-- 右へ `t` だけずらす（先頭に 0 を `t` 個）。 -/
def shR : ℕ → List ℕ → List ℕ
  | 0, l => l
  | t + 1, l => 0 :: shR t l

@[simp] theorem addL_nil_left (y : List ℕ) : addL [] y = y := by cases y <;> rfl

@[simp] theorem addL_nil_right (x : List ℕ) : addL x [] = x := by cases x <;> rfl

theorem getD_addL : ∀ (x y : List ℕ) (r : ℕ),
    (addL x y).getD r 0 = x.getD r 0 + y.getD r 0 := by
  intro x
  induction x with
  | nil => intro y r; simp
  | cons a x ih =>
      intro y r
      cases y with
      | nil => simp
      | cons b y =>
          cases r with
          | zero => simp [addL, List.getD]
          | succ r =>
              simp only [addL, List.getD_cons_succ]
              exact ih y r

theorem getD_shR : ∀ (t : ℕ) (l : List ℕ) (r : ℕ),
    (shR t l).getD r 0 = if t ≤ r then l.getD (r - t) 0 else 0 := by
  intro t
  induction t with
  | zero => intro l r; simp [shR]
  | succ t ih =>
      intro l r
      cases r with
      | zero => simp [shR, List.getD]
      | succ r =>
          simp only [shR, List.getD_cons_succ, ih l r]
          by_cases h : t ≤ r
          · rw [if_pos h, if_pos (by omega : t + 1 ≤ r + 1)]
            congr 1
            omega
          · rw [if_neg h, if_neg (by omega : ¬ (t + 1 ≤ r + 1))]

/-! ## 2. 一段の畳み込み -/

/-- 桁 DP の一段。`row` は「n 桁で重み r の個数」の行、戻り値は n+1 桁の行。 -/
def nextRow (p : ℕ) (row : List ℕ) : List ℕ :=
  ((List.range p).map fun k => shR (T p k) row).foldr addL []

theorem getD_foldr_addL : ∀ (L : List (List ℕ)) (r : ℕ),
    (L.foldr addL []).getD r 0 = (L.map fun l => l.getD r 0).sum := by
  intro L
  induction L with
  | nil => intro r; simp
  | cons l L ih =>
      intro r
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, getD_addL, ih r]

theorem getD_nextRow (p : ℕ) (row : List ℕ) (r : ℕ) :
    (nextRow p row).getD r 0
      = ∑ k ∈ Finset.range p, (if T p k ≤ r then row.getD (r - T p k) 0 else 0) := by
  rw [nextRow, getD_foldr_addL, List.map_map, ← sum_range_list]
  congr 1
  refine List.map_congr_left ?_
  intro k _
  simpa using getD_shR (T p k) row r

/-! ## 3. 表と、その正しさ -/

/-- **桁 DP の表**。`cntTab p n` の第 r 成分が「n 桁・各桁 < p・重み和 r」の個数。 -/
def cntTab (p : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => nextRow p (cntTab p n)

/-- **本ファイルの中心**：表の値はブロックの個数そのものである。 -/
theorem cntTab_card (p : ℕ) (hp : 1 ≤ p) : ∀ (n r : ℕ),
    (cntTab p n).getD r 0 = (BlkF p n r).card := by
  intro n
  induction n with
  | zero =>
      intro r
      cases r with
      | zero => simp [cntTab, List.getD, BlkF_zero]
      | succ r =>
          simp only [cntTab, List.getD_cons_succ, BlkF_zero, if_neg (Nat.succ_ne_zero r)]
          simp [List.getD]
  | succ n ih =>
      intro r
      rw [cntTab, getD_nextRow, card_BlkF_succ p hp n r]
      refine Finset.sum_congr rfl ?_
      intro k _
      by_cases hT : T p k ≤ r
      · rw [if_pos hT, if_pos hT, ih]
      · rw [if_neg hT, if_neg hT]

/-- 表から取った個数（`loI` の `cf` にそのまま渡せる形）。 -/
def cfT (p : ℕ) (n r : ℕ) : ℕ := (cntTab p n).getD r 0

theorem cfT_le (p : ℕ) (hp : 1 ≤ p) : ∀ n r, cfT p n r ≤ (BlkF p n r).card := by
  intro n r; rw [cfT, cntTab_card p hp n r]

theorem card_le_cfT (p : ℕ) (hp : 1 ≤ p) : ∀ r, (BlkF p 0 r).card ≤ cfT p 0 r := by
  intro r; rw [cfT, cntTab_card p hp 0 r]

/-! ## 4. 一つの窓についての挟み込み（ブロック側の一般形） -/

/-- **一つの窓の下界**。`p ≥ 1`、offset `a > 0`、展開の深さ `d` は自由。
    `cf` は桁 DP の表から取るので、**外から与える証明義務は無い**。 -/
theorem window_lower (p SC : ℕ) (hSC : 0 < SC) (hp : 1 ≤ p) (d a n r : ℕ) (ha : 0 < a) :
    ((loI p SC (cfT p) d a n r : ℕ) : ℚ) / SC ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) :=
  loI_le p SC hSC hp (cfT p) (cfT_le p hp) d a n r ha

/-- **一つの窓の上界**。 -/
theorem window_upper (p SC : ℕ) (hSC : 0 < SC) (hp : 1 ≤ p) (d a n r : ℕ) (ha : 0 < a)
    (hnd : n ≤ d) :
    ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) ≤ ((hiI p SC (cfT p) d a n r : ℕ) : ℚ) / SC :=
  le_hiI p SC hSC hp (cfT p) (card_le_cfT p hp) d a n r ha hnd

/-! ## 5. 窓の族の和（段を足し合わせる形） -/

/-- 窓の一覧 `(p, n, r, a)` に対する下界の総和（SC 倍・整数）。`d` は展開の深さ。 -/
def totLo (SC d : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | (p, n, r, a) :: ws => loI p SC (cfT p) d a n r + totLo SC d ws

/-- 窓の族の逆数和（各窓 `a + B(p,n,r)` の寄与の総和）。 -/
def sumWin : List (ℕ × ℕ × ℕ × ℕ) → ℚ
  | [] => 0
  | (p, n, r, a) :: ws => (∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s)) + sumWin ws

/-- **窓の族についての下界**（段を足し合わせた形）。 -/
theorem totLo_le (SC : ℕ) (hSC : 0 < SC) (d : ℕ) :
    ∀ ws : List (ℕ × ℕ × ℕ × ℕ),
      (∀ w ∈ ws, 1 ≤ w.1 ∧ 0 < w.2.2.2) →
      ((totLo SC d ws : ℕ) : ℚ) / SC ≤ sumWin ws := by
  intro ws
  induction ws with
  | nil => intro _; simp [totLo, sumWin]
  | cons w ws ih =>
      intro h
      obtain ⟨p, n, r, a⟩ := w
      have hw := h (p, n, r, a) (by simp)
      have hrest : ∀ w ∈ ws, 1 ≤ w.1 ∧ 0 < w.2.2.2 := fun w hw => h w (by simp [hw])
      have h1 : ((loI p SC (cfT p) d a n r : ℕ) : ℚ) / SC
          ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) :=
        window_lower p SC hSC hw.1 d a n r hw.2
      have h2 := ih hrest
      simp only [totLo, sumWin]
      rw [Nat.cast_add, add_div]
      exact add_le_add h1 h2

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.cntTab_card
#print axioms APFree.BlockBounds.totLo_le
