/-

  エルデシュ問題 #169。**窓が互いに素であることを Lean に入れ、
  下界を「集合 A の上の Σ 1/n」についての言明に上げる。**

  【なぜ要るか（APFreeBlockBoundsDigitCount (G) の残り (ii)）】
    `APFreeBlockBoundsTotalDepthTwo.total_lower` も `APFreeBlockBoundsBudgetTotal.total_lower4` も、
    「窓ごとの逆数和の**総和**」についての言明であって、
    「集合 A = Z₀ ∪ ⋃(a_i + B_i) の上の Σ 1/n」ではない。
    両者が等しいためには窓が互いに素であればよい。Python では検査済み
    （offset 昇順に並べて `a_{i+1} > a_i + mxv(p_i,q_i)`：破れ 0 対 / 171 対、
      最小の隙間 20171202）。本ファイルはそれを Lean に入れる。

  【要点】
    ・頭 Z₀ は `winF (2, 16, 0, 1)` そのものである（⟹ APFreeBlockBounds の O-3）。
      だから頭を特別扱いせず、**窓の一覧の先頭に (2,16,0,1) を置くだけ**でよい。
    ・区間 [a, a + mxv p n] が互いに素なら十分（真の max ではなく `mxv` で足りる）。
    ・並びは既に offset 昇順なので、検査は `ordWB`（Bool）の kernel 評価一つで済む。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsBudgetTotal

namespace APFree.WindowsDisjoint

open APFree.BlockBounds APFree.StepsMaxElement

set_option maxRecDepth 4000000

/-! ## 1. 窓を Finset として置く -/

/-- 窓 `(p, n, r, a)` が覆う集合 `a + B(p, n, r)`。 -/
def winF : (ℕ × ℕ × ℕ × ℕ) → Finset ℕ
  | (p, n, r, a) => (BlkF p n r).image (fun s => a + s)

/-- 窓の一覧が覆う集合。 -/
def unionW : List (ℕ × ℕ × ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | w :: ws => winF w ∪ unionW ws

/-- 窓が使う区間の右端（`mxv` で十分。真の max より広く取る）。 -/
def hiW : (ℕ × ℕ × ℕ × ℕ) → ℕ
  | (p, n, r, a) => a + mxv p n

/-- 窓の元は区間の右端以下。 -/
theorem winF_ub (p n r a : ℕ) (hp : 1 ≤ p) :
    ∀ x ∈ winF (p, n, r, a), x ≤ hiW (p, n, r, a) := by
  intro x hx
  simp only [winF, Finset.mem_image] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have h := BlkF_le p hp n r s hs
  simp only [hiW]
  omega

/-- 一覧の全 offset が `b` 以上なら、覆う集合の元も `b` 以上。 -/
theorem unionW_lb : ∀ (ws : List (ℕ × ℕ × ℕ × ℕ)) (b : ℕ),
    (∀ w ∈ ws, b ≤ w.2.2.2) → ∀ x ∈ unionW ws, b ≤ x := by
  intro ws
  induction ws with
  | nil => intro b _ x hx; simp [unionW] at hx
  | cons w ws ih =>
      intro b h x hx
      obtain ⟨p, n, r, a⟩ := w
      simp only [unionW, Finset.mem_union] at hx
      rcases hx with hx | hx
      · simp only [winF, Finset.mem_image] at hx
        obtain ⟨s, _, rfl⟩ := hx
        have hb := h (p, n, r, a) (by simp)
        simp only at hb
        omega
      · exact ih b (fun v hv => h v (by simp [hv])) x hx

/-! ## 2. 並びの検査（Bool。kernel 評価一つで済む） -/

/-- 「どの窓も、後ろの窓すべてより厳密に左で終わる」。 -/
def ordWB : List (ℕ × ℕ × ℕ × ℕ) → Bool
  | [] => true
  | w :: ws => (ws.all fun v => decide (hiW w < v.2.2.2)) && ordWB ws

/-! ## 3. 和が分かれる -/

theorem sum_unionW (f : ℕ → ℚ) : ∀ ws : List (ℕ × ℕ × ℕ × ℕ),
    (∀ w ∈ ws, 1 ≤ w.1) → ordWB ws = true →
    ∑ x ∈ unionW ws, f x = (ws.map fun w => ∑ x ∈ winF w, f x).sum := by
  intro ws
  induction ws with
  | nil => intro _ _; simp [unionW]
  | cons w ws ih =>
      intro hp hord
      obtain ⟨p, n, r, a⟩ := w
      rw [ordWB, Bool.and_eq_true] at hord
      obtain ⟨hall, hrest⟩ := hord
      have hlt : ∀ v ∈ ws, hiW (p, n, r, a) < v.2.2.2 := by
        intro v hv
        have := (List.all_eq_true.mp hall) v hv
        simpa using this
      have hdisj : Disjoint (winF (p, n, r, a)) (unionW ws) := by
        rw [Finset.disjoint_left]
        intro x hx hx2
        have h1 : x ≤ hiW (p, n, r, a) := winF_ub p n r a (hp (p, n, r, a) (by simp)) x hx
        have h2 : hiW (p, n, r, a) + 1 ≤ x :=
          unionW_lb ws (hiW (p, n, r, a) + 1) (fun v hv => hlt v hv) x hx2
        omega
      rw [unionW, Finset.sum_union hdisj, List.map_cons, List.sum_cons,
        ih (fun v hv => hp v (by simp [hv])) hrest]

/-! ## 4. 窓の逆数和は `sumWin` の項そのもの -/

theorem sum_winF (p n r a : ℕ) :
    ∑ x ∈ winF (p, n, r, a), (1 : ℚ) / x = ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) := by
  rw [winF, Finset.sum_image (by intro x _ y _ h; exact Nat.add_left_cancel h)]
  refine Finset.sum_congr rfl ?_
  intro s _
  push_cast
  ring_nf

theorem map_sum_eq_sumWin : ∀ ws : List (ℕ × ℕ × ℕ × ℕ),
    (ws.map fun w => ∑ x ∈ winF w, (1 : ℚ) / x).sum = sumWin ws := by
  intro ws
  induction ws with
  | nil => simp [sumWin]
  | cons w ws ih =>
      obtain ⟨p, n, r, a⟩ := w
      simp only [List.map_cons, List.sum_cons, sumWin, ih, sum_winF]

/-- **窓が互いに素なら、集合の上の逆数和は窓ごとの逆数和の総和に等しい**。 -/
theorem sum_set_eq (ws : List (ℕ × ℕ × ℕ × ℕ))
    (hp : ∀ w ∈ ws, 1 ≤ w.1) (hord : ordWB ws = true) :
    ∑ x ∈ unionW ws, (1 : ℚ) / x = sumWin ws := by
  rw [sum_unionW (fun x => (1 : ℚ) / x) ws hp hord, map_sum_eq_sumWin]

/-! ## 5. 本ファイルの構成に当てる -/

/-- **構成そのもの**：頭 Z₀ と 100 段 171 個の窓を、一本の一覧にする。
    頭 Z₀ = 1 + B(2,16,0) は `winF (2,16,0,1)` そのものである（⟹ O-3）。 -/
def winsAll : List (ℕ × ℕ × ℕ × ℕ) := (2, 16, 0, 1) :: (wins50 ++ wins100b)

/-- 構成が覆う集合 A。 -/
def setA : Finset ℕ := unionW winsAll

theorem winsAll_p : ∀ w ∈ winsAll, 1 ≤ w.1 := by decide

set_option maxHeartbeats 4000000 in
/-- **窓は互いに素である**（171 対 ＋ 頭。kernel 評価）。 -/
theorem winsAll_ord : ordWB winsAll = true := by decide

theorem Z0F_eq_winF : Z0F = winF (2, 16, 0, 1) := rfl

/-- 集合 A の上の逆数和は、頭と窓の逆数和の総和に等しい。 -/
theorem sum_setA :
    ∑ x ∈ setA, (1 : ℚ) / x
      = (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins50 + sumWin wins100b := by
  have h := sum_set_eq winsAll winsAll_p winsAll_ord
  rw [setA, h, winsAll, sumWin, sumWin_append, Z0F_eq_winF, sum_winF]
  ring

/-- **本ファイルの結論（構成そのものについて）**：
    Wróblewski 型 3-AP-free 集合 A の逆数和は **3.0085383814002 を超える**。
    これは「窓ごとの逆数和の総和」ではなく、**集合 A の上の Σ 1/n** についての言明である。 -/
theorem setA_lower : (30085383814002 : ℚ) / 10 ^ 13 < ∑ x ∈ setA, (1 : ℚ) / x := by
  rw [sum_setA]; exact total_lower4

/-- 記録 3.00849 との比較（集合そのものについて）。 -/
theorem setA_beats_record : (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ setA, (1 : ℚ) / x := by
  have h := setA_lower
  have : (300849 : ℚ) / 10 ^ 5 < (30085383814002 : ℚ) / 10 ^ 13 := by norm_num
  linarith

end APFree.WindowsDisjoint

/-! ### 公理の確認 -/

#print axioms APFree.WindowsDisjoint.winsAll_p
#print axioms APFree.WindowsDisjoint.winsAll_ord
#print axioms APFree.WindowsDisjoint.sum_setA
#print axioms APFree.WindowsDisjoint.setA_lower
#print axioms APFree.WindowsDisjoint.setA_beats_record
