/-
  Principia.APFree.LeafUpperBound — B

  【問い（予告 B）】
  ブロックの逆数和の**上側** `hiI` は `le_hiI` が `n ≤ d`（＝**全展開**）を要求するので、
  n = 16 のような窓では葉が (2p−1)^n 個になって回らない。挟み込みが片側しか立たない。

  【原因（本ファイルで名指しした）】`hiI` の**打ち切りの葉**が
      `hiI p SC cf 0 a n r = cf 0 r * cdiv SC a`
  と、個数を **`cf 0 r`**（＝ n = 0 の個数）で数えている。n > 0 で打ち切ると
  部分木の元の個数は `cf n r` であって `cf 0 r` ではないので、この式は上界にならない。
  だから `le_hiI` は `n ≤ d`（打ち切りが起きない）を仮定するしかなかった。

  【直し方（一文字）】葉の個数を **`cf n r`** にする。元は必ず 0 以上なので
      Σ_{s ∈ B(p,n,r)} 1/(a+s) ≤ |B(p,n,r)| · (1/a) ≤ cf n r · ⌈SC/a⌉ / SC
  が任意の深さで成り立つ。⟹ **`n ≤ d` が要らなくなる。**

  代償は「尾を 0 で押さえた」分だけ緩むこと。より締めるには 1/a を
  1/(a + 尾の**最小**) に替えればよい（`mxv` の対になる `mnv` が要る）。
  本ファイルは第一版として 1/a のままにする（`totLoD` と同じ骨組みで、
  窓ごとに深さを配れる `totHiD` まで置く）。

  sorry 0・native_decide 不使用。既存ファイルは編集していない。
-/
import Principia.APFree.BlockBoundsMixedDepth

namespace APFree.LeafUpperBound

open APFree.StepsMaxElement APFree.BlockBounds

/-- **上界（第862 版）**。打ち切りの葉で個数を `cf n r` に直したもの。 -/
def hiJ (p SC : ℕ) (cf : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, a, n, r => cf n r * cdiv SC a
  | _ + 1, a, 0, r => cf 0 r * cdiv SC a
  | d + 1, a, n + 1, r =>
      ((List.range p).map fun k =>
        if T p k ≤ r then hiJ p SC cf d (a + k * (2 * p - 1) ^ n) n (r - T p k) else 0).sum

/-- 葉の上からの評価（**任意の n で**）。元は 0 以上なので 1/(a+s) ≤ 1/a を使う。 -/
theorem leaf_upper_gen (p SC : ℕ) (hSC : 0 < SC) (c a n r : ℕ) (ha : 0 < a)
    (hc : (BlkF p n r).card ≤ c) :
    ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) ≤ ((c * cdiv SC a : ℕ) : ℚ) / SC := by
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hSCq : (0 : ℚ) < SC := by exact_mod_cast hSC
  have hone : (1 : ℚ) / (a : ℚ) ≤ ((cdiv SC a : ℕ) : ℚ) / (SC : ℚ) := by
    have hSCa : (SC : ℚ) ≤ ((cdiv SC a : ℕ) : ℚ) * (a : ℚ) := by
      exact_mod_cast cdiv_ge SC a ha
    rw [div_le_div_iff₀ haq hSCq]; linarith
  have hterm : ∀ s ∈ BlkF p n r, (1 : ℚ) / ((a : ℚ) + (s : ℚ)) ≤ (1 : ℚ) / (a : ℚ) := by
    intro s _
    have : (0 : ℚ) ≤ (s : ℚ) := by positivity
    apply one_div_le_one_div_of_le haq; linarith
  have hcq : ((BlkF p n r).card : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc
  have hnn : (0 : ℚ) ≤ ((cdiv SC a : ℕ) : ℚ) / (SC : ℚ) := by positivity
  calc ∑ s ∈ BlkF p n r, (1 : ℚ) / ((a : ℚ) + (s : ℚ))
      ≤ ∑ _s ∈ BlkF p n r, (1 : ℚ) / (a : ℚ) := Finset.sum_le_sum hterm
    _ = ((BlkF p n r).card : ℚ) * ((1 : ℚ) / (a : ℚ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (c : ℚ) * (((cdiv SC a : ℕ) : ℚ) / (SC : ℚ)) := by
          apply mul_le_mul hcq hone (by positivity) (by positivity)
    _ = ((c * cdiv SC a : ℕ) : ℚ) / (SC : ℚ) := by push_cast; ring

/-- **本定理**：`hiJ` は任意の深さ `d` で上界である（`n ≤ d` は要らない）。 -/
theorem le_hiJ (p SC : ℕ) (hSC : 0 < SC) (hp : 1 ≤ p) (cf : ℕ → ℕ → ℕ)
    (hcf : ∀ n r, (BlkF p n r).card ≤ cf n r) :
    ∀ (d a n r : ℕ), 0 < a →
      ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) ≤ ((hiJ p SC cf d a n r : ℕ) : ℚ) / SC := by
  intro d
  induction d with
  | zero =>
      intro a n r ha
      exact leaf_upper_gen p SC hSC _ a n r ha (hcf n r)
  | succ d ih =>
      intro a n r ha
      match n with
      | 0 => exact leaf_upper_gen p SC hSC _ a 0 r ha (hcf 0 r)
      | n + 1 =>
          rw [hiJ, sum_range_list, sum_BlkF_succ p hp n r]
          have hcast : ∀ x y v : ℕ,
              (1 : ℚ) / ((x : ℚ) + ((y + v : ℕ) : ℚ))
                = (1 : ℚ) / (((x + y : ℕ) : ℚ) + (v : ℚ)) := by
            intro x y v; simp only [Nat.cast_add]; ring_nf
          have key : ∀ k ∈ Finset.range p,
              (if T p k ≤ r then
                  ∑ v ∈ BlkF p n (r - T p k),
                    (1 : ℚ) / ((a : ℚ) + ((k * (2 * p - 1) ^ n + v : ℕ) : ℚ))
               else 0)
                ≤ ((if T p k ≤ r then hiJ p SC cf d (a + k * (2 * p - 1) ^ n) n (r - T p k)
                    else 0 : ℕ) : ℚ) / SC := by
            intro k _
            by_cases hT : T p k ≤ r
            · rw [if_pos hT, if_pos hT]
              have hpos : 0 < a + k * (2 * p - 1) ^ n := by omega
              have hih := ih (a + k * (2 * p - 1) ^ n) n (r - T p k) hpos
              refine le_trans (le_of_eq ?_) hih
              exact Finset.sum_congr rfl fun v _ => hcast a (k * (2 * p - 1) ^ n) v
            · rw [if_neg hT, if_neg hT]; simp
          refine le_trans (Finset.sum_le_sum key) (le_of_eq ?_)
          rw [Nat.cast_sum, Finset.sum_div]

/-! ## 窓ごとに深さを配る版（`totLoD` の上側の対） -/

/-- 窓ごとに深さ `d` を指定した**上界**の総和（SC 倍・整数）。 -/
def totHiD (SC : ℕ) (cf : ℕ → ℕ → ℕ → ℕ) :
    List ((ℕ × ℕ × ℕ × ℕ) × ℕ) → ℕ
  | [] => 0
  | ((p, n, r, a), d) :: ws => hiJ p SC (cf p) d a n r + totHiD SC cf ws

/-- **窓ごとに深さを変えた上界**。`le_hiJ` を各窓に当てるだけ。 -/
theorem totHiD_le (SC : ℕ) (hSC : 0 < SC) (cf : ℕ → ℕ → ℕ → ℕ)
    (hcf : ∀ p n r, (BlkF p n r).card ≤ cf p n r) :
    ∀ ws : List ((ℕ × ℕ × ℕ × ℕ) × ℕ),
      (∀ w ∈ ws, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2) →
      sumWin (ws.map Prod.fst) ≤ ((totHiD SC cf ws : ℕ) : ℚ) / SC := by
  intro ws
  induction ws with
  | nil => intro _; simp [totHiD, sumWin]
  | cons w ws ih =>
      intro h
      obtain ⟨⟨p, n, r, a⟩, d⟩ := w
      have hw := h ((p, n, r, a), d) (by simp)
      have hrest : ∀ w ∈ ws, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := fun w hw => h w (by simp [hw])
      have h1 : ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s)
          ≤ ((hiJ p SC (cf p) d a n r : ℕ) : ℚ) / SC :=
        le_hiJ p SC hSC hw.1 (cf p) (fun n r => hcf p n r) d a n r hw.2
      have h2 := ih hrest
      simp only [totHiD, List.map_cons, sumWin]
      rw [Nat.cast_add, add_div]
      exact add_le_add h1 h2

end APFree.LeafUpperBound

/-! ### 公理の確認 -/

#print axioms APFree.LeafUpperBound.le_hiJ
#print axioms APFree.LeafUpperBound.totHiD_le
#print axioms APFree.LeafUpperBound.leaf_upper_gen
