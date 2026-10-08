/-
  ブロックの個数の詰め込み計算 —
  エルデシュ問題 #169、`k = 4`。**`|B(p,n,r)|` を kernel で速く数える。**

  【なぜ要るか】尾のブロックは `p ≤ 400, q ≤ 26`。`APFreeBlockBoundsDigitCount.cntTab`（`List ℕ` の畳み込み）は
    行の長さ `q·Tmax ≈ 5×10⁵`、`p` 回のずらし加算を `q` 段——kernel の `List` 演算では回らない。
  【やり方】行を一つの自然数に詰める（Kronecker 置換）：`packed W l = Σ_i l_i · 2^{W i}`。
    `n` 桁の表は一桁の多項式の `n` 乗だから `packed (cntTab p n) = base^n`、
    `base = Σ_k 2^{W·T p k}`——kernel は `Nat.pow` を GMP で一度に評価する
    （ずらし加算を `p` 回 × `n` 段で書くと、中間の大きな整数が全部 kernel のキャッシュに残り
    `p = 400, q = 26` で 14 GiB を超えた。の実測）。
    係数の取り出しは `(packed >>> (W r)) % 2^W`。これが正しいのは全係数 `< 2^W` のときで、
    係数は `≤ p^n` だから `p^n < 2^W` を検査すればよい。葉ごとのずらしの結果が大きくならないよう、
    先に `2^{W(R+1)}`（`R` は窓の `r`）で切り詰める（`extract_trunc`）。
  【定理】`cfP_le`：`cfP p W n r ≤ |B(p,n,r)|`（`p^n < 2^W` でないときは 0 を返す）。
    `loI_le` の `cf` にそのまま渡せる。sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsDigitCount

namespace APFree.FourTermRecord

open APFree.StepsMaxElement APFree.BlockBounds

/-! ## 1. 行の詰め込み -/

/-- `packed W l = Σ_i l_i · 2^{W i}`。 -/
def packed (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 2 ^ W * packed W l

theorem packed_addL (W : ℕ) : ∀ x y : List ℕ, packed W (addL x y) = packed W x + packed W y := by
  intro x
  induction x with
  | nil => intro y; simp [packed]
  | cons a x ih =>
      intro y
      cases y with
      | nil => simp [packed]
      | cons b y => simp only [addL, packed, ih]; ring

theorem packed_shR (W : ℕ) : ∀ (t : ℕ) (l : List ℕ), packed W (shR t l) = 2 ^ (W * t) * packed W l := by
  intro t
  induction t with
  | zero => intro l; simp [shR]
  | succ t ih =>
      intro l
      simp only [shR, packed, ih]
      rw [Nat.mul_succ, pow_add]
      ring

theorem packed_foldr (W : ℕ) : ∀ L : List (List ℕ),
    packed W (L.foldr addL []) = (L.map (packed W)).sum := by
  intro L
  induction L with
  | nil => simp [packed]
  | cons l L ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, packed_addL, ih]

theorem packed_nextRow (p W : ℕ) (row : List ℕ) :
    packed W (nextRow p row) = ∑ k ∈ Finset.range p, 2 ^ (W * T p k) * packed W row := by
  rw [nextRow, packed_foldr, List.map_map, ← sum_range_list]
  congr 1
  refine List.map_congr_left ?_
  intro k _
  simp [packed_shR]

/-! ## 2. kernel 向けの計算：`packed (cntTab p n) = base^n` -/

/-- `base p W = Σ_{k<p} 2^{W·T p k}`（一桁の多項式を詰めたもの）。 -/
def base (p W : ℕ) : ℕ := ((List.range p).map fun k => 2 ^ (W * T p k)).sum

theorem base_eq (p W : ℕ) : base p W = ∑ k ∈ Finset.range p, 2 ^ (W * T p k) := by
  rw [base, sum_range_list]

/-- **`n` 桁の表を詰めたものは `base^n`**（Kronecker 置換は整数として厳密。桁あふれの条件は
    取り出しのときにだけ要る）。kernel は `Nat.pow` を GMP で一度に評価する。 -/
theorem packed_cntTab (p W : ℕ) : ∀ n, packed W (cntTab p n) = base p W ^ n := by
  intro n
  induction n with
  | zero => simp [cntTab, packed]
  | succ n ih =>
      rw [cntTab, packed_nextRow, ih, ← Finset.sum_mul, ← base_eq, pow_succ]
      ring

/-! ## 3. 係数の上界と取り出し -/

theorem cntTab_le (p : ℕ) : ∀ n r, (cntTab p n).getD r 0 ≤ p ^ n := by
  intro n
  induction n with
  | zero =>
      intro r
      cases r with
      | zero => simp [cntTab, List.getD]
      | succ r => simp [cntTab, List.getD]
  | succ n ih =>
      intro r
      rw [cntTab, getD_nextRow]
      calc ∑ k ∈ Finset.range p, (if T p k ≤ r then (cntTab p n).getD (r - T p k) 0 else 0)
          ≤ ∑ _k ∈ Finset.range p, p ^ n := by
            refine Finset.sum_le_sum ?_
            intro k _
            split_ifs
            · exact ih _
            · exact Nat.zero_le _
        _ = p ^ (n + 1) := by simp [Finset.sum_const]; ring

theorem extract (W : ℕ) : ∀ (l : List ℕ), (∀ r, l.getD r 0 < 2 ^ W) →
    ∀ r, (packed W l >>> (W * r)) % 2 ^ W = l.getD r 0 := by
  intro l
  induction l with
  | nil => intro _ r; simp [packed, List.getD]
  | cons a l ih =>
      intro hlt r
      have ha : a < 2 ^ W := by simpa [List.getD] using hlt 0
      have hrest : ∀ r, l.getD r 0 < 2 ^ W := fun r => by simpa [List.getD] using hlt (r + 1)
      have hpos : 0 < 2 ^ W := by positivity
      cases r with
      | zero =>
          simp only [packed, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      | succ r =>
          rw [Nat.shiftRight_eq_div_pow, List.getD_cons_succ, ← ih hrest r,
            Nat.shiftRight_eq_div_pow]
          have e : 2 ^ (W * (r + 1)) = 2 ^ W * 2 ^ (W * r) := by
            rw [Nat.mul_succ, pow_add]; ring
          rw [e, ← Nat.div_div_eq_div_mul]
          congr 2
          simp only [packed]
          rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, zero_add]

/-- 先に `2^A` で切り詰めても、`B + W ≤ A` なら取り出す `W` ビットは変わらない。
    （葉ごとのずらしの結果が小さくなり、kernel のキャッシュが膨らまない。） -/
theorem extract_trunc (x A B W : ℕ) (h : B + W ≤ A) :
    ((x % 2 ^ A) >>> B) % 2 ^ W = (x >>> B) % 2 ^ W := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  obtain ⟨C, rfl⟩ : ∃ C, A = B + (W + C) := ⟨A - B - W, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_right W C))]

/-- 切り詰めつきの冪 `b^n % M`（各段で `M` で割った余りを取る。中間の整数が `M` を超えない。
    kernel の `Nat.pow` は結果が大きすぎると評価を拒むので、掛け算で書く）。 -/
def pwm (b M : ℕ) : ℕ → ℕ
  | 0 => 1 % M
  | n + 1 => (b * pwm b M n) % M

theorem pwm_eq (b M : ℕ) : ∀ n, pwm b M n = b ^ n % M := by
  intro n
  induction n with
  | zero => simp [pwm]
  | succ n ih =>
      rw [pwm, ih, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ, mul_comm]

/-- **個数（下界としては上界も要らない）**：`p^n < 2^W` かつ `r ≤ R` なら
    `base^n` を `2^{W(R+1)}` で切り詰めたものから取り出した係数、さもなくば 0。
    （`2^{W(R+1)}` は `1 <<< _` で作る：kernel の `Nat.pow` は結果 2^24 ビット超を拒む。実測。） -/
def cfP (p W R : ℕ) (n r : ℕ) : ℕ :=
  if p ^ n < 2 ^ W ∧ r ≤ R then (pwm (base p W) (1 <<< (W * (R + 1))) n >>> (W * r)) % 2 ^ W else 0

theorem cfP_le (p W R : ℕ) (hp : 1 ≤ p) : ∀ n r, cfP p W R n r ≤ (BlkF p n r).card := by
  intro n r
  unfold cfP
  split_ifs with h
  · have hBW : W * r + W ≤ W * (R + 1) := by
      rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.mul_le_mul_left W h.2) W
    rw [pwm_eq, Nat.one_shiftLeft, extract_trunc _ _ _ _ hBW, ← packed_cntTab,
      extract W (cntTab p n) (fun r => lt_of_le_of_lt (cntTab_le p n r) h.1) r,
      cntTab_card p hp n r]
  · exact Nat.zero_le _

/-! ## 4. 窓ごとの下界（`APFreeBlockBoundsMixedDepth.totLoD` の `cfP` 版） -/

/-- 窓 `((p, n, r, a), W, d)`：詰め込み幅 `W`、展開の深さ `d`。個数は `cfP p W r`（切り詰めは `r`）。 -/
def totLoP (SC : ℕ) : List ((ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ) → ℕ
  | [] => 0
  | ((p, n, r, a), W, d) :: ws => loI p SC (cfP p W r) d a n r + totLoP SC ws

theorem totLoP_le (SC : ℕ) (hSC : 0 < SC) :
    ∀ ws : List ((ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ),
      (∀ w ∈ ws, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2) →
      ((totLoP SC ws : ℕ) : ℚ) / SC ≤ sumWin (ws.map Prod.fst) := by
  intro ws
  induction ws with
  | nil => intro _; simp [totLoP, sumWin]
  | cons w ws ih =>
      intro h
      obtain ⟨⟨p, n, r, a⟩, W, d⟩ := w
      have hw := h (((p, n, r, a), W, d)) (by simp)
      have hrest : ∀ w ∈ ws, 1 ≤ w.1.1 ∧ 0 < w.1.2.2.2 := fun w hw => h w (by simp [hw])
      have h1 : ((loI p SC (cfP p W r) d a n r : ℕ) : ℚ) / SC
          ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) :=
        loI_le p SC hSC hw.1 (cfP p W r) (cfP_le p W r hw.1) d a n r hw.2
      have h2 := ih hrest
      simp only [totLoP, List.map_cons, sumWin]
      rw [Nat.cast_add, add_div]
      exact add_le_add h1 h2

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.cfP_le
#print axioms APFree.FourTermRecord.totLoP_le
#print axioms APFree.FourTermRecord.pwm_eq
