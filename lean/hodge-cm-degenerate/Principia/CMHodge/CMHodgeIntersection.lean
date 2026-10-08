/-
  CM アーベル多様体 `A = C^9 / Φ_S(O_K)`（`K = Q(ζ_19)`、`S` は退化かつ原始的な CM 型）の
  上の「非有理特異点を持つ因子」の探索で、**交点数の議論が最後に落ちる有限の部分**を置く。

  幾何については何も主張していない。交点数の正値性・有効性・Grothendieck–Lefschetz・
  随伴イデアル・Serre 双対・Koszul 分解・Mumford の消滅は、ここには入っていない。
  入っているのは、それらを使った議論の骨が落ちる次の四つだけである。

  (1) 余次元 3（`c = 3`）の挟み撃ち：`m p k ≤ P`（k = 0,1,2）・`P ≤ Σ c k p k`・
      `1 ≤ c k`・`Σ c k ≤ m`・`0 < p k`・`0 < m` なら **すべて等号**
      （`m p k = P` かつ `Σ c k = m`）。等号が `E_k = 0` を与える段の核。
  (2) 余次元 2（`c = 2`）の重みつき版：`P = Σ b k p k`（`0 ≤ b k`）・`m p k ≤ P`・
      `Σ b k ≤ m` なら `Σ b k = m` かつ「`b k ≠ 0` なら `m p k = P`」。
      さらに両方の `b k` が正なら `m p 0 = m p 1 = P`。
  (3) 許される重み `b` の勘定（`ℕ`）：Koszul の三段から来る `b` の集合の中で
      `b 0 + b 1 = m` を満たすものは、両成分が `1` 以上のものだけ。
  (4) 実符号の場所勘定：`ey j > 0`（全 j）、`0 ≤ ey j - m * e1 j` が 8 個以上の場所で、
      `0 ≤ ey j - m * e2 j` が 8 個以上の場所で成り立ち、`0 ≤ b1, b2`、`b1 + b2 ≤ m` なら
      **`ey j - b1 e1 j - b2 e2 j < 0` となる場所は 2 個以下**。
      欠損の側が要求する「6 個以上」とは両立しない。
-/
import Mathlib

namespace CMHodge

open Finset

/-! ## 1. 余次元 3 の挟み撃ち（等号の連鎖） -/

/-- `c = 3` の等号の連鎖：`m p k ≤ P ≤ Σ c k p k ≤ (Σ c k) M ≤ m M` が潰れる段。
`max` を使わず、恒等式 `Σ c k (P - m p k) = (Σ c k) P - m Σ c k p k` で書いてある。 -/
theorem squeeze_three (p c : Fin 3 → ℝ) (m P : ℝ)
    (hp : ∀ k, 0 < p k) (hc : ∀ k, 1 ≤ c k) (hm : 0 < m)
    (hmult : ∀ k, m * p k ≤ P)
    (hdef : P ≤ c 0 * p 0 + c 1 * p 1 + c 2 * p 2)
    (hsum : c 0 + c 1 + c 2 ≤ m) :
    (m * p 0 = P ∧ m * p 1 = P ∧ m * p 2 = P) ∧ c 0 + c 1 + c 2 = m := by
  have hP : 0 < P := lt_of_lt_of_le (mul_pos hm (hp 0)) (hmult 0)
  -- `(Σ c k) P ≤ m P`
  have h1 : (c 0 + c 1 + c 2) * P ≤ m * P := mul_le_mul_of_nonneg_right hsum hP.le
  -- `m P ≤ m (Σ c k p k)`
  have h2 : m * P ≤ m * (c 0 * p 0 + c 1 * p 1 + c 2 * p 2) :=
    mul_le_mul_of_nonneg_left hdef hm.le
  -- 各項は非負
  have n : ∀ k, 0 ≤ c k * (P - m * p k) := by
    intro k
    exact mul_nonneg (le_trans zero_le_one (hc k)) (by linarith [hmult k])
  -- 和は非正
  have hsum0 : c 0 * (P - m * p 0) + c 1 * (P - m * p 1) + c 2 * (P - m * p 2) ≤ 0 := by
    nlinarith [h1, h2]
  have e0 : c 0 * (P - m * p 0) = 0 := by linarith [n 0, n 1, n 2]
  have e1 : c 1 * (P - m * p 1) = 0 := by linarith [n 0, n 1, n 2]
  have e2 : c 2 * (P - m * p 2) = 0 := by linarith [n 0, n 1, n 2]
  have z0 : m * p 0 = P := by
    have := (mul_eq_zero.1 e0).resolve_left (by linarith [hc 0]); linarith
  have z1 : m * p 1 = P := by
    have := (mul_eq_zero.1 e1).resolve_left (by linarith [hc 1]); linarith
  have z2 : m * p 2 = P := by
    have := (mul_eq_zero.1 e2).resolve_left (by linarith [hc 2]); linarith
  refine ⟨⟨z0, z1, z2⟩, ?_⟩
  -- `P ≤ Σ c k p k = (Σ c k) P / m` と `Σ c k ≤ m` から等号
  have q0 : m * (c 0 * p 0) = c 0 * P := by rw [← z0]; ring
  have q1 : m * (c 1 * p 1) = c 1 * P := by rw [← z1]; ring
  have q2 : m * (c 2 * p 2) = c 2 * P := by rw [← z2]; ring
  have : m * P ≤ (c 0 + c 1 + c 2) * P := by nlinarith [h2, q0, q1, q2]
  have hge : m ≤ c 0 + c 1 + c 2 := le_of_mul_le_mul_right (by linarith) hP
  linarith

/-- `c = 3` の帰結：`P - m p k = 0`（`V_k` 上の有効因子 `E_k` が消える段）。 -/
theorem squeeze_three_defect_zero (p c : Fin 3 → ℝ) (m P : ℝ)
    (hp : ∀ k, 0 < p k) (hc : ∀ k, 1 ≤ c k) (hm : 0 < m)
    (hmult : ∀ k, m * p k ≤ P)
    (hdef : P ≤ c 0 * p 0 + c 1 * p 1 + c 2 * p 2)
    (hsum : c 0 + c 1 + c 2 ≤ m) :
    P - m * p 0 = 0 ∧ P - m * p 1 = 0 ∧ P - m * p 2 = 0 := by
  obtain ⟨⟨z0, z1, z2⟩, _⟩ := squeeze_three p c m P hp hc hm hmult hdef hsum
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## 2. 余次元 2 の重みつき挟み撃ち -/

/-- `c = 2`：欠損が `y = b 0 y_0 + b 1 y_1`（`0 ≤ b k`、`Σ b k ≤ m`）を強制したあと、
重複度 `m p k ≤ P` と合わせると `Σ b k = m` になり、`b k ≠ 0` の側で等号になる。 -/
theorem squeeze_two (p b : Fin 2 → ℝ) (m P : ℝ)
    (hp : ∀ k, 0 < p k) (hb : ∀ k, 0 ≤ b k) (hm : 0 < m)
    (hP : P = b 0 * p 0 + b 1 * p 1)
    (hmult : ∀ k, m * p k ≤ P)
    (hsum : b 0 + b 1 ≤ m) :
    b 0 + b 1 = m ∧ (b 0 ≠ 0 → m * p 0 = P) ∧ (b 1 ≠ 0 → m * p 1 = P) := by
  rcases le_total (p 0) (p 1) with h | h
  · -- 最大は `p 1`
    have key : P ≤ (b 0 + b 1) * p 1 := by nlinarith [hb 0, hb 1]
    have h2 : (b 0 + b 1) * p 1 ≤ m * p 1 := mul_le_mul_of_nonneg_right hsum (hp 1).le
    have h3 : m * p 1 ≤ P := hmult 1
    have hP1 : P = m * p 1 := by linarith
    have hs : (b 0 + b 1) * p 1 = m * p 1 := by linarith
    have hbsum : b 0 + b 1 = m := by
      have := mul_right_cancel₀ (ne_of_gt (hp 1)) hs
      exact this
    refine ⟨hbsum, ?_, fun _ => hP1.symm⟩
    intro hk
    have hb0 : 0 < b 0 := lt_of_le_of_ne (hb 0) (Ne.symm hk)
    have e : b 0 * p 0 = b 0 * p 1 := by nlinarith
    have e' : p 0 = p 1 := mul_left_cancel₀ (ne_of_gt hb0) e
    rw [e']; exact hP1.symm
  · -- 最大は `p 0`
    have key : P ≤ (b 0 + b 1) * p 0 := by nlinarith [hb 0, hb 1]
    have h2 : (b 0 + b 1) * p 0 ≤ m * p 0 := mul_le_mul_of_nonneg_right hsum (hp 0).le
    have h3 : m * p 0 ≤ P := hmult 0
    have hP0 : P = m * p 0 := by linarith
    have hs : (b 0 + b 1) * p 0 = m * p 0 := by linarith
    have hbsum : b 0 + b 1 = m := mul_right_cancel₀ (ne_of_gt (hp 0)) hs
    refine ⟨hbsum, fun _ => hP0.symm, ?_⟩
    intro hk
    have hb1 : 0 < b 1 := lt_of_le_of_ne (hb 1) (Ne.symm hk)
    have e : b 1 * p 1 = b 1 * p 0 := by nlinarith
    have e' : p 1 = p 0 := mul_left_cancel₀ (ne_of_gt hb1) e
    rw [e']; exact hP0.symm

/-- `c = 2` で両方の重みが正のとき：`m p 0 = m p 1 = P`（両側で `E_k = 0`）。 -/
theorem squeeze_two_both (p b : Fin 2 → ℝ) (m P : ℝ)
    (hp : ∀ k, 0 < p k) (hb : ∀ k, 0 < b k) (hm : 0 < m)
    (hP : P = b 0 * p 0 + b 1 * p 1)
    (hmult : ∀ k, m * p k ≤ P)
    (hsum : b 0 + b 1 ≤ m) :
    m * p 0 = P ∧ m * p 1 = P ∧ b 0 + b 1 = m := by
  obtain ⟨h1, h20, h21⟩ := squeeze_two p b m P hp (fun k => (hb k).le) hm hP hmult hsum
  exact ⟨h20 (ne_of_gt (hb 0)), h21 (ne_of_gt (hb 1)), h1⟩

/-- `Σ b k < m` は起きない（`P ≤ (Σ b k) M < m M ≤ P`）。 -/
theorem weights_not_deficient (p b : Fin 2 → ℝ) (m P : ℝ)
    (hp : ∀ k, 0 < p k) (hb : ∀ k, 0 ≤ b k) (hm : 0 < m)
    (hP : P = b 0 * p 0 + b 1 * p 1)
    (hmult : ∀ k, m * p k ≤ P) :
    ¬ (b 0 + b 1 < m) := by
  intro hlt
  have := (squeeze_two p b m P hp hb hm hP hmult hlt.le).1
  linarith

/-! ## 3. 許される重みの勘定（`ℕ`） -/

/-- Koszul の三段（`p = 0,1,2`）から来る重み `b` の集合。`hc` は `1 ≤ c k`・`Σ c k ≤ m`
から来る制約を、`b = c`・`b = c - e_k`・`b = c - (1,1)` の三通りに展開したもの。 -/
def AllowedWeight (m b0 b1 : ℕ) : Prop :=
  (1 ≤ b0 ∧ 1 ≤ b1 ∧ b0 + b1 ≤ m) ∨
  (1 ≤ b1 ∧ b0 + b1 + 1 ≤ m) ∨
  (1 ≤ b0 ∧ b0 + b1 + 1 ≤ m) ∨
  (b0 + b1 + 2 ≤ m)

/-- 重みの総和が `m` に達するのは、両成分が正のときだけ。
とくに `b = (m, 0)`（`y = m y_0`、もう一方の偏極が効かない場合）は起きない。 -/
theorem allowed_top_pos (m b0 b1 : ℕ) (h : AllowedWeight m b0 b1) (htop : b0 + b1 = m) :
    1 ≤ b0 ∧ 1 ≤ b1 := by
  rcases h with ⟨h1, h2, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | h2
  · exact ⟨h1, h2⟩
  · omega
  · omega
  · omega

/-- `b = (m, 0)` は許されない。 -/
theorem allowed_not_extreme (m : ℕ) (hm : 1 ≤ m) : ¬ AllowedWeight m m 0 := by
  intro h
  have := (allowed_top_pos m m 0 h (by omega)).2
  omega

/-- Koszul の段の次数勘定：`|c| = 2 + d` で `d ≤ m - 2` なら `|c| ≤ m`。 -/
theorem koszul_degree (m d c0 c1 : ℕ) (hd : d + 2 ≤ m) (hc : c0 + c1 = 2 + d) :
    c0 + c1 ≤ m := by omega

/-! ## 4. 実符号の場所勘定 -/

/-- **本稿の鍵**。`ey` は豊富（全成分正）、`e1`・`e2` も豊富。
`0 ≤ ey j - m * e1 j` が 8 個以上の場所で、`0 ≤ ey j - m * e2 j` が 8 個以上の場所で
成り立つとき（＝重複度の条件が `L_{y - m y_k}|_{D_j}` の有効性から強制するもの）、
`0 ≤ b1, b2`、`b1 + b2 ≤ m` なる任意の重みについて
`ey j - b1 * e1 j - b2 * e2 j < 0` となる場所は **2 個以下**である。 -/
theorem places_nonneg_of_mult
    (e1 e2 ey : Fin 9 → ℝ) (m b1 b2 : ℝ)
    (h1 : ∀ j, 0 < e1 j) (h2 : ∀ j, 0 < e2 j)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hsum : b1 + b2 ≤ m)
    (G1 G2 : Finset (Fin 9))
    (hG1 : ∀ j ∈ G1, 0 ≤ ey j - m * e1 j)
    (hG2 : ∀ j ∈ G2, 0 ≤ ey j - m * e2 j)
    (c1 : 8 ≤ G1.card) (c2 : 8 ≤ G2.card) :
    (univ.filter (fun j : Fin 9 => ey j - b1 * e1 j - b2 * e2 j < 0)).card ≤ 2 := by
  -- `G1 ∩ G2` は 7 個以上
  have hu : (G1 ∪ G2).card ≤ 9 := by
    have := Finset.card_le_univ (G1 ∪ G2)
    simpa using this
  have hui : (G1 ∪ G2).card + (G1 ∩ G2).card = G1.card + G2.card :=
    Finset.card_union_add_card_inter G1 G2
  have hinter : 7 ≤ (G1 ∩ G2).card := by omega
  -- `G1 ∩ G2` の上では非負
  have key : ∀ j ∈ G1 ∩ G2, 0 ≤ ey j - b1 * e1 j - b2 * e2 j := by
    intro j hj
    have hj1 : j ∈ G1 := (Finset.mem_inter.1 hj).1
    have hj2 : j ∈ G2 := (Finset.mem_inter.1 hj).2
    have a1 := hG1 j hj1
    have a2 := hG2 j hj2
    rcases le_total (e1 j) (e2 j) with h | h
    · -- `b1 e1 + b2 e2 ≤ (b1+b2) e2 ≤ m e2 ≤ ey`
      have t1 : b1 * e1 j ≤ b1 * e2 j := mul_le_mul_of_nonneg_left h hb1
      have t2 : (b1 + b2) * e2 j ≤ m * e2 j :=
        mul_le_mul_of_nonneg_right hsum (h2 j).le
      nlinarith
    · have t1 : b2 * e2 j ≤ b2 * e1 j := mul_le_mul_of_nonneg_left h hb2
      have t2 : (b1 + b2) * e1 j ≤ m * e1 j :=
        mul_le_mul_of_nonneg_right hsum (h1 j).le
      nlinarith
  -- 負の場所は `G1 ∩ G2` の補集合に入る
  have hsub : (univ.filter (fun j : Fin 9 => ey j - b1 * e1 j - b2 * e2 j < 0)) ⊆ (G1 ∩ G2)ᶜ := by
    intro j hj
    have hneg : ey j - b1 * e1 j - b2 * e2 j < 0 := (Finset.mem_filter.1 hj).2
    rw [Finset.mem_compl]
    intro hmem
    exact absurd (key j hmem) (by linarith)
  have hcc : ((G1 ∩ G2)ᶜ).card = 9 - (G1 ∩ G2).card := by
    have := Finset.card_compl (G1 ∩ G2)
    simpa using this
  have := Finset.card_le_card hsub
  omega

/-- 欠損の側は「6 個以上の場所で負」を要求するので、重複度と両立しない。 -/
theorem defect_incompatible_with_mult
    (e1 e2 ey : Fin 9 → ℝ) (m b1 b2 : ℝ)
    (h1 : ∀ j, 0 < e1 j) (h2 : ∀ j, 0 < e2 j)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hsum : b1 + b2 ≤ m)
    (G1 G2 : Finset (Fin 9))
    (hG1 : ∀ j ∈ G1, 0 ≤ ey j - m * e1 j)
    (hG2 : ∀ j ∈ G2, 0 ≤ ey j - m * e2 j)
    (c1 : 8 ≤ G1.card) (c2 : 8 ≤ G2.card)
    (hdef : 6 ≤ (univ.filter (fun j : Fin 9 => ey j - b1 * e1 j - b2 * e2 j < 0)).card) :
    False := by
  have := places_nonneg_of_mult e1 e2 ey m b1 b2 h1 h2 hb1 hb2 hsum G1 G2 hG1 hG2 c1 c2
  omega

/-- 場所勘定の下限は 7 が最良（`8 + 8 - 9 = 7`）で、`2` という上界も最良である
ことの、勘定だけの確認：8 個と 8 個の共通部分が 7 個になる配置は `Fin 9` にある。 -/
theorem inter_seven_attained :
    ∃ G1 G2 : Finset (Fin 9), 8 ≤ G1.card ∧ 8 ≤ G2.card ∧ (G1 ∩ G2).card = 7 := by
  refine ⟨univ.erase 0, univ.erase 1, ?_, ?_, ?_⟩ <;> decide

#print axioms squeeze_three
#print axioms squeeze_three_defect_zero
#print axioms squeeze_two
#print axioms squeeze_two_both
#print axioms weights_not_deficient
#print axioms allowed_top_pos
#print axioms allowed_not_extreme
#print axioms koszul_degree
#print axioms places_nonneg_of_mult
#print axioms defect_incompatible_with_mult
#print axioms inter_seven_attained

end CMHodge
