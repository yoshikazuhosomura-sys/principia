/-
  エルデシュ問題 #169（3-AP を含まない集合の逆数和）。

   で紙に書いた「窓分離定理」の有限版を機械検査する。

  【定理W（窓分離）】
    各 i について A i ⊆ [l i, r i] が 3-AP-free とする。
    すべての三つ組 (i,j,k) で ¬(i = j ∧ j = k) なるものについて
        [l i + l k, r i + r k] ∩ [2 (l j), 2 (r j)] = ∅
    ならば ⋃ i, A i も 3-AP-free。

  【要点】条件は **囲み区間しか見ない**。中身 A i を見ないので、
    A i 自身が内部で分離された合併であっても外側の条件は変わらない。
    したがって **入れ子は無条件に自由**（系 nest）。
    これが Wroblewski 1984 (Math. Comp. 43, 261-262) の Lemma 2 の一般形であり、
    記録 f(3) ≥ 3.00849 を作っている論法である。

  【倍加税】三つ組 (2,1,1) は a > 2z を強制する（lemma doubling_tax）。
    すなわち有限ブロックを継ぐたびに尺度を必ず 2 倍以上使う。

  【Wroblewski の平行移動】z = t = u のとき彼の三つの移動量
    (2u+1, 6u+3, 8u+4) が (W) を満たすことを検査する（lemma wroblewski_windows）。
-/
import Mathlib.Tactic

namespace APFree.WindowSeparation

/-- 集合 S が 3-AP を含まない（自明な x = y を除く）。 -/
def IsThreeAPFree (S : Set ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = y

/-- 窓の配置：各添字に閉区間 [l i, r i] を割り当てる。 -/
structure Windows (ι : Type*) where
  l : ι → ℤ
  r : ι → ℤ

/-- 窓分離条件 (W)：全ての (i,j,k)（i = j = k は除く）で、
    区間の和 [l i + l k, r i + r k] が 2 倍区間 [2 l j, 2 r j] と交わらない。 -/
def Separated {ι : Type*} (W : Windows ι) : Prop :=
  ∀ i j k : ι, ¬(i = j ∧ j = k) →
    (2 * W.r j < W.l i + W.l k ∨ W.r i + W.r k < 2 * W.l j)

/-- **定理W（窓分離定理）**。 -/
theorem apfree_iUnion_of_separated {ι : Type*}
    (W : Windows ι) (A : ι → Set ℤ)
    (hbox : ∀ i, ∀ x ∈ A i, W.l i ≤ x ∧ x ≤ W.r i)
    (hfree : ∀ i, IsThreeAPFree (A i))
    (hsep : Separated W) :
    IsThreeAPFree (⋃ i, A i) := by
  rintro x hx y hy z hz hxyz
  simp only [Set.mem_iUnion] at hx hy hz
  obtain ⟨i, hxi⟩ := hx
  obtain ⟨j, hyj⟩ := hy
  obtain ⟨k, hzk⟩ := hz
  by_cases h : i = j ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    exact hfree i x hxi y hyj z hzk hxyz
  · exfalso
    obtain ⟨hxl, hxr⟩ := hbox i x hxi
    obtain ⟨hyl, hyr⟩ := hbox j y hyj
    obtain ⟨hzl, hzr⟩ := hbox k z hzk
    rcases hsep i j k h with hc | hc
    · -- 2 * r j < l i + l k ≤ x + z = 2 y ≤ 2 * r j
      omega
    · -- x + z ≤ r i + r k < 2 * l j ≤ 2 y = x + z
      omega

/-- **系（入れ子は自由）**。外側の窓 [L m, R m] に、内側で再び窓分離された合併を入れてよい。
    条件は囲み区間しか見ないので、内側の構造は外側の条件に一切影響しない。 -/
theorem apfree_nested {ι κ : Type*}
    (W : Windows ι) (V : ι → Windows κ) (A : ι → κ → Set ℤ)
    -- 内側：各 i について、A i · は窓 V i で分離されている
    (hinner_box : ∀ i c, ∀ x ∈ A i c, (V i).l c ≤ x ∧ x ≤ (V i).r c)
    (hinner_free : ∀ i c, IsThreeAPFree (A i c))
    (hinner_sep : ∀ i, Separated (V i))
    -- 外側：内側の合併は窓 W に収まり、W は分離されている
    (houter_box : ∀ i c, W.l i ≤ (V i).l c ∧ (V i).r c ≤ W.r i)
    (houter_sep : Separated W) :
    IsThreeAPFree (⋃ i, ⋃ c, A i c) := by
  have hfree : ∀ i, IsThreeAPFree (⋃ c, A i c) := fun i =>
    apfree_iUnion_of_separated (V i) (A i) (hinner_box i) (hinner_free i) (hinner_sep i)
  have hbox : ∀ i, ∀ x ∈ (⋃ c, A i c), W.l i ≤ x ∧ x ≤ W.r i := by
    intro i x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨c, hc⟩ := hx
    obtain ⟨h1, h2⟩ := hinner_box i c x hc
    obtain ⟨h3, h4⟩ := houter_box i c
    exact ⟨le_trans h3 h1, le_trans h2 h4⟩
  have := apfree_iUnion_of_separated W (fun i => ⋃ c, A i c) hbox hfree houter_sep
  simpa using this

/-- **倍加税**。頭 [0, z] に幅 t のブロックを [a, a+t] として継ぐとき、
    (W) の三つ組（新ブロック, 頭, 頭）は a > 2z を強制する。
    すなわち各段は尺度を必ず 2 倍以上使う。 -/
theorem doubling_tax (z t a : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (W : Windows (Fin 2))
    (hW0l : W.l 0 = 0) (hW0r : W.r 0 = z)
    (hW1l : W.l 1 = a) (hW1r : W.r 1 = a + t)
    (hsep : Separated W) : 2 * z < a := by
  have h := hsep 1 0 0 (by simp)
  rw [hW0l, hW0r, hW1l, hW1r] at h
  omega

/-- 頭が [0,z]、幅 t のブロックを一つ継ぐときの最小の平行移動量は
    max (2z) (z+t) + 1、すなわち a > 2z かつ a > z + t。 -/
theorem one_block_bound (z t a : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (W : Windows (Fin 2))
    (hW0l : W.l 0 = 0) (hW0r : W.r 0 = z)
    (hW1l : W.l 1 = a) (hW1r : W.r 1 = a + t)
    (hsep : Separated W) : 2 * z < a ∧ z + t < a := by
  refine ⟨doubling_tax z t a hz ht ha W hW0l hW0r hW1l hW1r hsep, ?_⟩
  have h := hsep 0 1 1 (by simp)
  rw [hW0l, hW0r, hW1l, hW1r] at h
  omega

/-- Wroblewski 1984 の (Z,T) 演算の窓（z = t = u の場合）：
    [0,u], [2u+1, 3u+1], [6u+3, 7u+3], [8u+4, 9u+4]。 -/
def wrobWindows (u : ℤ) : Windows (Fin 4) where
  l := fun i => match i with
    | 0 => 0 | 1 => 2*u+1 | 2 => 6*u+3 | 3 => 8*u+4
  r := fun i => match i with
    | 0 => u | 1 => 3*u+1 | 2 => 7*u+3 | 3 => 9*u+4

/-- **Wroblewski の平行移動は (W) を満たす**（u ≥ 0）。
    窓番号 {0, 1, 3, 4}（4 元の最小 Salem–Spencer 集合）を刻み 2u+1 で置いたもの。 -/
theorem wroblewski_windows (u : ℤ) (hu : 0 ≤ u) : Separated (wrobWindows u) := by
  intro i j k h
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [wrobWindows] at h ⊢ <;>
    first
      | omega
      | simp at h

/-- **系**：Wroblewski の配置に 3-AP-free なブロックを入れると、合併も 3-AP-free。
    これが Lemma 2（記録 f(3) ≥ 3.00849 を支える補題）の内容である。 -/
theorem wroblewski_lemma2 (u : ℤ) (hu : 0 ≤ u) (A : Fin 4 → Set ℤ)
    (hbox : ∀ i, ∀ x ∈ A i, (wrobWindows u).l i ≤ x ∧ x ≤ (wrobWindows u).r i)
    (hfree : ∀ i, IsThreeAPFree (A i)) :
    IsThreeAPFree (⋃ i, A i) :=
  apfree_iUnion_of_separated (wrobWindows u) A hbox hfree (wroblewski_windows u hu)

/-- 対照：窓番号を {0,1,2}（3-AP を含む）にすると (W) は破れる。
    刻み 2u+1 で三つ並べた [0,u], [2u+1,3u+1], [4u+2,5u+2] は分離されない。 -/
def badWindows (u : ℤ) : Windows (Fin 3) where
  l := fun i => match i with
    | 0 => 0 | 1 => 2*u+1 | 2 => 4*u+2
  r := fun i => match i with
    | 0 => u | 1 => 3*u+1 | 2 => 5*u+2

theorem badWindows_not_separated (u : ℤ) (hu : 0 < u) : ¬ Separated (badWindows u) := by
  intro h
  have := h 0 1 2 (by simp)
  simp only [badWindows] at this
  omega

end APFree.WindowSeparation

/-! ### 公理の確認 -/

#print axioms APFree.WindowSeparation.apfree_iUnion_of_separated
#print axioms APFree.WindowSeparation.apfree_nested
#print axioms APFree.WindowSeparation.doubling_tax
#print axioms APFree.WindowSeparation.wroblewski_windows
#print axioms APFree.WindowSeparation.wroblewski_lemma2
#print axioms APFree.WindowSeparation.badWindows_not_separated
