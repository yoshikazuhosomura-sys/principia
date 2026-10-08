/-

  エルデシュ問題 #169。**M = 4 と M = 5 の段の窓分離 (W) を一般補題にする。**

  【なぜ要るか（・）】
     (A) は τ = t/z の連続極限で、最左配置が M ≤ 5 まで一次式になることを見た：
        α = [τ+1, 4τ+2, 10τ+4, 12τ+4, 26τ+8]。
    ところが `sep_M3`（`APFreeWindowSeparationM3`）は**整数の式**（m+z+1, 3m+2t+z+3, 3m+4t+z+4）であって、
    連続極限の式そのままでは Lean に入らない。加法定数を決める必要がある。
    APFreeWindowSeparationM45 で、整数の厳密演算による最左配置を (z,t) の格子上で当てはめたところ、
    **m = max z t として係数も定数も整数で確定した**（24 点で外れ 0）：

        a₁ = m + z + 1, a₂ = 4m + 2z + 3, a₃ = 10m + 4z + 7,
        a₄ = 12m + 4z + 8, a₅ = 26m + 8z + 17

    （t の係数はすべて 0 である。τ ≥ 1 側では m = t なので t は m に吸収される。
      τ ≤ 1 側の最左配置は a₃ 以降が一次にならない—— (A) の観察と一致する。
      しかし**下の定理は m ≥ max z t を仮定するだけで、τ の大小を問わない**。）

  【`APFreeWindowSeparationM3` の `sep_M3` との違い】
    `sep_M3` は Wróblewski の配置（a₂ = 3m + 2t + z + 3）で、これは最左ではない
    （a₂ を犠牲にして a₃ を小さくしている。⟹ (C) の O-1）。
    本ファイルの `W4g` / `W5g` は**貪欲な最左**の族である。二つは別の配置族であり、
    どちらも (W) を満たす。⟹ 政策の行動集合は少なくともこの二族を含む。

  【本ファイルの中身】
    (1) W4g / sep_M4_gen / sep_M4 : 0 ≤ z, 0 ≤ t, z ≤ m, t ≤ m だけで (W) が成り立つ
    (2) W5g / sep_M5_gen / sep_M5 : 同じ形の M = 5 版
    (3) step_M4_apfree / step_M5_apfree : その段の合併は 3-AP-free
    (4) nextZ4 / nextZ5 と W4_in_box / W5_in_box（箱に収まる）
    (5) M4_doubling : 倍加税は M = 4 でも効く（最初のブロックは 2z より右）

  sorry 0、native_decide 不使用。
-/
import Mathlib.Tactic
import Principia.APFree.WindowSeparation

namespace APFree.WindowSeparationM45

open APFree.WindowSeparation

set_option maxRecDepth 100000

/-! ## 1. M = 4 の窓（貪欲な最左の族） -/

/-- 頭 [0, z] と四つのブロック窓（幅 t）。刻みは m を通して与える。
    m = max z t が最左の取り方である。 -/
def W4g (z t m : ℤ) : Windows (Fin 5) where
  l := fun i => match i with
    | 0 => 0
    | 1 => m + z + 1
    | 2 => 4*m + 2*z + 3
    | 3 => 10*m + 4*z + 7
    | 4 => 12*m + 4*z + 8
  r := fun i => match i with
    | 0 => z
    | 1 => m + z + 1 + t
    | 2 => 4*m + 2*z + 3 + t
    | 3 => 10*m + 4*z + 7 + t
    | 4 => 12*m + 4*z + 8 + t

/-- **一般形（M = 4）**：0 ≤ z, 0 ≤ t, z ≤ m, t ≤ m ならば (W) が成り立つ。 -/
theorem sep_M4_gen (z t m : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (hzm : z ≤ m) (htm : t ≤ m) :
    Separated (W4g z t m) := by
  intro i j k h
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [W4g] at h ⊢ <;> first | omega | simp at h

/-- 最左の取り方 m = max z t。 -/
def W4 (z t : ℤ) : Windows (Fin 5) := W4g z t (max z t)

/-- **M = 4 の段は (W) を満たす**。前提は 0 ≤ z, 0 ≤ t のみ。 -/
theorem sep_M4 (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) : Separated (W4 z t) :=
  sep_M4_gen z t (max z t) hz ht (le_max_left _ _) (le_max_right _ _)

/-- 第837 の当てはめが与えた式が、窓の左端と一致する。 -/
theorem M4_offsets (z t : ℤ) :
    (W4 z t).l 1 = max z t + z + 1 ∧
    (W4 z t).l 2 = 4*(max z t) + 2*z + 3 ∧
    (W4 z t).l 3 = 10*(max z t) + 4*z + 7 ∧
    (W4 z t).l 4 = 12*(max z t) + 4*z + 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 2. M = 5 の窓 -/

def W5g (z t m : ℤ) : Windows (Fin 6) where
  l := fun i => match i with
    | 0 => 0
    | 1 => m + z + 1
    | 2 => 4*m + 2*z + 3
    | 3 => 10*m + 4*z + 7
    | 4 => 12*m + 4*z + 8
    | 5 => 26*m + 8*z + 17
  r := fun i => match i with
    | 0 => z
    | 1 => m + z + 1 + t
    | 2 => 4*m + 2*z + 3 + t
    | 3 => 10*m + 4*z + 7 + t
    | 4 => 12*m + 4*z + 8 + t
    | 5 => 26*m + 8*z + 17 + t

/-- **一般形（M = 5）**。 -/
theorem sep_M5_gen (z t m : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (hzm : z ≤ m) (htm : t ≤ m) :
    Separated (W5g z t m) := by
  intro i j k h
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [W5g] at h ⊢ <;> first | omega | simp at h

def W5 (z t : ℤ) : Windows (Fin 6) := W5g z t (max z t)

theorem sep_M5 (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) : Separated (W5 z t) :=
  sep_M5_gen z t (max z t) hz ht (le_max_left _ _) (le_max_right _ _)

/-! ## 3. 段の帰結 -/

/-- M = 4 の段：頭と四つのブロックの合併は 3-AP-free。 -/
theorem step_M4_apfree (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (A : Fin 5 → Set ℤ)
    (hbox : ∀ i, ∀ x ∈ A i, (W4 z t).l i ≤ x ∧ x ≤ (W4 z t).r i)
    (hfree : ∀ i, IsThreeAPFree (A i)) : IsThreeAPFree (⋃ i, A i) :=
  apfree_iUnion_of_separated (W4 z t) A hbox hfree (sep_M4 z t hz ht)

/-- M = 5 の段。 -/
theorem step_M5_apfree (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (A : Fin 6 → Set ℤ)
    (hbox : ∀ i, ∀ x ∈ A i, (W5 z t).l i ≤ x ∧ x ≤ (W5 z t).r i)
    (hfree : ∀ i, IsThreeAPFree (A i)) : IsThreeAPFree (⋃ i, A i) :=
  apfree_iUnion_of_separated (W5 z t) A hbox hfree (sep_M5 z t hz ht)

/-- 段の後の頭の最大元（最後の窓の右端）。 -/
def nextZ4 (z t : ℤ) : ℤ := 12*(max z t) + 4*z + 8 + t

def nextZ5 (z t : ℤ) : ℤ := 26*(max z t) + 8*z + 17 + t

/-- M = 4 の段の窓は、すべて次の段の箱 [0, nextZ4 z t] に収まる。 -/
theorem W4_in_box (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) (i : Fin 5) :
    0 ≤ (W4 z t).l i ∧ (W4 z t).r i ≤ nextZ4 z t := by
  have h1 : z ≤ max z t := le_max_left _ _
  have h2 : t ≤ max z t := le_max_right _ _
  fin_cases i <;> simp only [W4, W4g, nextZ4] <;> omega

theorem W5_in_box (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) (i : Fin 6) :
    0 ≤ (W5 z t).l i ∧ (W5 z t).r i ≤ nextZ5 z t := by
  have h1 : z ≤ max z t := le_max_left _ _
  have h2 : t ≤ max z t := le_max_right _ _
  fin_cases i <;> simp only [W5, W5g, nextZ5] <;> omega

/-- 段を継ぐと頭の最大元は必ず増える（倍加税の M = 4 版）。 -/
theorem nextZ4_gt (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) : z < nextZ4 z t := by
  have h1 : z ≤ max z t := le_max_left _ _
  simp only [nextZ4]; omega

/-- 倍加税は M = 4 でも効いている：最初のブロックは 2z より右から始まる。 -/
theorem M4_doubling (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) : 2*z < (W4 z t).l 1 := by
  have h1 : z ≤ max z t := le_max_left _ _
  simp only [W4, W4g]; omega

/-- 尺度の代金（`APFreeWindowSeparationM3.nextZ3_cases` の M = 4 版）。
    t ≤ z なら 12z + 4z + 8 + t = 16z + t + 8、z ≤ t なら 12t + 4z + 8 + t = 13t + 4z + 8。 -/
theorem nextZ4_cases (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) :
    (t ≤ z → nextZ4 z t = 16*z + t + 8) ∧ (z ≤ t → nextZ4 z t = 13*t + 4*z + 8) := by
  constructor <;> intro h <;> simp only [nextZ4] <;> omega

end APFree.WindowSeparationM45

/-! ### 公理の確認 -/

#print axioms APFree.WindowSeparationM45.sep_M4
#print axioms APFree.WindowSeparationM45.sep_M5
#print axioms APFree.WindowSeparationM45.step_M4_apfree
