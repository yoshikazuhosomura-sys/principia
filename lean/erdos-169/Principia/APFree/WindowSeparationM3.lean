/-
  エルデシュ問題 #169。**M = 3 の段の窓分離 (W) を一般補題にする。**

  【なぜ要るか】
    率基準（1 段先読み）の政策は最適ではない。第一手を **2 段先読み**で選ぶだけで
    同じ 110 段・同じ厳密な挟み込みで下界が
        3.0085326723249 → 3.0085334952854 （+8.23e-7）
    に上がる。ところがこの先読み政策は **M = 3 の段を使う**（K=6 で 1 段）。
    APFreeStepsSeparated の一般補題は M = 1（sep_M1）と M = 2 の内側案（sep_M2）しか覆っていない。
    そこで M = 3 を覆う `sep_M3` を立てる。これが無いと先読み政策の値は
    p ≤ 14 主値・p ≤ 26 と同じ検証水準に上げられない。

  【M = 3 の窓（Wróblewski の閉じた式。`外の生成器` の offsets_M3）】
    m = max z t として
        a₁ = m + z + 1, a₂ = 3m + 2t + z + 3, a₃ = 3m + 4t + z + 4
    窓は [0, z], [a₁, a₁+t], [a₂, a₂+t], [a₃, a₃+t]。
    z = t = u に落とすと (2u+1, 6u+3, 8u+4) ＝ APFreeWindowSeparation の `wrobWindows u`
    （4 元の最小 Salem–Spencer 集合 {0,1,3,4} を刻み 2u+1 で置いたもの）。

  【本ファイルの中身】
    (1) W3 / sep_M3 : **0 ≤ z, 0 ≤ t のみ**で (W) が成り立つ（数値条件は要らない）。
        —— M = 2 が 3t < z の一条件を必要としたのと対照的である。
    (2) W3_eq_wrob : z = t = u のとき W3 は APFreeWindowSeparation の wrobWindows と一致する
        （閉じた式が Wróblewski のものであることの機械検査）。
    (3) step_M3_apfree : M = 3 の段で、頭と三つのブロックの合併は 3-AP-free。
    (4) nextZ3 / W3_in_box : 段の後の頭の最大元は 3m + 5t + z + 4 で、
        すべての窓が [0, nextZ3] に収まる（`apfree_nested` の houter_box）。
    (5) sep_M3_gen : m を max z t に固定せず「z ≤ m かつ t ≤ m」だけを仮定しても
        (W) は成り立つ（配置の族としての余裕。max はその最小の取り方である）。

  sorry 0、native_decide 不使用。
-/
import Mathlib.Tactic
import Principia.APFree.WindowSeparation

namespace APFree.WindowSeparationM3

open APFree.WindowSeparation

set_option maxRecDepth 100000

/-! ## 1. M = 3 の窓（一般の m） -/

/-- 頭 [0, z] と三つのブロック窓（幅 t）。刻みは m を通して与える。
    m = max z t が Wróblewski の取り方である。 -/
def W3g (z t m : ℤ) : Windows (Fin 4) where
  l := fun i => match i with
    | 0 => 0
    | 1 => m + z + 1
    | 2 => 3*m + 2*t + z + 3
    | 3 => 3*m + 4*t + z + 4
  r := fun i => match i with
    | 0 => z
    | 1 => m + z + 1 + t
    | 2 => 3*m + 2*t + z + 3 + t
    | 3 => 3*m + 4*t + z + 4 + t

/-- **一般形**：0 ≤ z, 0 ≤ t, z ≤ m, t ≤ m ならば (W) が成り立つ。
    数値条件は「m が z と t の両方以上」だけで、M = 2 の 3t < z のような
    段ごとの条件は要らない。 -/
theorem sep_M3_gen (z t m : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (hzm : z ≤ m) (htm : t ≤ m) :
    Separated (W3g z t m) := by
  intro i j k h
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [W3g] at h ⊢ <;> first | omega | simp at h

/-! ## 2. Wróblewski の取り方 m = max z t -/

/-- Wróblewski の M = 3 の窓（`erdos732b.py` の `offsets_M3` そのもの）。 -/
def W3 (z t : ℤ) : Windows (Fin 4) := W3g z t (max z t)

/-- **M = 3 の段は (W) を満たす**。前提は 0 ≤ z, 0 ≤ t のみ。 -/
theorem sep_M3 (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) : Separated (W3 z t) :=
  sep_M3_gen z t (max z t) hz ht (le_max_left _ _) (le_max_right _ _)

/-- Python の `offsets_M3` の式（m = max z t）が、上の窓の左端と一致する。 -/
theorem M3_offsets (z t : ℤ) :
    (W3 z t).l 1 = max z t + z + 1 ∧
    (W3 z t).l 2 = 3*(max z t) + 2*t + z + 3 ∧
    (W3 z t).l 3 = 3*(max z t) + 4*t + z + 4 :=
  ⟨rfl, rfl, rfl⟩

/-- z = t = u のとき、W3 は APFreeWindowSeparation の `wrobWindows u` と一致する。
    すなわちこの閉じた式は Wróblewski 1984 の配置の (z,t) への一般化である。 -/
theorem W3_eq_wrob (u : ℤ) (i : Fin 4) :
    (W3 u u).l i = (wrobWindows u).l i ∧ (W3 u u).r i = (wrobWindows u).r i := by
  have hm : W3 u u = W3g u u u := by rw [W3, max_self]
  rw [hm]
  refine ⟨?_, ?_⟩ <;> fin_cases i <;> simp only [W3g, wrobWindows] <;> ring

/-! ## 3. 段の帰結 -/

/-- M = 3 の段：頭と三つのブロックの合併は 3-AP-free。 -/
theorem step_M3_apfree (z t : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t) (A : Fin 4 → Set ℤ)
    (hbox : ∀ i, ∀ x ∈ A i, (W3 z t).l i ≤ x ∧ x ≤ (W3 z t).r i)
    (hfree : ∀ i, IsThreeAPFree (A i)) : IsThreeAPFree (⋃ i, A i) :=
  apfree_iUnion_of_separated (W3 z t) A hbox hfree (sep_M3 z t hz ht)

/-- 段の後の頭の最大元（最後の窓の右端）。 -/
def nextZ3 (z t : ℤ) : ℤ := 3*(max z t) + 5*t + z + 4

/-- M = 3 の段の窓は、すべて次の段の箱 [0, nextZ3 z t] に収まる。 -/
theorem W3_in_box (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) (i : Fin 4) :
    0 ≤ (W3 z t).l i ∧ (W3 z t).r i ≤ nextZ3 z t := by
  have h1 : z ≤ max z t := le_max_left _ _
  have h2 : t ≤ max z t := le_max_right _ _
  fin_cases i <;> simp only [W3, W3g, nextZ3] <;> omega

/-- 段を継ぐと頭の最大元は必ず増える（倍加税の M = 3 版）。 -/
theorem nextZ3_gt (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) : z < nextZ3 z t := by
  have h1 : z ≤ max z t := le_max_left _ _
  simp only [nextZ3]; omega

/-- 倍加税は M = 3 でも効いている：最初のブロックは 2z より右から始まる。 -/
theorem M3_doubling (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) : 2*z < (W3 z t).l 1 := by
  have h1 : z ≤ max z t := le_max_left _ _
  simp only [W3, W3g]; omega

/-! ## 4. M = 1 / M = 2 との比較（尺度の代金） -/

/-- 一段で使う対数尺度の比（分母子）。M = 3 は幅 t の窓を三つ置くのに
    尺度を 3·max(z,t) + 5t + z + 4 まで使う。t ≤ z なら 4z + 5t + 4、
    t ≥ z なら 8t + z + 4。M = 1 は max(2z, z+t) + 1 + t、
    M = 2（内側案）は 2z + 3t + 2。 -/
theorem nextZ3_cases (z t : ℤ) (_hz : 0 ≤ z) (_ht : 0 ≤ t) :
    (t ≤ z → nextZ3 z t = 4*z + 5*t + 4) ∧ (z ≤ t → nextZ3 z t = 8*t + z + 4) := by
  constructor <;> intro h <;> simp only [nextZ3] <;> omega

end APFree.WindowSeparationM3

/-! ### 公理の確認 -/

#print axioms APFree.WindowSeparationM3.sep_M3_gen
#print axioms APFree.WindowSeparationM3.sep_M3
#print axioms APFree.WindowSeparationM3.W3_eq_wrob
#print axioms APFree.WindowSeparationM3.step_M3_apfree
#print axioms APFree.WindowSeparationM3.W3_in_box
#print axioms APFree.WindowSeparationM3.M3_doubling
