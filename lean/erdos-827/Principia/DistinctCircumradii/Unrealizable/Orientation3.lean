import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU3` の k25・k26

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

set_option linter.unusedVariables false

namespace QU3

/-- 格子の証明書が作る形。`L = R`（証人条件の積）と `N * R = D * L`（単項式の恒等式）
から `N = D` が出る。`N`, `D` は目標の形式に対応する単項式で、`L`, `R` は
証人条件を掛け合わせた単項式である。 -/
theorem eq_of_cert {N D L R : ℂ} (hLR : L = R) (hmono : N * R = D * L) (hL : L ≠ 0) :
    N = D := by
  rw [← hLR] at hmono
  exact mul_right_cancel₀ hL hmono

/-- 2 乗距離は負にならない。 -/
theorem sqdist_nonneg (p q : Pt) : 0 ≤ sqdist p q := by
  simp only [sqdist]
  positivity

/-- `qq` は最初の 2 つの引数について対称。 -/
theorem qq_comm (a b p : Pt) : qq a b p = qq b a p := by
  simp only [qq]; ring

/-- 直角を多項式の等式として書く。`(b - a) * conj (c - a)` の実部が `qq b c a` なので、
その数とその共役の和が `2 * qq b c a` である。 -/
theorem perp_poly {a b c : Pt} (h : qq b c a = 0) :
    (toC b - toC a) * (barC c - barC a) + (barC b - barC a) * (toC c - toC a) = 0 := by
  simp only [qq] at h
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
      toC_re, toC_im, barC_re, barC_im]
  · linear_combination (2 : ℝ) * h
  · ring

/-! ### 共円形式の `m = 2` ——「交比が純虚数」

`cyclicValue u v c d = (u - c)(v - d) · conj ((u - d)(v - c))` は、虚部が
`det4 u v c d` に等しい（`im_cyclicValue`）。だから「4 点が共円でない」は
「この数が実数でない」ことである。格子の証明書が `N ^ 2 = conj N ^ 2` を与えると、
`(N - conj N)(N + conj N) = 0` で、実数でない側が落ちて `N + conj N = 0`、
すなわち **交比が純虚数**になる。

1 つの 4 点組 `{a, b, c, d}` の 3 通りの組分けに対応する 3 つの積を
`P = (a-b)(c-d)`, `Q = (a-c)(b-d)`, `R = (a-d)(b-c)` と書くと `P - Q + R = 0` である。
`Q / R` と `P / R` の両方が純虚数だと、`(Q - R) conj R + conj (Q - R) R = -2 R conj R`
より `R conj R = 0`、つまり 2 点が一致する。**2 本で落ちる。** -/

/-- 共円形式に対応する複素量。 -/
def cyclicValue (u v c d : Pt) : ℂ :=
  (toC u - toC c) * (toC v - toC d) * ((barC u - barC d) * (barC v - barC c))

/-- その共役（`barC` で書いたもの）。 -/
def cyclicValueBar (u v c d : Pt) : ℂ :=
  (barC u - barC c) * (barC v - barC d) * ((toC u - toC d) * (toC v - toC c))

/-- **橋（共円版）**：虚部はちょうど `det4` である。 -/
theorem im_cyclicValue (u v c d : Pt) :
    (cyclicValue u v c d).im = det4 u v c d := by
  simp only [cyclicValue, det4, cross, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-- `cyclicValueBar` は `cyclicValue` の共役である。 -/
theorem cyclicValueBar_eq_conj (u v c d : Pt) :
    cyclicValueBar u v c d = (starRingEnd ℂ) (cyclicValue u v c d) := by
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [cyclicValue, cyclicValueBar, Complex.conj_re, Complex.conj_im,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      toC_re, toC_im, barC_re, barC_im] <;> ring

/-- 一般の位置（`det4 ≠ 0`）で `N ^ 2 = conj N ^ 2` なら `N + conj N = 0`。 -/
theorem cyc_add_bar_eq_zero {u v c d : Pt}
    (hsq : cyclicValue u v c d ^ 2 = cyclicValueBar u v c d ^ 2)
    (hdet : det4 u v c d ≠ 0) :
    cyclicValue u v c d + cyclicValueBar u v c d = 0 := by
  have h : (cyclicValue u v c d - cyclicValueBar u v c d) *
      (cyclicValue u v c d + cyclicValueBar u v c d) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h with h1 | h1
  · refine absurd ?_ hdet
    rw [← im_cyclicValue]
    refine im_eq_zero_iff_eq_conj.mpr ?_
    rw [← cyclicValueBar_eq_conj]
    linear_combination h1
  · exact h1

/-- **同じ 4 点組の 2 つの組分けが両方とも純虚数なら、2 点が一致する。** -/
theorem no_four_points_of_two_imaginary_cross_ratios {a b c d : Pt}
    (had : a ≠ d) (hbc : b ≠ c)
    (hd1 : det4 a b c d ≠ 0) (hd2 : det4 a c b d ≠ 0)
    (hs1 : cyclicValue a b c d ^ 2 = cyclicValueBar a b c d ^ 2)
    (hs2 : cyclicValue a c b d ^ 2 = cyclicValueBar a c b d ^ 2) :
    False := by
  have g1 := cyc_add_bar_eq_zero hs1 hd1
  have g2 := cyc_add_bar_eq_zero hs2 hd2
  simp only [cyclicValue, cyclicValueBar] at g1 g2
  have hR : ((toC a - toC d) * (toC b - toC c)) *
      ((barC a - barC d) * (barC b - barC c)) = 0 := by
    linear_combination (1 / 2 : ℂ) * g1 + (1 / 2 : ℂ) * g2
  exact (mul_ne_zero (mul_ne_zero (toC_sub_ne_zero had) (toC_sub_ne_zero hbc))
    (mul_ne_zero (barC_sub_ne_zero had) (barC_sub_ne_zero hbc))) hR

/-! ### 1 つ目の類 -/

/-- 格子の所属の証明書（枡 7 個・係数 [-1, 1, 1, -2, -1, 1, -1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p1; p2, p3)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem crossRatioCertA1 {z01 z02 z03 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z01 * z14 * c02 * c24 = z02 * z24 * c01 * c14)
    (E2 : z01 * z15 * c03 * c35 = z03 * z35 * c01 * c15)
    (E3 : z14 * z34 * c15 * c35 = z15 * z35 * c14 * c34)
    (E4 : z12 * z25 * c13 * c35 = z13 * z35 * c12 * c25)
    (E5 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (E6 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (E7 : z03 * z05 * c23 * c25 = z23 * z25 * c03 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z02 * z02 * z13 * z13 * c03 * c03 * c12 * c12 = z03 * z03 * z12 * z12 * c02 * c02 * c13 * c13 := by
  have hL : z01 * z02 * z02 * z05 * z13 * z13 * z14 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * c01 * c03 * c03 * c05 * c12 * c12 * c14 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz02)) (nz05)) (nz13)) (nz13)) (nz14)) (nz15)) (nz23)) (nz24)) (nz25)) (nz25)) (nz34)) (nz35)) (nz35)) (nz45)) (nc01)) (nc03)) (nc03)) (nc05)) (nc12)) (nc12)) (nc14)) (nc15)) (nc23)) (nc24)) (nc25)) (nc25)) (nc34)) (nc35)) (nc35)) (nc45)
  have hLR : z01 * z02 * z02 * z05 * z13 * z13 * z14 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * c01 * c03 * c03 * c05 * c12 * c12 * c14 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c35 * c45 = z01 * z03 * z03 * z05 * z12 * z12 * z14 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * c01 * c02 * c02 * c05 * c13 * c13 * c14 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c35 * c45 := by
    linear_combination - (z01 * z02 * z05 * z13 * z13 * z14 * z15 * z23 * z25 * z25 * z34 * z35 * z35 * z45 * c03 * c03 * c05 * c12 * c12 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c35 * c45) * E1 + (z01 * z02 * z05 * z13 * z13 * z14 * z14 * z23 * z25 * z25 * z34 * z35 * z35 * z45 * c02 * c03 * c05 * c12 * c12 * c15 * c23 * c24 * c24 * c25 * c25 * c34 * c35 * c45) * E2 + (z01 * z02 * z03 * z05 * z13 * z13 * z14 * z23 * z25 * z25 * z35 * z35 * z35 * z45 * c01 * c02 * c03 * c05 * c12 * c12 * c15 * c23 * c24 * c24 * c25 * c25 * c34 * c45) * E3 - (z01 * z02 * z03 * z05 * z13 * z14 * z15 * z23 * z25 * z25 * z35 * z35 * z35 * z45 * c01 * c02 * c03 * c05 * c12 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c45) * E4 - (z01 * z02 * z03 * z05 * z12 * z14 * z15 * z23 * z25 * z25 * z25 * z35 * z35 * z45 * c01 * c02 * c03 * c05 * c13 * c14 * c15 * c23 * c24 * c24 * c34 * c34 * c35 * c45) * E4 - (z01 * z02 * z03 * z05 * z12 * z12 * z14 * z15 * z23 * z25 * z25 * z25 * z35 * z35 * c01 * c02 * c03 * c05 * c13 * c13 * c14 * c15 * c24 * c24 * c34 * c35 * c35 * c45) * E5 + (z01 * z03 * z12 * z12 * z14 * z15 * z23 * z23 * z25 * z25 * z25 * z34 * z35 * z35 * c01 * c02 * c03 * c05 * c13 * c13 * c14 * c15 * c24 * c25 * c34 * c35 * c35 * c45) * E6 - (z01 * z03 * z12 * z12 * z14 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * c01 * c02 * c02 * c05 * c13 * c13 * c14 * c15 * c24 * c25 * c34 * c35 * c35 * c45) * E7
  have hmono : z02 * z02 * z13 * z13 * c03 * c03 * c12 * c12 * (z01 * z03 * z03 * z05 * z12 * z12 * z14 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * c01 * c02 * c02 * c05 * c13 * c13 * c14 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c35 * c45) = z03 * z03 * z12 * z12 * c02 * c02 * c13 * c13 * (z01 * z02 * z02 * z05 * z13 * z13 * z14 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * c01 * c03 * c03 * c05 * c12 * c12 * c14 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 7 個・係数 [1, 1, 1, -1, -1, -1, 1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p2; p1, p3)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem crossRatioCertA2 {z01 z02 z03 z04 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 : ℂ}
    (E1 : z02 * z23 * c04 * c34 = z04 * z34 * c02 * c23)
    (E2 : z01 * z14 * c02 * c24 = z02 * z24 * c01 * c14)
    (E3 : z01 * z15 * c03 * c35 = z03 * z35 * c01 * c15)
    (E4 : z12 * z25 * c13 * c35 = z13 * z35 * c12 * c25)
    (E5 : z12 * z13 * c24 * c34 = z24 * z34 * c12 * c13)
    (E6 : z03 * z05 * c23 * c25 = z23 * z25 * c03 * c05)
    (E7 : z04 * z05 * c14 * c15 = z14 * z15 * c04 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    : z01 * z01 * z23 * z23 * c03 * c03 * c12 * c12 = z03 * z03 * z12 * z12 * c01 * c01 * c23 * c23 := by
  have hL : z01 * z01 * z02 * z04 * z05 * z13 * z14 * z15 * z23 * z23 * z24 * z25 * z34 * z35 * c02 * c03 * c03 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c24 * c25 * c34 * c35 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz02)) (nz04)) (nz05)) (nz13)) (nz14)) (nz15)) (nz23)) (nz23)) (nz24)) (nz25)) (nz34)) (nz35)) (nc02)) (nc03)) (nc03)) (nc04)) (nc05)) (nc12)) (nc12)) (nc13)) (nc14)) (nc15)) (nc24)) (nc25)) (nc34)) (nc35)
  have hLR : z01 * z01 * z02 * z04 * z05 * z13 * z14 * z15 * z23 * z23 * z24 * z25 * z34 * z35 * c02 * c03 * c03 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c24 * c25 * c34 * c35 = z02 * z03 * z03 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c04 * c05 * c13 * c14 * c15 * c23 * c23 * c24 * c25 * c34 * c35 := by
    linear_combination (z01 * z01 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * c02 * c03 * c03 * c05 * c12 * c12 * c13 * c14 * c15 * c24 * c25 * c35) * E1 + (z01 * z04 * z04 * z05 * z13 * z15 * z23 * z24 * z25 * z34 * z34 * z35 * c02 * c03 * c03 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c25 * c35) * E2 + (z02 * z04 * z04 * z05 * z13 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * c01 * c02 * c03 * c05 * c12 * c12 * c13 * c14 * c14 * c15 * c23 * c25) * E3 - (z02 * z03 * z04 * z04 * z05 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * c01 * c01 * c02 * c03 * c05 * c12 * c13 * c14 * c14 * c15 * c15 * c23) * E4 - (z02 * z03 * z04 * z04 * z05 * z12 * z23 * z24 * z25 * z25 * z34 * z35 * c01 * c01 * c02 * c03 * c05 * c13 * c14 * c14 * c15 * c15 * c23 * c35) * E5 - (z02 * z03 * z04 * z04 * z05 * z12 * z12 * z13 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c13 * c14 * c14 * c15 * c15 * c23 * c24 * c34 * c35) * E6 + (z02 * z03 * z03 * z04 * z05 * z12 * z12 * z13 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c13 * c14 * c15 * c23 * c23 * c24 * c25 * c34 * c35) * E7
  have hmono : z01 * z01 * z23 * z23 * c03 * c03 * c12 * c12 * (z02 * z03 * z03 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c04 * c05 * c13 * c14 * c15 * c23 * c23 * c24 * c25 * c34 * c35) = z03 * z03 * z12 * z12 * c01 * c01 * c23 * c23 * (z01 * z01 * z02 * z04 * z05 * z13 * z14 * z15 * z23 * z23 * z24 * z25 * z34 * z35 * c02 * c03 * c03 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c24 * c25 * c34 * c35) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- 格子の所属の証明書（枡 7 個・係数 [1, 1, 1, -1, -1, -1, 1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p2; p1, p3)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/

theorem no_general_position_of_imaginary_cross_ratios (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw3 : Psi (p 2) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw5 : Psi (p 1) (p 3) (p 0) (p 5) = 0)
    (hw7 : Psi (p 4) (p 5) (p 1) (p 3) = 0)
    (hw9 : Psi (p 2) (p 3) (p 1) (p 5) = 0)
    (hw10 : Psi (p 1) (p 4) (p 2) (p 3) = 0)
    (hw11 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw12 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 2) (p 3) (p 5) = 0)
    (hw15 : Psi (p 0) (p 1) (p 4) (p 5) = 0)
    : False := by
  have hne := hgp.1
  have hcyc := hgp.2.2
  have hs1 : cyclicValue (p 0) (p 1) (p 2) (p 3) ^ 2
      = cyclicValueBar (p 0) (p 1) (p 2) (p 3) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioCertA1
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 1) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw9)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw11)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw12)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hs2 : cyclicValue (p 0) (p 2) (p 1) (p 3) ^ 2
      = cyclicValueBar (p 0) (p 2) (p 1) (p 3) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioCertA2
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw9)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 3)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (show (toC (p 0) - toC (p 4)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 1) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
  have hd1 : det4 (p 0) (p 1) (p 2) (p 3) ≠ 0 := by
    simpa [Concyclic4] using hcyc 0 1 2 3 (by decide) (by decide) (by decide)
  have hd2 : det4 (p 0) (p 2) (p 1) (p 3) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 3) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 3 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination -hx
  exact no_four_points_of_two_imaginary_cross_ratios
    (hne 0 3 (by decide)) (hne 1 2 (by decide)) hd1 hd2 hs1 hs2

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。 -/
theorem no_general_position_of_imaginary_cross_ratios_all (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 3) (p 4) (p 0) (p 1) = 0)
    (hw2 : Psi (p 1) (p 5) (p 0) (p 2) = 0)
    (hw3 : Psi (p 2) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw5 : Psi (p 1) (p 3) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw7 : Psi (p 4) (p 5) (p 1) (p 3) = 0)
    (hw8 : Psi (p 2) (p 5) (p 1) (p 4) = 0)
    (hw9 : Psi (p 2) (p 3) (p 1) (p 5) = 0)
    (hw10 : Psi (p 1) (p 4) (p 2) (p 3) = 0)
    (hw11 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw12 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw13 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw14 : Psi (p 0) (p 2) (p 3) (p 5) = 0)
    (hw15 : Psi (p 0) (p 1) (p 4) (p 5) = 0)
    : False :=
  no_general_position_of_imaginary_cross_ratios p hgp hw3 hw4 hw5 hw7 hw9 hw10 hw11 hw12 hw14 hw15

/-! ### 2 つ目の類 -/

/-- 格子の所属の証明書（枡 7 個・係数 [-1, 1, -1, -1, -1, 1, -1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p1; p2, p3)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem crossRatioCertB1 {z01 z02 z03 z04 z05 z12 z13 z14 z23 z24 z25 z34 z45 c01 c02 c03 c04 c05 c12 c13 c14 c23 c24 c25 c34 c45 : ℂ}
    (E1 : z03 * z23 * c04 * c24 = z04 * z24 * c03 * c23)
    (E2 : z01 * z13 * c04 * c34 = z04 * z34 * c01 * c13)
    (E3 : z01 * z14 * c02 * c24 = z02 * z24 * c01 * c14)
    (E4 : z12 * z24 * c13 * c34 = z13 * z34 * c12 * c24)
    (E5 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E6 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (E7 : z03 * z05 * c23 * c25 = z23 * z25 * c03 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z02 * z02 * z13 * z13 * c03 * c03 * c12 * c12 = z03 * z03 * z12 * z12 * c02 * c02 * c13 * c13 := by
  have hL : z01 * z02 * z02 * z04 * z05 * z13 * z13 * z14 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c03 * c03 * c04 * c05 * c12 * c12 * c14 * c23 * c24 * c24 * c25 * c34 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz02)) (nz04)) (nz05)) (nz13)) (nz13)) (nz14)) (nz23)) (nz24)) (nz24)) (nz25)) (nz34)) (nz45)) (nc01)) (nc03)) (nc03)) (nc04)) (nc05)) (nc12)) (nc12)) (nc14)) (nc23)) (nc24)) (nc24)) (nc25)) (nc34)) (nc45)
  have hLR : z01 * z02 * z02 * z04 * z05 * z13 * z13 * z14 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c03 * c03 * c04 * c05 * c12 * c12 * c14 * c23 * c24 * c24 * c25 * c34 * c45 = z01 * z03 * z03 * z04 * z05 * z12 * z12 * z14 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c02 * c02 * c04 * c05 * c13 * c13 * c14 * c23 * c24 * c24 * c25 * c34 * c45 := by
    linear_combination - (z01 * z02 * z02 * z05 * z13 * z13 * z14 * z23 * z24 * z25 * z34 * z45 * c01 * c03 * c04 * c05 * c12 * c12 * c14 * c24 * c24 * c25 * c34 * c45) * E1 + (z02 * z02 * z03 * z05 * z13 * z14 * z23 * z23 * z24 * z25 * z34 * z45 * c01 * c03 * c04 * c05 * c12 * c12 * c14 * c24 * c24 * c24 * c25 * c45) * E2 - (z02 * z03 * z04 * z05 * z13 * z14 * z23 * z23 * z25 * z34 * z34 * z45 * c01 * c03 * c04 * c05 * c12 * c12 * c13 * c24 * c24 * c24 * c25 * c45) * E3 - (z01 * z02 * z03 * z04 * z05 * z14 * z14 * z23 * z23 * z25 * z34 * z45 * c01 * c02 * c03 * c04 * c05 * c12 * c13 * c24 * c24 * c24 * c25 * c45) * E4 - (z01 * z02 * z03 * z04 * z05 * z12 * z14 * z23 * z23 * z24 * z25 * z34 * c01 * c02 * c03 * c04 * c05 * c13 * c13 * c24 * c24 * c24 * c34 * c45) * E5 + (z01 * z03 * z04 * z12 * z12 * z14 * z23 * z23 * z24 * z25 * z25 * z34 * c01 * c02 * c03 * c04 * c05 * c13 * c13 * c14 * c24 * c24 * c34 * c45) * E6 - (z01 * z03 * z04 * z12 * z12 * z14 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c02 * c02 * c04 * c05 * c13 * c13 * c14 * c24 * c24 * c34 * c45) * E7
  have hmono : z02 * z02 * z13 * z13 * c03 * c03 * c12 * c12 * (z01 * z03 * z03 * z04 * z05 * z12 * z12 * z14 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c02 * c02 * c04 * c05 * c13 * c13 * c14 * c23 * c24 * c24 * c25 * c34 * c45) = z03 * z03 * z12 * z12 * c02 * c02 * c13 * c13 * (z01 * z02 * z02 * z04 * z05 * z13 * z13 * z14 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c03 * c03 * c04 * c05 * c12 * c12 * c14 * c23 * c24 * c24 * c25 * c34 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 7 個・係数 [1, 1, -1, -1, 1, -1, 1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p2; p1, p3)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem crossRatioCertB2 {z01 z03 z04 z05 z12 z13 z14 z15 z23 z25 z34 z35 z45 c01 c03 c04 c05 c12 c13 c14 c15 c23 c25 c34 c35 c45 : ℂ}
    (E1 : z01 * z13 * c04 * c34 = z04 * z34 * c01 * c13)
    (E2 : z01 * z15 * c03 * c35 = z03 * z35 * c01 * c15)
    (E3 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E4 : z12 * z13 * c25 * c35 = z25 * z35 * c12 * c13)
    (E5 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (E6 : z03 * z05 * c23 * c25 = z23 * z25 * c03 * c05)
    (E7 : z04 * z05 * c14 * c15 = z14 * z15 * c04 * c05)
    (nz01 : z01 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z01 * z01 * z23 * z23 * c03 * c03 * c12 * c12 = z03 * z03 * z12 * z12 * c01 * c01 * c23 * c23 := by
  have hL : z01 * z01 * z04 * z05 * z13 * z14 * z15 * z23 * z23 * z25 * z25 * z34 * z35 * z45 * c03 * c03 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c25 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz04)) (nz05)) (nz13)) (nz14)) (nz15)) (nz23)) (nz23)) (nz25)) (nz25)) (nz34)) (nz35)) (nz45)) (nc03)) (nc03)) (nc04)) (nc05)) (nc12)) (nc12)) (nc13)) (nc14)) (nc15)) (nc25)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z01 * z04 * z05 * z13 * z14 * z15 * z23 * z23 * z25 * z25 * z34 * z35 * z45 * c03 * c03 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c25 * c25 * c34 * c35 * c45 = z03 * z03 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z25 * z25 * z34 * z35 * z45 * c01 * c01 * c04 * c05 * c13 * c14 * c15 * c23 * c23 * c25 * c25 * c34 * c35 * c45 := by
    linear_combination (z01 * z04 * z05 * z14 * z15 * z23 * z23 * z25 * z25 * z34 * z35 * z45 * c03 * c03 * c05 * c12 * c12 * c13 * c14 * c15 * c25 * c25 * c35 * c45) * E1 + (z04 * z04 * z05 * z14 * z23 * z23 * z25 * z25 * z34 * z34 * z35 * z45 * c01 * c03 * c05 * c12 * c12 * c13 * c13 * c14 * c15 * c25 * c25 * c45) * E2 - (z03 * z04 * z04 * z05 * z23 * z23 * z25 * z25 * z34 * z34 * z35 * z35 * c01 * c01 * c03 * c05 * c12 * c13 * c13 * c14 * c15 * c15 * c25 * c45) * E3 - (z03 * z04 * z04 * z05 * z12 * z23 * z23 * z25 * z25 * z34 * z34 * z35 * c01 * c01 * c03 * c05 * c13 * c14 * c14 * c15 * c15 * c25 * c45 * c45) * E4 + (z03 * z04 * z04 * z05 * z12 * z12 * z13 * z23 * z25 * z25 * z34 * z35 * c01 * c01 * c03 * c05 * c13 * c14 * c14 * c15 * c15 * c25 * c35 * c45) * E5 - (z03 * z04 * z04 * z05 * z12 * z12 * z13 * z25 * z25 * z34 * z35 * z45 * c01 * c01 * c13 * c14 * c14 * c15 * c15 * c23 * c25 * c34 * c35 * c45) * E6 + (z03 * z03 * z04 * z05 * z12 * z12 * z13 * z25 * z25 * z34 * z35 * z45 * c01 * c01 * c13 * c14 * c15 * c23 * c23 * c25 * c25 * c34 * c35 * c45) * E7
  have hmono : z01 * z01 * z23 * z23 * c03 * c03 * c12 * c12 * (z03 * z03 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z25 * z25 * z34 * z35 * z45 * c01 * c01 * c04 * c05 * c13 * c14 * c15 * c23 * c23 * c25 * c25 * c34 * c35 * c45) = z03 * z03 * z12 * z12 * c01 * c01 * c23 * c23 * (z01 * z01 * z04 * z05 * z13 * z14 * z15 * z23 * z23 * z25 * z25 * z34 * z35 * z45 * c03 * c03 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c25 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- 格子の所属の証明書（枡 7 個・係数 [1, 1, -1, -1, 1, -1, 1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p2; p1, p3)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/

theorem no_general_position_of_imaginary_cross_ratios' (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw2 : Psi (p 3) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 1) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw5 : Psi (p 1) (p 3) (p 0) (p 5) = 0)
    (hw8 : Psi (p 2) (p 3) (p 1) (p 4) = 0)
    (hw9 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw10 : Psi (p 1) (p 5) (p 2) (p 3) = 0)
    (hw11 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw12 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 2) (p 3) (p 5) = 0)
    (hw15 : Psi (p 0) (p 1) (p 4) (p 5) = 0)
    : False := by
  have hne := hgp.1
  have hcyc := hgp.2.2
  have hs1 : cyclicValue (p 0) (p 1) (p 2) (p 3) ^ 2
      = cyclicValueBar (p 0) (p 1) (p 2) (p 3) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioCertB1
      (show (toC (p 0) - toC (p 3)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 3)) * (barC (p 2) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 3)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw8)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw9)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw12)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hs2 : cyclicValue (p 0) (p 2) (p 1) (p 3) ^ 2
      = cyclicValueBar (p 0) (p 2) (p 1) (p 3) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioCertB2
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 3)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw9)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 3)) * (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw11)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (show (toC (p 0) - toC (p 4)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 1) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hd1 : det4 (p 0) (p 1) (p 2) (p 3) ≠ 0 := by
    simpa [Concyclic4] using hcyc 0 1 2 3 (by decide) (by decide) (by decide)
  have hd2 : det4 (p 0) (p 2) (p 1) (p 3) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 3) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 3 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination -hx
  exact no_four_points_of_two_imaginary_cross_ratios
    (hne 0 3 (by decide)) (hne 1 2 (by decide)) hd1 hd2 hs1 hs2

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。 -/
theorem no_general_position_of_imaginary_cross_ratios_all' (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw2 : Psi (p 3) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 1) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw5 : Psi (p 1) (p 3) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw7 : Psi (p 4) (p 5) (p 1) (p 3) = 0)
    (hw8 : Psi (p 2) (p 3) (p 1) (p 4) = 0)
    (hw9 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw10 : Psi (p 1) (p 5) (p 2) (p 3) = 0)
    (hw11 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw12 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw13 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw14 : Psi (p 0) (p 2) (p 3) (p 5) = 0)
    (hw15 : Psi (p 0) (p 1) (p 4) (p 5) = 0)
    : False :=
  no_general_position_of_imaginary_cross_ratios' p hgp hw2 hw3 hw4 hw5 hw8 hw9 hw10 hw11 hw12 hw14 hw15

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## The direction classes, in the shape of the census -/

/-! ### Class 25 -/

/-- The mask of class 25 (entry 24 of `censusRest`). -/
def maskK25 : Mask := 19966497677405743500001544

/-- Class 25 is one of the thirty-four census representatives. -/
theorem maskK25_mem : maskK25 ∈ censusRest := by decide

/-- **Class 25, sharp form.**  No six points in general position support
the mask of class 25.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k25 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK25) : False := by
  have c3 : Psi (p 3) (p 4) (p 0) (p 1) = 0 := by
    have h := hs 3 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 3 = ((0, 1), (3, 4)) from by decide)] at h
  have c8 : Psi (p 1) (p 5) (p 0) (p 2) = 0 := by
    have h := hs 8 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 8 = ((0, 2), (1, 5)) from by decide)] at h
  have c15 : Psi (p 2) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 15 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 15 = ((0, 3), (2, 4)) from by decide)] at h
  have c18 : Psi (p 1) (p 2) (p 0) (p 4) = 0 := by
    have h := hs 18 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 18 = ((0, 4), (1, 2)) from by decide)] at h
  have c25 : Psi (p 1) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 25 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 25 = ((0, 5), (1, 3)) from by decide)] at h
  have c30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hs 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  have c41 : Psi (p 4) (p 5) (p 1) (p 3) = 0 := by
    have h := hs 41 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 41 = ((1, 3), (4, 5)) from by decide)] at h
  have c46 : Psi (p 2) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 46 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 46 = ((1, 4), (2, 5)) from by decide)] at h
  have c51 : Psi (p 2) (p 3) (p 1) (p 5) = 0 := by
    have h := hs 51 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 51 = ((1, 5), (2, 3)) from by decide)] at h
  have c57 : Psi (p 1) (p 4) (p 2) (p 3) = 0 := by
    have h := hs 57 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 57 = ((2, 3), (1, 4)) from by decide)] at h
  have c65 : Psi (p 3) (p 5) (p 2) (p 4) = 0 := by
    have h := hs 65 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 65 = ((2, 4), (3, 5)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c79 : Psi (p 0) (p 2) (p 3) (p 5) = 0 := by
    have h := hs 79 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 79 = ((3, 5), (0, 2)) from by decide)] at h
  have c84 : Psi (p 0) (p 1) (p 4) (p 5) = 0 := by
    have h := hs 84 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 84 = ((4, 5), (0, 1)) from by decide)] at h
  exact no_general_position_of_imaginary_cross_ratios_all p hgp c3 c8 c15 c18 c25 c30 c41 c46 c51 c57 c65 c68 c74 c79 c84

/-- **Class 25.**  No six points in general position carry the mask of
class 25. -/
theorem not_carries_k25 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK25) : False :=
  not_supports_k25 p hgp (supports_of_carries hc)

/-! ### Class 26 -/

/-- The mask of class 26 (entry 25 of `censusRest`). -/
def maskK26 : Mask := 19966497823737547017429508

/-- Class 26 is one of the thirty-four census representatives. -/
theorem maskK26_mem : maskK26 ∈ censusRest := by decide

/-- **Class 26, sharp form.**  No six points in general position support
the mask of class 26.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k26 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK26) : False := by
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have c9 : Psi (p 3) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 9 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 9 = ((0, 2), (3, 4)) from by decide)] at h
  have c13 : Psi (p 1) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 13 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 13 = ((0, 3), (1, 4)) from by decide)] at h
  have c18 : Psi (p 1) (p 2) (p 0) (p 4) = 0 := by
    have h := hs 18 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 18 = ((0, 4), (1, 2)) from by decide)] at h
  have c25 : Psi (p 1) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 25 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 25 = ((0, 5), (1, 3)) from by decide)] at h
  have c30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hs 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  have c41 : Psi (p 4) (p 5) (p 1) (p 3) = 0 := by
    have h := hs 41 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 41 = ((1, 3), (4, 5)) from by decide)] at h
  have c45 : Psi (p 2) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 45 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 45 = ((1, 4), (2, 3)) from by decide)] at h
  have c52 : Psi (p 2) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 52 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 52 = ((1, 5), (2, 4)) from by decide)] at h
  have c58 : Psi (p 1) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 58 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 58 = ((2, 3), (1, 5)) from by decide)] at h
  have c65 : Psi (p 3) (p 5) (p 2) (p 4) = 0 := by
    have h := hs 65 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 65 = ((2, 4), (3, 5)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c79 : Psi (p 0) (p 2) (p 3) (p 5) = 0 := by
    have h := hs 79 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 79 = ((3, 5), (0, 2)) from by decide)] at h
  have c84 : Psi (p 0) (p 1) (p 4) (p 5) = 0 := by
    have h := hs 84 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 84 = ((4, 5), (0, 1)) from by decide)] at h
  exact no_general_position_of_imaginary_cross_ratios_all' p hgp c2 c9 c13 c18 c25 c30 c41 c45 c52 c58 c65 c68 c74 c79 c84

/-- **Class 26.**  No six points in general position carry the mask of
class 26. -/
theorem not_carries_k26 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK26) : False :=
  not_supports_k26 p hgp (supports_of_carries hc)



end QU3

end DistinctCircumradii

#print axioms DistinctCircumradii.QU3.eq_of_cert
#print axioms DistinctCircumradii.QU3.sqdist_nonneg
#print axioms DistinctCircumradii.QU3.qq_comm
#print axioms DistinctCircumradii.QU3.perp_poly
#print axioms DistinctCircumradii.QU3.im_cyclicValue
#print axioms DistinctCircumradii.QU3.cyclicValueBar_eq_conj
#print axioms DistinctCircumradii.QU3.cyc_add_bar_eq_zero
#print axioms DistinctCircumradii.QU3.no_four_points_of_two_imaginary_cross_ratios
#print axioms DistinctCircumradii.QU3.crossRatioCertA1
#print axioms DistinctCircumradii.QU3.crossRatioCertA2
#print axioms DistinctCircumradii.QU3.no_general_position_of_imaginary_cross_ratios
#print axioms DistinctCircumradii.QU3.no_general_position_of_imaginary_cross_ratios_all
#print axioms DistinctCircumradii.QU3.crossRatioCertB1
#print axioms DistinctCircumradii.QU3.crossRatioCertB2
#print axioms DistinctCircumradii.QU3.no_general_position_of_imaginary_cross_ratios'
#print axioms DistinctCircumradii.QU3.no_general_position_of_imaginary_cross_ratios_all'
#print axioms DistinctCircumradii.QU3.cellPsi_eq
#print axioms DistinctCircumradii.QU3.maskK25_mem
#print axioms DistinctCircumradii.QU3.not_supports_k25
#print axioms DistinctCircumradii.QU3.not_carries_k25
#print axioms DistinctCircumradii.QU3.maskK26_mem
#print axioms DistinctCircumradii.QU3.not_supports_k26
#print axioms DistinctCircumradii.QU3.not_carries_k26
