import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU4` の k16・k17

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

set_option linter.unusedVariables false

namespace QU4

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

/-- 2 乗距離は対称。 -/
theorem sqdist_comm (a b : Pt) : sqdist a b = sqdist b a := by
  simp only [sqdist]; ring

/-- 相異なる 2 点の 2 乗距離は正。 -/
theorem sqdist_pos {a b : Pt} (h : a ≠ b) : 0 < sqdist a b := by
  rcases (sqdist_nonneg a b).lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (eq_of_sqdist_eq_zero h1.symm) h

/-- **共円形式の 2 乗距離での読み**。`P - Q + R = 0` から
`|P| ^ 2 = |Q| ^ 2 + |R| ^ 2` になるのと同じ式である。 -/
theorem re_cyclic_sum (u v c d : Pt) :
    (cyclicValue u v c d + cyclicValueBar u v c d).re
      = sqdist u c * sqdist v d + sqdist u d * sqdist v c - sqdist u v * sqdist c d := by
  simp only [cyclicValue, cyclicValueBar, sqdist, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-! ### 1 つ目の類 -/

/-- 格子の所属の証明書（枡 4 個・係数 [1, -1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{02} - e_{25}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p2 - p0) / (p2 - p5)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem mixedAngle1 {z01 z02 z05 z12 z14 z24 z25 z45 c01 c02 c05 c12 c14 c24 c25 c45 : ℂ}
    (E1 : z01 * z12 * c05 * c25 = z05 * z25 * c01 * c12)
    (E2 : z01 * z14 * c02 * c24 = z02 * z24 * c01 * c14)
    (E3 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E4 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z02 * z02 * c25 * c25 = z25 * z25 * c02 * c02 := by
  have hL : z01 * z02 * z02 * z05 * z12 * z14 * z24 * z45 * c01 * c05 * c12 * c14 * c24 * c25 * c25 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz02)) (nz05)) (nz12)) (nz14)) (nz24)) (nz45)) (nc01)) (nc05)) (nc12)) (nc14)) (nc24)) (nc25)) (nc25)) (nc45)
  have hLR : z01 * z02 * z02 * z05 * z12 * z14 * z24 * z45 * c01 * c05 * c12 * c14 * c24 * c25 * c25 * c45 = z01 * z05 * z12 * z14 * z24 * z25 * z25 * z45 * c01 * c02 * c02 * c05 * c12 * c14 * c24 * c45 := by
    linear_combination (z02 * z02 * z05 * z14 * z24 * z45 * c01 * c12 * c14 * c24 * c25 * c45) * E1 - (z02 * z05 * z05 * z14 * z25 * z45 * c01 * c12 * c12 * c24 * c25 * c45) * E2 - (z01 * z02 * z05 * z05 * z14 * z25 * c01 * c02 * c12 * c24 * c24 * c45) * E3 + (z01 * z05 * z12 * z14 * z25 * z25 * c01 * c02 * c12 * c14 * c24 * c45) * E4
  have hmono : z02 * z02 * c25 * c25 * (z01 * z05 * z12 * z14 * z24 * z25 * z25 * z45 * c01 * c02 * c02 * c05 * c12 * c14 * c24 * c45) = z25 * z25 * c02 * c02 * (z01 * z02 * z02 * z05 * z12 * z14 * z24 * z45 * c01 * c05 * c12 * c14 * c24 * c25 * c25 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 5 個・係数 [-1, -1, 1, 1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{15} - e_{25}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p5 - p1) / (p5 - p2)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem mixedAngle2 {z02 z03 z05 z13 z15 z24 z25 z34 z35 z45 c02 c03 c05 c13 c15 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z25 * c03 * c35 = z03 * z35 * c02 * c25)
    (E2 : z13 * z34 * c15 * c45 = z15 * z45 * c13 * c34)
    (E3 : z24 * z34 * c25 * c35 = z25 * z35 * c24 * c34)
    (E4 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (E5 : z03 * z05 * c13 * c15 = z13 * z15 * c03 * c05)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z15 * z15 * c25 * c25 = z25 * z25 * c15 * c15 := by
  have hL : z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz02) (nz03)) (nz05)) (nz13)) (nz15)) (nz15)) (nz24)) (nz34)) (nz35)) (nz45)) (nc02)) (nc03)) (nc05)) (nc13)) (nc24)) (nc25)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 = z02 * z03 * z05 * z13 * z24 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c15 * c15 * c24 * c34 * c35 * c45 := by
    linear_combination - (z02 * z05 * z13 * z15 * z15 * z24 * z34 * z45 * c03 * c05 * c13 * c24 * c25 * c34 * c35 * c45) * E1 - (z02 * z02 * z05 * z13 * z15 * z24 * z25 * z34 * c03 * c03 * c05 * c24 * c25 * c35 * c35 * c45) * E2 + (z02 * z02 * z05 * z13 * z13 * z15 * z25 * z34 * c03 * c03 * c05 * c15 * c24 * c35 * c45 * c45) * E3 + (z02 * z13 * z13 * z15 * z25 * z25 * z34 * z35 * c03 * c03 * c05 * c15 * c24 * c34 * c35 * c45) * E4 - (z02 * z13 * z24 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c05 * c15 * c24 * c34 * c35 * c45) * E5
  have hmono : z15 * z15 * c25 * c25 * (z02 * z03 * z05 * z13 * z24 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c15 * c15 * c24 * c34 * c35 * c45) = z25 * z25 * c15 * c15 * (z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 9 個・係数 [1, 1, 1, 1, -1, -2, -1, -2, 1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p2; p1, p5)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem mixedCross {z01 z02 z03 z04 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z01 * z15 * c04 * c45 = z04 * z45 * c01 * c15)
    (E2 : z02 * z25 * c03 * c35 = z03 * z35 * c02 * c25)
    (E3 : z01 * z02 * c13 * c23 = z13 * z23 * c01 * c02)
    (E4 : z13 * z34 * c15 * c45 = z15 * z45 * c13 * c34)
    (E5 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E6 : z24 * z34 * c25 * c35 = z25 * z35 * c24 * c34)
    (E7 : z12 * z14 * c23 * c34 = z23 * z34 * c12 * c14)
    (E8 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (E9 : z03 * z04 * c35 * c45 = z35 * z45 * c03 * c04)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z01 * z01 * z25 * z25 * c05 * c05 * c12 * c12 = z05 * z05 * z12 * z12 * c01 * c01 * c25 * c25 := by
  have hL : z01 * z01 * z02 * z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz02)) (nz02)) (nz03)) (nz04)) (nz13)) (nz14)) (nz15)) (nz23)) (nz24)) (nz24)) (nz25)) (nz25)) (nz25)) (nz34)) (nz34)) (nz35)) (nz35)) (nz45)) (nz45)) (nz45)) (nc02)) (nc02)) (nc03)) (nc04)) (nc05)) (nc05)) (nc12)) (nc12)) (nc13)) (nc14)) (nc15)) (nc23)) (nc24)) (nc24)) (nc25)) (nc34)) (nc34)) (nc35)) (nc35)) (nc45)) (nc45)) (nc45)
  have hLR : z01 * z01 * z02 * z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45 = z02 * z02 * z03 * z04 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c03 * c04 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45 := by
    linear_combination (z01 * z02 * z02 * z03 * z04 * z13 * z14 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45) * E1 + (z01 * z02 * z03 * z04 * z04 * z13 * z14 * z23 * z24 * z24 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c02 * c02 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c45 * c45) * E2 + (z03 * z03 * z04 * z04 * z13 * z14 * z23 * z24 * z24 * z25 * z25 * z34 * z34 * z35 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c02 * c02 * c02 * c05 * c05 * c12 * c12 * c14 * c15 * c15 * c24 * c24 * c25 * c25 * c34 * c34 * c35 * c45 * c45) * E3 + (z03 * z03 * z04 * z04 * z13 * z14 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c12 * c14 * c15 * c24 * c24 * c25 * c25 * c34 * c34 * c35 * c45) * E4 - (z03 * z03 * z04 * z04 * z13 * z15 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c13 * c14 * c15 * c24 * c24 * c25 * c34 * c34 * c34 * c35 * c45) * E5 - (z03 * z03 * z04 * z04 * z12 * z13 * z15 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c13 * c14 * c14 * c15 * c24 * c25 * c34 * c34 * c35 * c45 * c45) * E6 - (z03 * z03 * z04 * z04 * z12 * z13 * z15 * z23 * z23 * z24 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c13 * c14 * c14 * c15 * c25 * c25 * c34 * c35 * c35 * c45 * c45) * E6 - (z03 * z03 * z04 * z04 * z12 * z13 * z15 * z23 * z24 * z24 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c13 * c14 * c15 * c25 * c25 * c25 * c34 * c35 * c35 * c35 * c45 * c45) * E7 - (z03 * z03 * z04 * z04 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c05 * c13 * c14 * c15 * c23 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c35 * c45 * c45) * E8 - (z02 * z03 * z03 * z04 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * c01 * c01 * c02 * c02 * c13 * c14 * c15 * c23 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c35 * c45 * c45 * c45) * E8 + (z02 * z02 * z03 * z04 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * c01 * c01 * c02 * c02 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45) * E9
  have hmono : z01 * z01 * z25 * z25 * c05 * c05 * c12 * c12 * (z02 * z02 * z03 * z04 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c03 * c04 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45) = z05 * z05 * z12 * z12 * c01 * c01 * c25 * c25 * (z01 * z01 * z02 * z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- **この枡の証人を持つ 6 点は一般の位置にない。**単因子が `1⁹, 2, 2, 2, 4` の類（15 枡）。位数 2 の共線形式は `(2;0,5), (5;1,2), (5;3,4)` の 3 本しかなく、直角だけでは落ちない。使うのは前の 2 本と、4 点組 `{p₀, p₁, p₂, p₅}` の組分け `(0,2;1,5)` の共円形式（位数 2）である。 -/

theorem no_general_position_of_right_angles_and_cross_ratio (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw2 : Psi (p 1) (p 5) (p 0) (p 2) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw5 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw6 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw7 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw9 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw10 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw12 : Psi (p 1) (p 3) (p 2) (p 4) = 0)
    (hw13 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : False := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have hcyc := hgp.2.2
  have hsq1 : ((toC (p 2) - toC (p 0)) * (barC (p 2) - barC (p 5))) ^ 2
      = ((barC (p 2) - barC (p 0)) * (toC (p 2) - toC (p 5))) ^ 2 := by
    linear_combination mixedAngle1
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 2)) by linear_combination (-1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr1 : qq (p 0) (p 5) (p 2) * cross (p 2) (p 0) (p 5) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq1
  have hc1 : cross (p 2) (p 0) (p 5) ≠ 0 := by
    have h0 : cross (p 0) (p 2) (p 5) ≠ 0 := by
      simpa [Collinear3] using hcol 0 2 5 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination -hx
  have ha1 : qq (p 0) (p 5) (p 2) = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact h
    · exact absurd h hc1
  have hsq2 : ((toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 2))) ^ 2
      = ((barC (p 5) - barC (p 1)) * (toC (p 5) - toC (p 2))) ^ 2 := by
    linear_combination mixedAngle2
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw9)
      (show (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 5)) = (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr2 : qq (p 1) (p 2) (p 5) * cross (p 5) (p 1) (p 2) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq2
  have hc2 : cross (p 5) (p 1) (p 2) ≠ 0 := by
    have h0 : cross (p 1) (p 2) (p 5) ≠ 0 := by
      simpa [Collinear3] using hcol 1 2 5 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination hx
  have ha2 : qq (p 1) (p 2) (p 5) = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact h
    · exact absurd h hc2
  have hs : cyclicValue (p 0) (p 2) (p 1) (p 5) ^ 2
      = cyclicValueBar (p 0) (p 2) (p 1) (p 5) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination mixedCross
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 0) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) * (barC (p 1) - barC (p 3)) * (barC (p 2) - barC (p 3)) = (toC (p 1) - toC (p 3)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw9)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw12)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hd : det4 (p 0) (p 2) (p 1) (p 5) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 5) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 5 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination -hx
  have hg := cyc_add_bar_eq_zero hs hd
  have d1 : sqdist (p 0) (p 2) + sqdist (p 2) (p 5) - sqdist (p 0) (p 5) = 0 := by
    simp only [sqdist, qq] at ha1 ⊢
    linear_combination 2 * ha1
  have d2 : sqdist (p 1) (p 5) + sqdist (p 2) (p 5) - sqdist (p 1) (p 2) = 0 := by
    simp only [sqdist, qq] at ha2 ⊢
    linear_combination 2 * ha2
  have h3 : sqdist (p 0) (p 1) * sqdist (p 2) (p 5) + sqdist (p 0) (p 5) * sqdist (p 1) (p 2) - sqdist (p 0) (p 2) * sqdist (p 1) (p 5) = 0 := by
    have h := congrArg Complex.re hg
    rw [re_cyclic_sum, Complex.zero_re, sqdist_comm (p 2) (p 1)] at h
    linear_combination h
  have hfin : sqdist (p 2) (p 5) * (sqdist (p 0) (p 1) + sqdist (p 0) (p 2) + sqdist (p 1) (p 2)) = 0 := by
    linear_combination (sqdist (p 1) (p 2)) * d1 + (sqdist (p 0) (p 2)) * d2 + h3
  have hp : 0 < sqdist (p 2) (p 5) * (sqdist (p 0) (p 1) + sqdist (p 0) (p 2) + sqdist (p 1) (p 2)) := by
    refine mul_pos (sqdist_pos (hne 2 5 (by decide))) ?_
    have t1 := sqdist_pos (hne 0 1 (by decide))
    have t2 := sqdist_nonneg (p 0) (p 2)
    have t3 := sqdist_nonneg (p 1) (p 2)
    linarith
  exact absurd hfin hp.ne'

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。 -/
theorem no_general_position_of_right_angles_and_cross_ratio_all (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 3) (p 4) (p 0) (p 1) = 0)
    (hw2 : Psi (p 1) (p 5) (p 0) (p 2) = 0)
    (hw3 : Psi (p 2) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw5 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw6 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw7 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw8 : Psi (p 2) (p 5) (p 1) (p 3) = 0)
    (hw9 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw10 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw12 : Psi (p 1) (p 3) (p 2) (p 4) = 0)
    (hw13 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : False :=
  no_general_position_of_right_angles_and_cross_ratio p hgp hw2 hw4 hw5 hw6 hw7 hw9 hw10 hw11 hw12 hw13 hw14 hw15

/-! ### 2 つ目の類 -/

/-- 格子の所属の証明書（枡 4 個・係数 [1, -1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{02} - e_{25}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p2 - p0) / (p2 - p5)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem mixedAltAngle1 {z01 z02 z05 z12 z14 z24 z25 z45 c01 c02 c05 c12 c14 c24 c25 c45 : ℂ}
    (E1 : z01 * z12 * c05 * c25 = z05 * z25 * c01 * c12)
    (E2 : z01 * z14 * c02 * c24 = z02 * z24 * c01 * c14)
    (E3 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E4 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z02 * z02 * c25 * c25 = z25 * z25 * c02 * c02 := by
  have hL : z01 * z02 * z02 * z05 * z12 * z14 * z24 * z45 * c01 * c05 * c12 * c14 * c24 * c25 * c25 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz02)) (nz05)) (nz12)) (nz14)) (nz24)) (nz45)) (nc01)) (nc05)) (nc12)) (nc14)) (nc24)) (nc25)) (nc25)) (nc45)
  have hLR : z01 * z02 * z02 * z05 * z12 * z14 * z24 * z45 * c01 * c05 * c12 * c14 * c24 * c25 * c25 * c45 = z01 * z05 * z12 * z14 * z24 * z25 * z25 * z45 * c01 * c02 * c02 * c05 * c12 * c14 * c24 * c45 := by
    linear_combination (z02 * z02 * z05 * z14 * z24 * z45 * c01 * c12 * c14 * c24 * c25 * c45) * E1 - (z02 * z05 * z05 * z14 * z25 * z45 * c01 * c12 * c12 * c24 * c25 * c45) * E2 - (z01 * z02 * z05 * z05 * z14 * z25 * c01 * c02 * c12 * c24 * c24 * c45) * E3 + (z01 * z05 * z12 * z14 * z25 * z25 * c01 * c02 * c12 * c14 * c24 * c45) * E4
  have hmono : z02 * z02 * c25 * c25 * (z01 * z05 * z12 * z14 * z24 * z25 * z25 * z45 * c01 * c02 * c02 * c05 * c12 * c14 * c24 * c45) = z25 * z25 * c02 * c02 * (z01 * z02 * z02 * z05 * z12 * z14 * z24 * z45 * c01 * c05 * c12 * c14 * c24 * c25 * c25 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 5 個・係数 [-1, -1, 1, 1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{15} - e_{25}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p5 - p1) / (p5 - p2)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem mixedAltAngle2 {z02 z03 z05 z13 z15 z24 z25 z34 z35 z45 c02 c03 c05 c13 c15 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z25 * c03 * c35 = z03 * z35 * c02 * c25)
    (E2 : z13 * z34 * c15 * c45 = z15 * z45 * c13 * c34)
    (E3 : z24 * z34 * c25 * c35 = z25 * z35 * c24 * c34)
    (E4 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (E5 : z03 * z05 * c13 * c15 = z13 * z15 * c03 * c05)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z15 * z15 * c25 * c25 = z25 * z25 * c15 * c15 := by
  have hL : z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz02) (nz03)) (nz05)) (nz13)) (nz15)) (nz15)) (nz24)) (nz34)) (nz35)) (nz45)) (nc02)) (nc03)) (nc05)) (nc13)) (nc24)) (nc25)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 = z02 * z03 * z05 * z13 * z24 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c15 * c15 * c24 * c34 * c35 * c45 := by
    linear_combination - (z02 * z05 * z13 * z15 * z15 * z24 * z34 * z45 * c03 * c05 * c13 * c24 * c25 * c34 * c35 * c45) * E1 - (z02 * z02 * z05 * z13 * z15 * z24 * z25 * z34 * c03 * c03 * c05 * c24 * c25 * c35 * c35 * c45) * E2 + (z02 * z02 * z05 * z13 * z13 * z15 * z25 * z34 * c03 * c03 * c05 * c15 * c24 * c35 * c45 * c45) * E3 + (z02 * z13 * z13 * z15 * z25 * z25 * z34 * z35 * c03 * c03 * c05 * c15 * c24 * c34 * c35 * c45) * E4 - (z02 * z13 * z24 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c05 * c15 * c24 * c34 * c35 * c45) * E5
  have hmono : z15 * z15 * c25 * c25 * (z02 * z03 * z05 * z13 * z24 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c15 * c15 * c24 * c34 * c35 * c45) = z25 * z25 * c15 * c15 * (z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 9 個・係数 [1, 1, 1, 1, -1, -2, -1, -2, 1]）を抽象の複素変数で書いたもの。結論は共円形式 `F(p0, p2; p1, p5)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem mixedAltCross {z01 z02 z03 z04 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z01 * z15 * c04 * c45 = z04 * z45 * c01 * c15)
    (E2 : z02 * z25 * c03 * c35 = z03 * z35 * c02 * c25)
    (E3 : z01 * z02 * c13 * c23 = z13 * z23 * c01 * c02)
    (E4 : z13 * z34 * c15 * c45 = z15 * z45 * c13 * c34)
    (E5 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E6 : z24 * z34 * c25 * c35 = z25 * z35 * c24 * c34)
    (E7 : z12 * z14 * c23 * c34 = z23 * z34 * c12 * c14)
    (E8 : z02 * z05 * c24 * c45 = z24 * z45 * c02 * c05)
    (E9 : z03 * z04 * c35 * c45 = z35 * z45 * c03 * c04)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z01 * z01 * z25 * z25 * c05 * c05 * c12 * c12 = z05 * z05 * z12 * z12 * c01 * c01 * c25 * c25 := by
  have hL : z01 * z01 * z02 * z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz02)) (nz02)) (nz03)) (nz04)) (nz13)) (nz14)) (nz15)) (nz23)) (nz24)) (nz24)) (nz25)) (nz25)) (nz25)) (nz34)) (nz34)) (nz35)) (nz35)) (nz45)) (nz45)) (nz45)) (nc02)) (nc02)) (nc03)) (nc04)) (nc05)) (nc05)) (nc12)) (nc12)) (nc13)) (nc14)) (nc15)) (nc23)) (nc24)) (nc24)) (nc25)) (nc34)) (nc34)) (nc35)) (nc35)) (nc45)) (nc45)) (nc45)
  have hLR : z01 * z01 * z02 * z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45 = z02 * z02 * z03 * z04 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c03 * c04 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45 := by
    linear_combination (z01 * z02 * z02 * z03 * z04 * z13 * z14 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45) * E1 + (z01 * z02 * z03 * z04 * z04 * z13 * z14 * z23 * z24 * z24 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c02 * c02 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c45 * c45) * E2 + (z03 * z03 * z04 * z04 * z13 * z14 * z23 * z24 * z24 * z25 * z25 * z34 * z34 * z35 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c02 * c02 * c02 * c05 * c05 * c12 * c12 * c14 * c15 * c15 * c24 * c24 * c25 * c25 * c34 * c34 * c35 * c45 * c45) * E3 + (z03 * z03 * z04 * z04 * z13 * z14 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c12 * c14 * c15 * c24 * c24 * c25 * c25 * c34 * c34 * c35 * c45) * E4 - (z03 * z03 * z04 * z04 * z13 * z15 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c13 * c14 * c15 * c24 * c24 * c25 * c34 * c34 * c34 * c35 * c45) * E5 - (z03 * z03 * z04 * z04 * z12 * z13 * z15 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c13 * c14 * c14 * c15 * c24 * c25 * c34 * c34 * c35 * c45 * c45) * E6 - (z03 * z03 * z04 * z04 * z12 * z13 * z15 * z23 * z23 * z24 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c12 * c13 * c14 * c14 * c15 * c25 * c25 * c34 * c35 * c35 * c45 * c45) * E6 - (z03 * z03 * z04 * z04 * z12 * z13 * z15 * z23 * z24 * z24 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c02 * c05 * c05 * c13 * c14 * c15 * c25 * c25 * c25 * c34 * c35 * c35 * c35 * c45 * c45) * E7 - (z03 * z03 * z04 * z04 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c02 * c05 * c13 * c14 * c15 * c23 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c35 * c45 * c45) * E8 - (z02 * z03 * z03 * z04 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * c01 * c01 * c02 * c02 * c13 * c14 * c15 * c23 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c35 * c45 * c45 * c45) * E8 + (z02 * z02 * z03 * z04 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z45 * z45 * c01 * c01 * c02 * c02 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45) * E9
  have hmono : z01 * z01 * z25 * z25 * c05 * c05 * c12 * c12 * (z02 * z02 * z03 * z04 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c01 * c01 * c02 * c02 * c03 * c04 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45) = z05 * z05 * z12 * z12 * c01 * c01 * c25 * c25 * (z01 * z01 * z02 * z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z25 * z34 * z34 * z35 * z35 * z45 * z45 * z45 * c02 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c34 * c34 * c35 * c35 * c45 * c45 * c45) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- **この枡の証人を持つ 6 点は一般の位置にない。**単因子が同じ `1⁹, 2, 2, 2, 4` の、もう一つの類（15 枡。証人集合は上と別）。位数 2 の共線形式は `(2;0,5), (1;2,3), (5;1,2)` で、上と同じ 3 本の捩れ形式（直角 2 本＋共円 1 本）で落ちる。 -/

theorem no_general_position_of_right_angles_and_cross_ratio' (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 1) (p 5) (p 0) (p 2) = 0)
    (hw3 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw4 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw5 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw9 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw10 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw12 : Psi (p 1) (p 3) (p 2) (p 4) = 0)
    (hw13 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : False := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have hcyc := hgp.2.2
  have hsq1 : ((toC (p 2) - toC (p 0)) * (barC (p 2) - barC (p 5))) ^ 2
      = ((barC (p 2) - barC (p 0)) * (toC (p 2) - toC (p 5))) ^ 2 := by
    linear_combination mixedAltAngle1
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 2)) by linear_combination (-1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw3)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr1 : qq (p 0) (p 5) (p 2) * cross (p 2) (p 0) (p 5) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq1
  have hc1 : cross (p 2) (p 0) (p 5) ≠ 0 := by
    have h0 : cross (p 0) (p 2) (p 5) ≠ 0 := by
      simpa [Collinear3] using hcol 0 2 5 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination -hx
  have ha1 : qq (p 0) (p 5) (p 2) = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact h
    · exact absurd h hc1
  have hsq2 : ((toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 2))) ^ 2
      = ((barC (p 5) - barC (p 1)) * (toC (p 5) - toC (p 2))) ^ 2 := by
    linear_combination mixedAltAngle2
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw9)
      (show (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 5)) = (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr2 : qq (p 1) (p 2) (p 5) * cross (p 5) (p 1) (p 2) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq2
  have hc2 : cross (p 5) (p 1) (p 2) ≠ 0 := by
    have h0 : cross (p 1) (p 2) (p 5) ≠ 0 := by
      simpa [Collinear3] using hcol 1 2 5 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination hx
  have ha2 : qq (p 1) (p 2) (p 5) = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact h
    · exact absurd h hc2
  have hs : cyclicValue (p 0) (p 2) (p 1) (p 5) ^ 2
      = cyclicValueBar (p 0) (p 2) (p 1) (p 5) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination mixedAltCross
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 0) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) * (barC (p 1) - barC (p 3)) * (barC (p 2) - barC (p 3)) = (toC (p 1) - toC (p 3)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw9)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw12)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hd : det4 (p 0) (p 2) (p 1) (p 5) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 5) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 5 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination -hx
  have hg := cyc_add_bar_eq_zero hs hd
  have d1 : sqdist (p 0) (p 2) + sqdist (p 2) (p 5) - sqdist (p 0) (p 5) = 0 := by
    simp only [sqdist, qq] at ha1 ⊢
    linear_combination 2 * ha1
  have d2 : sqdist (p 1) (p 5) + sqdist (p 2) (p 5) - sqdist (p 1) (p 2) = 0 := by
    simp only [sqdist, qq] at ha2 ⊢
    linear_combination 2 * ha2
  have h3 : sqdist (p 0) (p 1) * sqdist (p 2) (p 5) + sqdist (p 0) (p 5) * sqdist (p 1) (p 2) - sqdist (p 0) (p 2) * sqdist (p 1) (p 5) = 0 := by
    have h := congrArg Complex.re hg
    rw [re_cyclic_sum, Complex.zero_re, sqdist_comm (p 2) (p 1)] at h
    linear_combination h
  have hfin : sqdist (p 2) (p 5) * (sqdist (p 0) (p 1) + sqdist (p 0) (p 2) + sqdist (p 1) (p 2)) = 0 := by
    linear_combination (sqdist (p 1) (p 2)) * d1 + (sqdist (p 0) (p 2)) * d2 + h3
  have hp : 0 < sqdist (p 2) (p 5) * (sqdist (p 0) (p 1) + sqdist (p 0) (p 2) + sqdist (p 1) (p 2)) := by
    refine mul_pos (sqdist_pos (hne 2 5 (by decide))) ?_
    have t1 := sqdist_pos (hne 0 1 (by decide))
    have t2 := sqdist_nonneg (p 0) (p 2)
    have t3 := sqdist_nonneg (p 1) (p 2)
    linarith
  exact absurd hfin hp.ne'

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。 -/
theorem no_general_position_of_right_angles_and_cross_ratio_all' (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 1) (p 5) (p 0) (p 2) = 0)
    (hw2 : Psi (p 2) (p 4) (p 0) (p 3) = 0)
    (hw3 : Psi (p 1) (p 2) (p 0) (p 4) = 0)
    (hw4 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw5 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 4) (p 1) (p 3) = 0)
    (hw8 : Psi (p 2) (p 5) (p 1) (p 3) = 0)
    (hw9 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw10 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw12 : Psi (p 1) (p 3) (p 2) (p 4) = 0)
    (hw13 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : False :=
  no_general_position_of_right_angles_and_cross_ratio' p hgp hw1 hw3 hw4 hw5 hw6 hw9 hw10 hw11 hw12 hw13 hw14 hw15

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## The direction classes, in the shape of the census -/

/-! ### Class 16 -/

/-- The mask of class 16 (entry 15 of `censusRest`). -/
def maskK16 : Mask := 321425873218542288273672

/-- Class 16 is one of the thirty-four census representatives. -/
theorem maskK16_mem : maskK16 ∈ censusRest := by decide

/-- **Class 16, sharp form.**  No six points in general position support
the mask of class 16.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k16 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK16) : False := by
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
  have c26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hs 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  have c40 : Psi (p 2) (p 5) (p 1) (p 3) = 0 := by
    have h := hs 40 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 40 = ((1, 3), (2, 5)) from by decide)] at h
  have c47 : Psi (p 3) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 47 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 47 = ((1, 4), (3, 5)) from by decide)] at h
  have c52 : Psi (p 2) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 52 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 52 = ((1, 5), (2, 4)) from by decide)] at h
  have c59 : Psi (p 4) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 59 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 59 = ((2, 3), (4, 5)) from by decide)] at h
  have c63 : Psi (p 1) (p 3) (p 2) (p 4) = 0 := by
    have h := hs 63 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 63 = ((2, 4), (1, 3)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hs 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  exact no_general_position_of_right_angles_and_cross_ratio_all p hgp c3 c8 c15 c18 c26 c27 c30 c40 c47 c52 c59 c63 c68 c74 c78

/-- **Class 16.**  No six points in general position carry the mask of
class 16. -/
theorem not_carries_k16 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK16) : False :=
  not_supports_k16 p hgp (supports_of_carries hc)

/-! ### Class 17 -/

/-- The mask of class 17 (entry 16 of `censusRest`). -/
def maskK17 : Mask := 321425873218679727227136

/-- Class 17 is one of the thirty-four census representatives. -/
theorem maskK17_mem : maskK17 ∈ censusRest := by decide

/-- **Class 17, sharp form.**  No six points in general position support
the mask of class 17.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k17 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK17) : False := by
  have c8 : Psi (p 1) (p 5) (p 0) (p 2) = 0 := by
    have h := hs 8 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 8 = ((0, 2), (1, 5)) from by decide)] at h
  have c15 : Psi (p 2) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 15 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 15 = ((0, 3), (2, 4)) from by decide)] at h
  have c18 : Psi (p 1) (p 2) (p 0) (p 4) = 0 := by
    have h := hs 18 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 18 = ((0, 4), (1, 2)) from by decide)] at h
  have c26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hs 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  have c37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have c40 : Psi (p 2) (p 5) (p 1) (p 3) = 0 := by
    have h := hs 40 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 40 = ((1, 3), (2, 5)) from by decide)] at h
  have c47 : Psi (p 3) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 47 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 47 = ((1, 4), (3, 5)) from by decide)] at h
  have c52 : Psi (p 2) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 52 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 52 = ((1, 5), (2, 4)) from by decide)] at h
  have c59 : Psi (p 4) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 59 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 59 = ((2, 3), (4, 5)) from by decide)] at h
  have c63 : Psi (p 1) (p 3) (p 2) (p 4) = 0 := by
    have h := hs 63 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 63 = ((2, 4), (1, 3)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hs 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  exact no_general_position_of_right_angles_and_cross_ratio_all' p hgp c8 c15 c18 c26 c27 c30 c37 c40 c47 c52 c59 c63 c68 c74 c78

/-- **Class 17.**  No six points in general position carry the mask of
class 17. -/
theorem not_carries_k17 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK17) : False :=
  not_supports_k17 p hgp (supports_of_carries hc)



end QU4

end DistinctCircumradii

#print axioms DistinctCircumradii.QU4.eq_of_cert
#print axioms DistinctCircumradii.QU4.sqdist_nonneg
#print axioms DistinctCircumradii.QU4.qq_comm
#print axioms DistinctCircumradii.QU4.perp_poly
#print axioms DistinctCircumradii.QU4.im_cyclicValue
#print axioms DistinctCircumradii.QU4.cyclicValueBar_eq_conj
#print axioms DistinctCircumradii.QU4.cyc_add_bar_eq_zero
#print axioms DistinctCircumradii.QU4.no_four_points_of_two_imaginary_cross_ratios
#print axioms DistinctCircumradii.QU4.sqdist_comm
#print axioms DistinctCircumradii.QU4.sqdist_pos
#print axioms DistinctCircumradii.QU4.re_cyclic_sum
#print axioms DistinctCircumradii.QU4.mixedAngle1
#print axioms DistinctCircumradii.QU4.mixedAngle2
#print axioms DistinctCircumradii.QU4.mixedCross
#print axioms DistinctCircumradii.QU4.no_general_position_of_right_angles_and_cross_ratio
#print axioms DistinctCircumradii.QU4.no_general_position_of_right_angles_and_cross_ratio_all
#print axioms DistinctCircumradii.QU4.mixedAltAngle1
#print axioms DistinctCircumradii.QU4.mixedAltAngle2
#print axioms DistinctCircumradii.QU4.mixedAltCross
#print axioms DistinctCircumradii.QU4.no_general_position_of_right_angles_and_cross_ratio'
#print axioms DistinctCircumradii.QU4.no_general_position_of_right_angles_and_cross_ratio_all'
#print axioms DistinctCircumradii.QU4.cellPsi_eq
#print axioms DistinctCircumradii.QU4.maskK16_mem
#print axioms DistinctCircumradii.QU4.not_supports_k16
#print axioms DistinctCircumradii.QU4.not_carries_k16
#print axioms DistinctCircumradii.QU4.maskK17_mem
#print axioms DistinctCircumradii.QU4.not_supports_k17
#print axioms DistinctCircumradii.QU4.not_carries_k17
