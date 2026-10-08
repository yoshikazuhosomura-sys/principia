import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU5` の k23

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

set_option linter.unusedVariables false

namespace QU5

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

/-! ### 三つの交比 -/

/-- 格子の所属の証明書（枡 8 個・係数 [1, -1, 1, 1, 1, -1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共円形式 `F(p0, p4; p1, p2)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。`ring` は単項式しか見ない。 -/
theorem crossRatioPair1 {z01 z02 z03 z04 z12 z13 z14 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c12 c13 c14 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z01 * z12 * c04 * c24 = z04 * z24 * c01 * c12)
    (E2 : z02 * z25 * c04 * c45 = z04 * z45 * c02 * c25)
    (E3 : z01 * z03 * c12 * c23 = z12 * z23 * c01 * c03)
    (E4 : z12 * z24 * c13 * c34 = z13 * z34 * c12 * c24)
    (E5 : z13 * z35 * c14 * c45 = z14 * z45 * c13 * c35)
    (E6 : z02 * z03 * c24 * c34 = z24 * z34 * c02 * c03)
    (E7 : z12 * z14 * c25 * c45 = z25 * z45 * c12 * c14)
    (E8 : z23 * z24 * c35 * c45 = z35 * z45 * c23 * c24)
    (nz01 : z01 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z01 * z01 * z24 * z24 * c02 * c02 * c14 * c14 = z02 * z02 * z14 * z14 * c01 * c01 * c24 * c24 := by
  have hL : z01 * z01 * z03 * z04 * z12 * z12 * z13 * z23 * z24 * z24 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c02 * c03 * c04 * c12 * c12 * c13 * c14 * c14 * c23 * c24 * c25 * c34 * c35 * c45 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz03)) (nz04)) (nz12)) (nz12)) (nz13)) (nz23)) (nz24)) (nz24)) (nz24)) (nz25)) (nz34)) (nz35)) (nz45)) (nz45)) (nc02)) (nc02)) (nc03)) (nc04)) (nc12)) (nc12)) (nc13)) (nc14)) (nc14)) (nc23)) (nc24)) (nc25)) (nc34)) (nc35)) (nc45)) (nc45)
  have hLR : z01 * z01 * z03 * z04 * z12 * z12 * z13 * z23 * z24 * z24 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c02 * c03 * c04 * c12 * c12 * c13 * c14 * c14 * c23 * c24 * c25 * c34 * c35 * c45 * c45 = z02 * z02 * z03 * z04 * z12 * z12 * z13 * z14 * z14 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c01 * c01 * c03 * c04 * c12 * c12 * c13 * c23 * c24 * c24 * c24 * c25 * c34 * c35 * c45 * c45 := by
    linear_combination (z01 * z03 * z04 * z12 * z13 * z23 * z24 * z24 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c02 * c03 * c12 * c12 * c13 * c14 * c14 * c23 * c25 * c34 * c35 * c45 * c45) * E1 - (z01 * z03 * z04 * z12 * z13 * z23 * z24 * z24 * z24 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c12 * c12 * c12 * c13 * c14 * c14 * c23 * c34 * c35 * c45 * c45) * E2 + (z02 * z04 * z12 * z13 * z23 * z24 * z24 * z24 * z24 * z25 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c12 * c12 * c13 * c14 * c14 * c34 * c35 * c45 * c45 * c45) * E3 + (z02 * z04 * z12 * z13 * z23 * z23 * z24 * z24 * z24 * z25 * z25 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c03 * c04 * c12 * c12 * c14 * c14 * c35 * c45 * c45 * c45) * E4 + (z02 * z04 * z12 * z13 * z23 * z23 * z24 * z24 * z24 * z25 * z25 * z34 * z34 * z45 * c01 * c01 * c02 * c03 * c03 * c04 * c12 * c12 * c12 * c14 * c24 * c35 * c45 * c45) * E5 - (z02 * z04 * z12 * z13 * z14 * z23 * z23 * z24 * z24 * z25 * z25 * z34 * z45 * z45 * c01 * c01 * c03 * c04 * c12 * c12 * c12 * c13 * c14 * c24 * c35 * c35 * c45 * c45) * E6 - (z02 * z02 * z03 * z04 * z12 * z13 * z14 * z23 * z23 * z24 * z24 * z25 * z34 * z45 * c01 * c01 * c03 * c04 * c12 * c12 * c13 * c24 * c24 * c34 * c35 * c35 * c45 * c45) * E7 + (z02 * z02 * z03 * z04 * z12 * z12 * z13 * z14 * z14 * z23 * z24 * z25 * z34 * z45 * c01 * c01 * c03 * c04 * c12 * c12 * c13 * c24 * c24 * c25 * c34 * c35 * c45 * c45) * E8
  have hmono : z01 * z01 * z24 * z24 * c02 * c02 * c14 * c14 * (z02 * z02 * z03 * z04 * z12 * z12 * z13 * z14 * z14 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c01 * c01 * c03 * c04 * c12 * c12 * c13 * c23 * c24 * c24 * c24 * c25 * c34 * c35 * c45 * c45) = z02 * z02 * z14 * z14 * c01 * c01 * c24 * c24 * (z01 * z01 * z03 * z04 * z12 * z12 * z13 * z23 * z24 * z24 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c02 * c03 * c04 * c12 * c12 * c13 * c14 * c14 * c23 * c24 * c25 * c34 * c35 * c45 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 6 個・係数 [1, 1, 1, 1, -1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共円形式 `F(p0, p2; p1, p5)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。`ring` は単項式しか見ない。 -/
theorem crossRatioPair2 {z01 z02 z03 z04 z05 z12 z14 z23 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c14 c23 c25 c34 c35 c45 : ℂ}
    (E1 : z04 * z34 * c05 * c35 = z05 * z35 * c04 * c34)
    (E2 : z01 * z14 * c03 * c34 = z03 * z34 * c01 * c14)
    (E3 : z02 * z25 * c04 * c45 = z04 * z45 * c02 * c25)
    (E4 : z01 * z03 * c12 * c23 = z12 * z23 * c01 * c03)
    (E5 : z12 * z14 * c25 * c45 = z25 * z45 * c12 * c14)
    (E6 : z02 * z05 * c23 * c35 = z23 * z35 * c02 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z01 * z01 * z25 * z25 * c05 * c05 * c12 * c12 = z05 * z05 * z12 * z12 * c01 * c01 * c25 * c25 := by
  have hL : z01 * z01 * z02 * z03 * z04 * z14 * z23 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c14 * c23 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz02)) (nz03)) (nz04)) (nz14)) (nz23)) (nz25)) (nz25)) (nz34)) (nz35)) (nz45)) (nc02)) (nc03)) (nc04)) (nc05)) (nc05)) (nc12)) (nc12)) (nc14)) (nc23)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z01 * z02 * z03 * z04 * z14 * z23 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c14 * c23 * c34 * c35 * c45 = z02 * z03 * z04 * z05 * z05 * z12 * z12 * z14 * z23 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c04 * c14 * c23 * c25 * c25 * c34 * c35 * c45 := by
    linear_combination (z01 * z01 * z02 * z03 * z14 * z23 * z25 * z25 * z35 * z45 * c02 * c03 * c04 * c05 * c12 * c12 * c14 * c23 * c34 * c45) * E1 + (z01 * z02 * z03 * z05 * z23 * z25 * z25 * z35 * z35 * z45 * c02 * c04 * c04 * c05 * c12 * c12 * c14 * c23 * c34 * c45) * E2 + (z01 * z03 * z03 * z05 * z23 * z25 * z34 * z35 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c12 * c14 * c14 * c23 * c34) * E3 + (z03 * z04 * z05 * z23 * z25 * z34 * z35 * z35 * z45 * z45 * c01 * c02 * c02 * c04 * c05 * c12 * c14 * c14 * c25 * c34) * E4 - (z03 * z04 * z05 * z12 * z23 * z23 * z34 * z35 * z35 * z45 * c01 * c01 * c02 * c02 * c03 * c04 * c05 * c14 * c25 * c34) * E5 - (z03 * z04 * z05 * z12 * z12 * z14 * z23 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c04 * c14 * c25 * c25 * c34 * c45) * E6
  have hmono : z01 * z01 * z25 * z25 * c05 * c05 * c12 * c12 * (z02 * z03 * z04 * z05 * z05 * z12 * z12 * z14 * z23 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c04 * c14 * c23 * c25 * c25 * c34 * c35 * c45) = z05 * z05 * z12 * z12 * c01 * c01 * c25 * c25 * (z01 * z01 * z02 * z03 * z04 * z14 * z23 * z25 * z25 * z34 * z35 * z45 * c02 * c03 * c04 * c05 * c05 * c12 * c12 * c14 * c23 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 8 個・係数 [1, 1, -1, 1, 1, -1, -1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共円形式 `F(p0, p5; p1, p4)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。`ring` は単項式しか見ない。 -/
theorem crossRatioPair3 {z01 z02 z03 z04 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z12 * c05 * c15 = z05 * z15 * c02 * c12)
    (E2 : z01 * z12 * c04 * c24 = z04 * z24 * c01 * c12)
    (E3 : z04 * z34 * c05 * c35 = z05 * z35 * c04 * c34)
    (E4 : z13 * z23 * c15 * c25 = z15 * z25 * c13 * c23)
    (E5 : z01 * z03 * c12 * c23 = z12 * z23 * c01 * c03)
    (E6 : z13 * z35 * c14 * c45 = z14 * z45 * c13 * c35)
    (E7 : z02 * z03 * c24 * c34 = z24 * z34 * c02 * c03)
    (E8 : z12 * z14 * c25 * c45 = z25 * z45 * c12 * c14)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
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
    : z01 * z01 * z45 * z45 * c04 * c04 * c15 * c15 = z04 * z04 * z15 * z15 * c01 * c01 * c45 * c45 := by
  have hL : z01 * z01 * z02 * z03 * z05 * z12 * z12 * z13 * z14 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c03 * c04 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c15 * c23 * c24 * c25 * c34 * c35 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz02)) (nz03)) (nz05)) (nz12)) (nz12)) (nz13)) (nz14)) (nz23)) (nz24)) (nz25)) (nz34)) (nz35)) (nz45)) (nz45)) (nc02)) (nc03)) (nc04)) (nc04)) (nc05)) (nc12)) (nc12)) (nc13)) (nc14)) (nc15)) (nc15)) (nc23)) (nc24)) (nc25)) (nc34)) (nc35)
  have hLR : z01 * z01 * z02 * z03 * z05 * z12 * z12 * z13 * z14 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c03 * c04 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c15 * c23 * c24 * c25 * c34 * c35 = z02 * z03 * z04 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z15 * z23 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c03 * c05 * c12 * c12 * c13 * c14 * c23 * c24 * c25 * c34 * c35 * c45 * c45 := by
    linear_combination (z01 * z01 * z03 * z05 * z12 * z13 * z14 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c03 * c04 * c04 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35) * E1 + (z01 * z03 * z05 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c02 * c03 * c04 * c12 * c12 * c12 * c13 * c14 * c15 * c23 * c25 * c34 * c35) * E2 - (z01 * z03 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z34 * z45 * z45 * c01 * c02 * c02 * c03 * c12 * c12 * c12 * c12 * c13 * c14 * c15 * c23 * c25 * c35) * E3 + (z01 * z03 * z04 * z04 * z05 * z14 * z15 * z24 * z24 * z25 * z34 * z34 * z45 * z45 * c01 * c02 * c02 * c03 * c05 * c12 * c12 * c12 * c12 * c13 * c14 * c23 * c35 * c35) * E4 + (z04 * z04 * z05 * z14 * z15 * z15 * z24 * z24 * z25 * z25 * z34 * z34 * z45 * z45 * c01 * c02 * c02 * c03 * c05 * c12 * c12 * c12 * c13 * c13 * c14 * c23 * c35 * c35) * E5 - (z04 * z04 * z05 * z12 * z15 * z15 * z23 * z24 * z24 * z25 * z25 * z34 * z34 * z45 * c01 * c01 * c02 * c02 * c03 * c03 * c05 * c12 * c12 * c12 * c13 * c14 * c23 * c35) * E6 - (z04 * z04 * z05 * z12 * z13 * z15 * z15 * z23 * z24 * z25 * z25 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c05 * c12 * c12 * c12 * c13 * c14 * c14 * c23 * c35 * c45) * E7 - (z02 * z03 * z04 * z04 * z05 * z12 * z13 * z15 * z15 * z23 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c03 * c05 * c12 * c12 * c13 * c14 * c23 * c24 * c34 * c35 * c45) * E8
  have hmono : z01 * z01 * z45 * z45 * c04 * c04 * c15 * c15 * (z02 * z03 * z04 * z04 * z05 * z12 * z12 * z13 * z14 * z15 * z15 * z23 * z24 * z25 * z34 * z35 * c01 * c01 * c02 * c03 * c05 * c12 * c12 * c13 * c14 * c23 * c24 * c25 * c34 * c35 * c45 * c45) = z04 * z04 * z15 * z15 * c01 * c01 * c45 * c45 * (z01 * z01 * z02 * z03 * z05 * z12 * z12 * z13 * z14 * z23 * z24 * z25 * z34 * z35 * z45 * z45 * c02 * c03 * c04 * c04 * c05 * c12 * c12 * c13 * c14 * c15 * c15 * c23 * c24 * c25 * c34 * c35) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- **この枡の証人を持つ 6 点は一般の位置にない。**単因子が `1⁹, 2, 2, 4, 4` の類（15 枡）。位数 2 の共線形式は 1 本しかないが、位数 2 の共円形式が 7 本ある。使うのは 4 点組 `{p₀,p₁,p₂,p₄}`・`{p₀,p₁,p₂,p₅}`・`{p₀,p₁,p₄,p₅}` の組分け `(0,4;1,2)`・`(0,2;1,5)`・`(0,5;1,4)` の 3 本である。 -/

theorem no_general_position_of_three_imaginary_cross_ratios (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw2 : Psi (p 1) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 4) (p 5) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 3) (p 0) (p 4) = 0)
    (hw5 : Psi (p 2) (p 4) (p 0) (p 5) = 0)
    (hw6 : Psi (p 3) (p 5) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 2) (p 1) (p 3) = 0)
    (hw9 : Psi (p 2) (p 3) (p 1) (p 4) = 0)
    (hw10 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 0) (p 4) (p 2) (p 3) = 0)
    (hw12 : Psi (p 1) (p 5) (p 2) (p 4) = 0)
    (hw13 : Psi (p 0) (p 3) (p 2) (p 5) = 0)
    (hw14 : Psi (p 2) (p 5) (p 3) (p 4) = 0)
    : False := by
  have hne := hgp.1
  have hcyc := hgp.2.2
  have hs1 : cyclicValue (p 0) (p 4) (p 1) (p 2) ^ 2
      = cyclicValueBar (p 0) (p 4) (p 1) (p 2) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioPair1
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 2)) by linear_combination (-1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 0) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 3)) = (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw9)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 3)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw12)
      (show (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hd1 : det4 (p 0) (p 4) (p 1) (p 2) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 4) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 4 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination hx
  have hg1 := cyc_add_bar_eq_zero hs1 hd1
  have hq1 : sqdist (p 0) (p 1) * sqdist (p 2) (p 4) + sqdist (p 0) (p 2) * sqdist (p 1) (p 4) - sqdist (p 0) (p 4) * sqdist (p 1) (p 2) = 0 := by
    have h := congrArg Complex.re hg1
    rw [re_cyclic_sum, Complex.zero_re, sqdist_comm (p 4) (p 1), sqdist_comm (p 4) (p 2)] at h
    linear_combination h
  have hs2 : cyclicValue (p 0) (p 2) (p 1) (p 5) ^ 2
      = cyclicValueBar (p 0) (p 2) (p 1) (p 5) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioPair2
      (show (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 0) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 3)) = (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw12)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hd2 : det4 (p 0) (p 2) (p 1) (p 5) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 5) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 5 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination -hx
  have hg2 := cyc_add_bar_eq_zero hs2 hd2
  have hq2 : sqdist (p 0) (p 1) * sqdist (p 2) (p 5) + sqdist (p 0) (p 5) * sqdist (p 1) (p 2) - sqdist (p 0) (p 2) * sqdist (p 1) (p 5) = 0 := by
    have h := congrArg Complex.re hg2
    rw [re_cyclic_sum, Complex.zero_re, sqdist_comm (p 2) (p 1)] at h
    linear_combination h
  have hs3 : cyclicValue (p 0) (p 5) (p 1) (p 4) ^ 2
      = cyclicValueBar (p 0) (p 5) (p 1) (p 4) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination crossRatioPair3
      (show (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 2)) by linear_combination (-1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw3)
      (show (toC (p 1) - toC (p 3)) * (toC (p 2) - toC (p 3)) * (barC (p 1) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 2) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 3)) = (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 3)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw12)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
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
  have hd3 : det4 (p 0) (p 5) (p 1) (p 4) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 4) (p 5) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 4 5 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination hx
  have hg3 := cyc_add_bar_eq_zero hs3 hd3
  have hq3 : sqdist (p 0) (p 1) * sqdist (p 4) (p 5) + sqdist (p 0) (p 4) * sqdist (p 1) (p 5) - sqdist (p 0) (p 5) * sqdist (p 1) (p 4) = 0 := by
    have h := congrArg Complex.re hg3
    rw [re_cyclic_sum, Complex.zero_re, sqdist_comm (p 5) (p 1), sqdist_comm (p 5) (p 4)] at h
    linear_combination h
  have hfin : sqdist (p 0) (p 1) * sqdist (p 4) (p 5) * (sqdist (p 0) (p 5) * sqdist (p 2) (p 4) + sqdist (p 0) (p 4) * sqdist (p 2) (p 5) + sqdist (p 0) (p 2) * sqdist (p 4) (p 5)) = 0 := by
    linear_combination (sqdist (p 0) (p 5) * sqdist (p 4) (p 5)) * hq1 + (sqdist (p 0) (p 4) * sqdist (p 4) (p 5)) * hq2 + (sqdist (p 0) (p 2) * sqdist (p 4) (p 5)) * hq3
  have hp : 0 < sqdist (p 0) (p 1) * sqdist (p 4) (p 5) * (sqdist (p 0) (p 5) * sqdist (p 2) (p 4) + sqdist (p 0) (p 4) * sqdist (p 2) (p 5) + sqdist (p 0) (p 2) * sqdist (p 4) (p 5)) := by
    refine mul_pos (mul_pos (sqdist_pos (hne 0 1 (by decide))) (sqdist_pos (hne 4 5 (by decide)))) ?_
    have i1 := mul_pos (sqdist_pos (hne 0 5 (by decide))) (sqdist_pos (hne 2 4 (by decide)))
    have i2 := mul_pos (sqdist_pos (hne 0 4 (by decide))) (sqdist_pos (hne 2 5 (by decide)))
    have i3 := mul_pos (sqdist_pos (hne 0 2 (by decide))) (sqdist_pos (hne 4 5 (by decide)))
    linarith
  exact absurd hfin hp.ne'

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。 -/
theorem no_general_position_of_three_imaginary_cross_ratios_all (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw2 : Psi (p 1) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 4) (p 5) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 3) (p 0) (p 4) = 0)
    (hw5 : Psi (p 2) (p 4) (p 0) (p 5) = 0)
    (hw6 : Psi (p 3) (p 5) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 2) (p 1) (p 3) = 0)
    (hw8 : Psi (p 0) (p 5) (p 1) (p 4) = 0)
    (hw9 : Psi (p 2) (p 3) (p 1) (p 4) = 0)
    (hw10 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 0) (p 4) (p 2) (p 3) = 0)
    (hw12 : Psi (p 1) (p 5) (p 2) (p 4) = 0)
    (hw13 : Psi (p 0) (p 3) (p 2) (p 5) = 0)
    (hw14 : Psi (p 2) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : False :=
  no_general_position_of_three_imaginary_cross_ratios p hgp hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw9 hw10 hw11 hw12 hw13 hw14

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## The direction class, in the shape of the census -/

/-! ### Class 23 -/

/-- The mask of class 23 (entry 22 of `censusRest`). -/
def maskK23 : Mask := 453513248141008326754436

/-- Class 23 is one of the thirty-four census representatives. -/
theorem maskK23_mem : maskK23 ∈ censusRest := by decide

/-- **Class 23, sharp form.**  No six points in general position support
the mask of class 23.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k23 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK23) : False := by
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have c7 : Psi (p 1) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 7 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 7 = ((0, 2), (1, 4)) from by decide)] at h
  have c17 : Psi (p 4) (p 5) (p 0) (p 3) = 0 := by
    have h := hs 17 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 17 = ((0, 3), (4, 5)) from by decide)] at h
  have c19 : Psi (p 1) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 19 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 19 = ((0, 4), (1, 3)) from by decide)] at h
  have c28 : Psi (p 2) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 28 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 28 = ((0, 5), (2, 4)) from by decide)] at h
  have c34 : Psi (p 3) (p 5) (p 1) (p 2) = 0 := by
    have h := hs 34 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 34 = ((1, 2), (3, 5)) from by decide)] at h
  have c36 : Psi (p 0) (p 2) (p 1) (p 3) = 0 := by
    have h := hs 36 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 36 = ((1, 3), (0, 2)) from by decide)] at h
  have c44 : Psi (p 0) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 44 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 44 = ((1, 4), (0, 5)) from by decide)] at h
  have c45 : Psi (p 2) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 45 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 45 = ((1, 4), (2, 3)) from by decide)] at h
  have c53 : Psi (p 3) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 53 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 53 = ((1, 5), (3, 4)) from by decide)] at h
  have c55 : Psi (p 0) (p 4) (p 2) (p 3) = 0 := by
    have h := hs 55 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 55 = ((2, 3), (0, 4)) from by decide)] at h
  have c64 : Psi (p 1) (p 5) (p 2) (p 4) = 0 := by
    have h := hs 64 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 64 = ((2, 4), (1, 5)) from by decide)] at h
  have c67 : Psi (p 0) (p 3) (p 2) (p 5) = 0 := by
    have h := hs 67 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 67 = ((2, 5), (0, 3)) from by decide)] at h
  have c77 : Psi (p 2) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 77 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 77 = ((3, 4), (2, 5)) from by decide)] at h
  have c78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hs 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  exact no_general_position_of_three_imaginary_cross_ratios_all p hgp c2 c7 c17 c19 c28 c34 c36 c44 c45 c53 c55 c64 c67 c77 c78

/-- **Class 23.**  No six points in general position carry the mask of
class 23. -/
theorem not_carries_k23 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK23) : False :=
  not_supports_k23 p hgp (supports_of_carries hc)



end QU5

end DistinctCircumradii

#print axioms DistinctCircumradii.QU5.eq_of_cert
#print axioms DistinctCircumradii.QU5.sqdist_nonneg
#print axioms DistinctCircumradii.QU5.qq_comm
#print axioms DistinctCircumradii.QU5.perp_poly
#print axioms DistinctCircumradii.QU5.im_cyclicValue
#print axioms DistinctCircumradii.QU5.cyclicValueBar_eq_conj
#print axioms DistinctCircumradii.QU5.cyc_add_bar_eq_zero
#print axioms DistinctCircumradii.QU5.no_four_points_of_two_imaginary_cross_ratios
#print axioms DistinctCircumradii.QU5.sqdist_comm
#print axioms DistinctCircumradii.QU5.sqdist_pos
#print axioms DistinctCircumradii.QU5.re_cyclic_sum
#print axioms DistinctCircumradii.QU5.crossRatioPair1
#print axioms DistinctCircumradii.QU5.crossRatioPair2
#print axioms DistinctCircumradii.QU5.crossRatioPair3
#print axioms DistinctCircumradii.QU5.no_general_position_of_three_imaginary_cross_ratios
#print axioms DistinctCircumradii.QU5.no_general_position_of_three_imaginary_cross_ratios_all
#print axioms DistinctCircumradii.QU5.cellPsi_eq
#print axioms DistinctCircumradii.QU5.maskK23_mem
#print axioms DistinctCircumradii.QU5.not_supports_k23
#print axioms DistinctCircumradii.QU5.not_carries_k23
