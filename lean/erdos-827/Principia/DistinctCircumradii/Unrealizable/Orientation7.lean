import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU7` の k21

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QU7

/-- A square equality splits into two signs.  This is the whole of "the class
has order two, so the branch value is `± 1`". -/
theorem sq_split {A B : ℂ} (h : A ^ 2 = B ^ 2) : A = B ∨ A = -B := by
  have h0 : (A - B) * (A + B) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (by linear_combination h1)

/-- `z = - conj z` says exactly that the real part vanishes. -/
theorem re_eq_zero_of_eq_neg_conj {z : ℂ} (h : z = -(starRingEnd ℂ) z) : z.re = 0 := by
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at this
  linarith

/-- `z = conj z` says exactly that the imaginary part vanishes. -/
theorem im_eq_zero_of_eq_conj {z : ℂ} (h : z = (starRingEnd ℂ) z) : z.im = 0 := by
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-! ### Collinearity atoms and the distance bridge

`atom a b c = (p_a - p_b) * conj (p_a - p_c)`: its real part is the inner
product at `a`, its imaginary part is minus the cross product.  So `2 * Re` is
the law-of-cosines expression `x2`, and a *product of two* imaginary parts is a
`2 × 2` determinant of inner products -- a distance polynomial, although a
single imaginary part is not. -/

/-- The atom. -/
def atom (a b c : Pt) : ℂ := (toC a - toC b) * (barC a - barC c)

/-- Twice the inner product at `a`, as a distance polynomial. -/
def x2 (a b c : Pt) : ℝ := sqdist a b + sqdist a c - sqdist b c

/-- `2 ⟪p - q, r - s⟫` as a distance polynomial. -/
def dd (p q r s : Pt) : ℝ := sqdist p s + sqdist q r - sqdist p r - sqdist q s

theorem re_atom (a b c : Pt) : 2 * (atom a b c).re = x2 a b c := by
  simp only [atom, x2, sqdist, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

theorem im_atom (a b c : Pt) : (atom a b c).im = - cross a b c := by
  simp only [atom, cross, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

/-- **A product of two imaginary parts is a distance polynomial.**  In the plane
`(u × v) * (x × y) = ⟪u, x⟫ ⟪v, y⟫ - ⟪u, y⟫ ⟪v, x⟫`. -/
theorem im_pair (a b c u v w : Pt) :
    4 * ((atom a b c).im * (atom u v w).im)
      = dd b a v u * dd c a w u - dd b a w u * dd c a v u := by
  simp only [atom, dd, sqdist, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

/-- **The real part of a two-atom product is a distance polynomial of degree
two.**  This is the generator a branch with value `-1` contributes. -/
theorem re_atom_pair (a b c u v w : Pt) :
    4 * (atom a b c * atom u v w).re
      = x2 a b c * x2 u v w - (dd b a v u * dd c a w u - dd b a w u * dd c a v u) := by
  simp only [atom, x2, dd, sqdist, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-- Squared distances of distinct points are positive. -/
theorem sqdist_pos {a b : Pt} (h : a ≠ b) : 0 < sqdist a b := by
  have h0 : (0:ℝ) ≤ sqdist a b := by simp only [sqdist]; positivity
  rcases lt_or_eq_of_le h0 with h1 | h1
  · exact h1
  · exact absurd (eq_of_sqdist_eq_zero h1.symm) h


/-! ### Reading a degeneracy class at a *translated* representative

`atomb` is the conjugate atom, written without `conj` so that `ring` can use it. -/

/-- The conjugate atom. -/
def atomb (a b c : Pt) : ℂ := (barC a - barC b) * (toC a - toC c)

theorem atomb_eq_conj (a b c : Pt) : atomb a b c = (starRingEnd ℂ) (atom a b c) := by
  rw [atom, atomb, map_mul, map_sub, map_sub, ← barC_eq_conj, ← barC_eq_conj]
  rw [show (starRingEnd ℂ) (barC a) = toC a from by
        refine Complex.ext_iff.mpr ⟨by simp, by simp⟩,
    show (starRingEnd ℂ) (barC c) = toC c from by
        refine Complex.ext_iff.mpr ⟨by simp, by simp⟩]

/-- `x2` is twice the inner product at the apex. -/
theorem x2_eq_two_qq (a b c : Pt) : x2 a b c = 2 * qq b c a := by
  simp only [x2, qq, sqdist]; ring

/-- A vanishing real part turns the atom into minus its conjugate. -/
theorem atom_add_atomb_eq_zero {a b c : Pt} (h : qq b c a = 0) :
    atom a b c + atomb a b c = 0 := by
  simp only [qq] at h
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [atom, atomb, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
      toC_re, toC_im, barC_re, barC_im]
  · linarith
  · ring

/-! ### 証明書の受け皿と、直角の距離読み -/

/-- 格子の証明書が作る形。`L = R`（証人条件の積）と `N * R = D * L`（単項式の恒等式）
から `N = D` が出る。`N`, `D` は目標の形式に対応する単項式で、`L`, `R` は
証人条件を掛け合わせた単項式である。 -/
theorem eq_of_cert {N D L R : ℂ} (hLR : L = R) (hmono : N * R = D * L) (hL : L ≠ 0) :
    N = D := by
  rw [← hLR] at hmono
  exact mul_right_cancel₀ hL hmono

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

/-- 2 乗距離は対称。 -/
theorem sqdist_comm (a b : Pt) : sqdist a b = sqdist b a := by
  simp only [sqdist]; ring

/-- **共円形式の 2 乗距離での読み**。`P - Q + R = 0` から
`|P| ^ 2 = |Q| ^ 2 + |R| ^ 2` になるのと同じ式である。 -/
theorem re_cyclic_sum (u v c d : Pt) :
    (cyclicValue u v c d + cyclicValueBar u v c d).re
      = sqdist u c * sqdist v d + sqdist u d * sqdist v c - sqdist u v * sqdist c d := by
  simp only [cyclicValue, cyclicValueBar, sqdist, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-- 同じ点の 2 乗距離は 0。 -/
theorem sqdist_self (a : Pt) : sqdist a a = 0 := by
  simp only [sqdist]; ring

/-- 原子は共役原子の共役である（`atomb_eq_conj` の反対側）。 -/
theorem atom_eq_conj_atomb (a b c : Pt) : atom a b c = (starRingEnd ℂ) (atomb a b c) := by
  rw [atomb_eq_conj]; simp

/-- 共役原子の積は、原子の積の共役である。 -/
theorem atomb_mul_atomb_eq_conj (a b c u v w : Pt) :
    atomb a b c * atomb u v w = (starRingEnd ℂ) (atom a b c * atom u v w) := by
  rw [map_mul, ← atomb_eq_conj, ← atomb_eq_conj]

/-- 片方だけ共役にした積も、向きを入れ替えた積の共役である。 -/
theorem atomb_mul_atom_eq_conj (a b c u v w : Pt) :
    atomb a b c * atom u v w = (starRingEnd ℂ) (atom a b c * atomb u v w) := by
  rw [map_mul, ← atomb_eq_conj, ← atom_eq_conj_atomb]

/-- `z + conj z = 0` は「実部が 0」である。 -/
theorem re_zero_of_sum {z w : ℂ} (hw : w = (starRingEnd ℂ) z) (h : z + w = 0) : z.re = 0 := by
  rw [hw] at h
  have hh := congrArg Complex.re h
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hh
  linarith

/-- **片方だけ共役にした二原子の積の実部も 2 乗距離の 2 次式である。**
`Im (conj A) = - Im A` なので、`re_atom_pair` の第二項の符号だけが変わる。 -/
theorem re_atom_atomb (a b c u v w : Pt) :
    4 * (atom a b c * atomb u v w).re
      = x2 a b c * x2 u v w + (dd b a v u * dd c a w u - dd b a w u * dd c a v u) := by
  simp only [atom, atomb, x2, dd, sqdist, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-- 格子の証書 `2 (e15 - e25) in L(S)` を、15 本の差とその共役を抽象の複素変数に置き換えて書いたもの。`E1 …` は枡の証人条件で、結論は共線形式 `COL(5; 1, 2)` の2 倍が格子に入ることの読み、すなわち平方の等式である。`ring` は単項式しか見ない。 -/
theorem rightAnglePairClass {z02 z03 z05 z13 z15 z24 z25 z34 z35 z45 c02 c03 c05 c13 c15 c24 c25 c34 c35 c45 : ℂ}
    (E1 : c03 * c35 * z02 * z25 = c02 * c25 * z03 * z35)
    (E2 : c15 * c45 * z13 * z34 = c13 * c34 * z15 * z45)
    (E3 : c25 * c35 * z24 * z34 = c24 * c34 * z25 * z35)
    (E4 : c24 * c45 * z02 * z05 = c02 * c05 * z24 * z45)
    (E5 : c13 * c15 * z03 * z05 = c03 * c05 * z13 * z15)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    : c25 ^ 2 * z15 ^ 2 = c15 ^ 2 * z25 ^ 2 := by
  have hL : c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 * z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc02) (nc03)) (nc05)) (nc13)) (nc24)) (nc25)) (nc25)) (nc34)) (nc35)) (nc45)) (nz02)) (nz03)) (nz05)) (nz13)) (nz15)) (nz15)) (nz24)) (nz34)) (nz35)) (nz45)
  have hLR : c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 * z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45 = c02 * c03 * c05 * c13 * c15 * c15 * c24 * c34 * c35 * c45 * z02 * z03 * z05 * z13 * z24 * z25 * z25 * z34 * z35 * z45 := by
    linear_combination (-1 * (c03 * c05 * c13 * c24 * c25 * c34 * c35 * c45 * z02 * z05 * z13 * z15 ^ 2 * z24 * z34 * z45)) * E1 + (-1 * (c03 ^ 2 * c05 * c24 * c25 * c35 ^ 2 * c45 * z02 ^ 2 * z05 * z13 * z15 * z24 * z25 * z34)) * E2 + (c03 ^ 2 * c05 * c15 * c24 * c35 * c45 ^ 2 * z02 ^ 2 * z05 * z13 ^ 2 * z15 * z25 * z34) * E3 + (c03 ^ 2 * c05 * c15 * c24 * c34 * c35 * c45 * z02 * z13 ^ 2 * z15 * z25 ^ 2 * z34 * z35) * E4 + (-1 * (c02 * c03 * c05 * c15 * c24 * c34 * c35 * c45 * z02 * z13 * z24 * z25 ^ 2 * z34 * z35 * z45)) * E5
  have hmono : c25 ^ 2 * z15 ^ 2 * (c02 * c03 * c05 * c13 * c15 * c15 * c24 * c34 * c35 * c45 * z02 * z03 * z05 * z13 * z24 * z25 * z25 * z34 * z35 * z45) = c15 ^ 2 * z25 ^ 2 * (c02 * c03 * c05 * c13 * c24 * c25 * c25 * c34 * c35 * c45 * z02 * z03 * z05 * z13 * z15 * z15 * z24 * z34 * z35 * z45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の証書 `2 (e01 - e05 - e12 + e25) in L(S)` を同じように書いたもの。結論は共円形式 `F(p0, p2; p1, p5)` の 2 倍が格子に入ることの読み、すなわち `cyclicValue ^ 2 = cyclicValueBar ^ 2` にあたる等式である。 -/
theorem crossRatioPairClass {z01 z02 z03 z04 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : c05 * c15 * z02 * z12 = c02 * c12 * z05 * z15)
    (E2 : c04 * c24 * z03 * z23 = c03 * c23 * z04 * z24)
    (E3 : c05 * c45 * z01 * z14 = c01 * c14 * z05 * z45)
    (E4 : c03 * c35 * z02 * z25 = c02 * c25 * z03 * z35)
    (E5 : c13 * c23 * z01 * z02 = c01 * c02 * z13 * z23)
    (E6 : c15 * c45 * z13 * z34 = c13 * c34 * z15 * z45)
    (E7 : c25 * c35 * z24 * z34 = c24 * c34 * z25 * z35)
    (E8 : c12 * c14 * z02 * z04 = c02 * c04 * z12 * z14)
    (E9 : c24 * c45 * z02 * z05 = c02 * c05 * z24 * z45)
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
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
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
    (nz45 : z45 ≠ 0)
    : c05 ^ 2 * c12 ^ 2 * z01 ^ 2 * z25 ^ 2 = c01 ^ 2 * c25 ^ 2 * z05 ^ 2 * z12 ^ 2 := by
  have hL : c02 * c02 * c03 * c04 * c05 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c34 * c35 * c45 * c45 * z01 * z01 * z02 * z02 * z03 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z45 * z45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc02) (nc02)) (nc03)) (nc04)) (nc05)) (nc05)) (nc05)) (nc12)) (nc12)) (nc13)) (nc14)) (nc15)) (nc23)) (nc24)) (nc24)) (nc34)) (nc35)) (nc45)) (nc45)) (nz01)) (nz01)) (nz02)) (nz02)) (nz03)) (nz04)) (nz05)) (nz13)) (nz14)) (nz15)) (nz23)) (nz24)) (nz24)) (nz25)) (nz25)) (nz34)) (nz35)) (nz45)) (nz45)
  have hLR : c02 * c02 * c03 * c04 * c05 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c34 * c35 * c45 * c45 * z01 * z01 * z02 * z02 * z03 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z45 * z45 = c01 * c01 * c02 * c02 * c03 * c04 * c05 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c34 * c35 * c45 * c45 * z02 * z02 * z03 * z04 * z05 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z34 * z35 * z45 * z45 := by
    linear_combination (-1 * (c02 * c03 * c04 * c05 ^ 3 * c12 * c13 * c14 * c15 * c23 * c24 ^ 2 * c34 * c35 * c45 ^ 2 * z01 ^ 2 * z02 ^ 2 * z03 * z04 * z13 * z14 * z23 * z24 ^ 2 * z25 ^ 2 * z34 * z35 * z45 ^ 2)) * E1 + (c02 * c03 * c05 ^ 4 * c12 * c13 * c14 * c15 ^ 2 * c23 * c24 * c34 * c35 * c45 ^ 2 * z01 ^ 2 * z02 ^ 3 * z04 * z12 * z13 * z14 * z24 ^ 2 * z25 ^ 2 * z34 * z35 * z45 ^ 2) * E2 + (c02 * c03 ^ 2 * c05 ^ 3 * c12 * c13 * c14 * c15 ^ 2 * c23 ^ 2 * c24 * c34 * c35 * c45 * z01 * z02 ^ 3 * z04 ^ 2 * z12 * z13 * z24 ^ 3 * z25 ^ 2 * z34 * z35 * z45 ^ 2) * E3 + (c01 * c02 * c03 * c05 ^ 3 * c12 * c13 * c14 ^ 2 * c15 ^ 2 * c23 ^ 2 * c24 * c34 * c45 * z01 * z02 ^ 2 * z04 ^ 2 * z05 * z12 * z13 * z24 ^ 3 * z25 * z34 * z35 * z45 ^ 3) * E4 + (c01 * c02 ^ 2 * c03 * c05 ^ 3 * c12 * c14 ^ 2 * c15 ^ 2 * c23 * c24 * c25 * c34 * c45 * z02 * z03 * z04 ^ 2 * z05 * z12 * z13 * z24 ^ 3 * z25 * z34 * z35 ^ 2 * z45 ^ 3) * E5 + (c01 ^ 2 * c02 ^ 3 * c03 * c05 ^ 3 * c12 * c14 ^ 2 * c15 * c23 * c24 * c25 * c34 * z02 * z03 * z04 ^ 2 * z05 * z12 * z13 * z23 * z24 ^ 3 * z25 * z35 ^ 2 * z45 ^ 3) * E6 + (-1 * (c01 ^ 2 * c02 ^ 3 * c03 * c05 ^ 3 * c12 * c13 * c14 ^ 2 * c15 * c23 * c25 * c34 * z02 * z03 * z04 ^ 2 * z05 * z12 * z13 * z15 * z23 * z24 ^ 3 * z35 * z45 ^ 4)) * E7 + (c01 ^ 2 * c02 ^ 3 * c03 * c05 ^ 3 * c13 * c14 * c15 * c23 * c25 ^ 2 * c34 * c35 * z03 * z04 * z05 * z12 * z13 * z15 * z23 * z24 ^ 4 * z34 * z35 * z45 ^ 4) * E8 + (-1 * (c01 ^ 2 * c02 ^ 3 * c03 * c04 * c05 ^ 2 * c13 * c14 * c15 * c23 * c25 ^ 2 * c34 * c35 * z03 * z04 * z05 * z12 ^ 2 * z13 * z14 * z15 * z23 * z24 ^ 3 * z34 * z35 * z45 ^ 3) + -1 * (c01 ^ 2 * c02 ^ 2 * c03 * c04 * c05 * c13 * c14 * c15 * c23 * c24 * c25 ^ 2 * c34 * c35 * c45 * z02 * z03 * z04 * z05 ^ 2 * z12 ^ 2 * z13 * z14 * z15 * z23 * z24 ^ 2 * z34 * z35 * z45 ^ 2)) * E9
  have hmono : c05 ^ 2 * c12 ^ 2 * z01 ^ 2 * z25 ^ 2 * (c01 * c01 * c02 * c02 * c03 * c04 * c05 * c13 * c14 * c15 * c23 * c24 * c24 * c25 * c25 * c34 * c35 * c45 * c45 * z02 * z02 * z03 * z04 * z05 * z05 * z05 * z12 * z12 * z13 * z14 * z15 * z23 * z24 * z24 * z34 * z35 * z45 * z45) = c01 ^ 2 * c25 ^ 2 * z05 ^ 2 * z12 ^ 2 * (c02 * c02 * c03 * c04 * c05 * c05 * c05 * c12 * c12 * c13 * c14 * c15 * c23 * c24 * c24 * c34 * c35 * c45 * c45 * z01 * z01 * z02 * z02 * z03 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z24 * z25 * z25 * z34 * z35 * z45 * z45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 生成元 ((5, 1, 2, -1),)：退化 RIGHT・枡の歩数 0・掛けた単項式の次数 0。 -/
theorem translated_class_21_01 {z15 z25 c15 c25 : ℂ}
    (hd : c25 * z15 = -(c15 * z25))
    : c15 * z25 + c25 * z15 = 0 := by
  linear_combination (1) * hd

/-- 生成元 ((1, 0, 2, -1), (5, 0, 2, 1))：退化 CYC・枡の歩数 0・掛けた単項式の次数 0。 -/
theorem translated_class_21_02 {z01 z05 z12 z25 c01 c05 c12 c25 : ℂ}
    (hd : c05 * c12 * z01 * z25 = -(c01 * c25 * z05 * z12))
    : c01 * c25 * z05 * z12 + c05 * c12 * z01 * z25 = 0 := by
  linear_combination (1) * hd

/-- 生成元 ((2, 0, 1, -1), (3, 0, 2, 1))：退化 RIGHT・枡の歩数 2・掛けた単項式の次数 6。 -/
theorem translated_class_21_03 {z02 z03 z12 z15 z23 z25 z35 c02 c03 c12 c15 c23 c25 c35 : ℂ}
    (hd : c25 * z15 = -(c15 * z25))
    (h2 : c03 * c35 * z02 * z25 = c02 * c25 * z03 * z35)
    (h3 : c23 * c35 * z12 * z15 = c12 * c15 * z23 * z35)
    (nc15 : c15 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz35 : z35 ≠ 0)
    : c02 * c23 * z03 * z12 + c03 * c12 * z02 * z23 = 0 := by
  have hM : c15 * c25 * c35 * z15 * z25 * z35 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc15) (nc25)) (nc35)) (nz15)) (nz25)) (nz35)
  have hkey : (c15 * c25 * c35 * z15 * z25 * z35) * (c02 * c23 * z03 * z12 + c03 * c12 * z02 * z23) = 0 := by
    linear_combination (c02 * c23 * c25 * c35 * z03 * z12 * z15 * z35) * hd + (c23 * c25 * c35 * z12 * z15 ^ 2) * h2 + (-1 * (c03 * c25 * c35 * z02 * z15 * z25)) * h3
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((0, 1, 5, 1), (3, 2, 5, -1))：退化 RIGHT・枡の歩数 3・掛けた単項式の次数 10。 -/
theorem translated_class_21_04 {z01 z02 z03 z05 z13 z15 z23 z25 z35 c01 c02 c03 c05 c13 c15 c23 c25 c35 : ℂ}
    (hd : c25 * z15 = -(c15 * z25))
    (h2 : c03 * c35 * z02 * z25 = c02 * c25 * z03 * z35)
    (h3 : c13 * c23 * z01 * z02 = c01 * c02 * z13 * z23)
    (h4 : c13 * c15 * z03 * z05 = c03 * c05 * z13 * z15)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz25 : z25 ≠ 0)
    : c05 * c23 * z01 * z35 + c01 * c35 * z05 * z23 = 0 := by
  have hM : c02 * c03 * c13 * c15 * c25 * z02 * z03 * z13 * z15 * z25 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc02) (nc03)) (nc13)) (nc15)) (nc25)) (nz02)) (nz03)) (nz13)) (nz15)) (nz25)
  have hkey : (c02 * c03 * c13 * c15 * c25 * z02 * z03 * z13 * z15 * z25) * (c05 * c23 * z01 * z35 + c01 * c35 * z05 * z23) = 0 := by
    linear_combination (c02 * c03 * c05 * c13 * c23 * c25 * z01 * z02 * z03 * z13 * z15 * z35) * hd + (c03 * c05 * c13 * c23 * c25 * z01 * z02 * z13 * z15 ^ 2) * h2 + (-1 * (c03 ^ 2 * c05 * c25 * c35 * z02 * z13 * z15 ^ 2 * z25)) * h3 + (c01 * c02 * c03 * c25 * c35 * z02 * z13 * z15 * z23 * z25) * h4
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((0, 2, 3, 1), (5, 2, 3, -1))：退化 CYC・枡の歩数 3・掛けた単項式の次数 12。 -/
theorem translated_class_21_05 {z01 z02 z03 z04 z05 z12 z14 z25 z35 z45 c01 c02 c03 c04 c05 c12 c14 c25 c35 c45 : ℂ}
    (hd : c05 * c12 * z01 * z25 = -(c01 * c25 * z05 * z12))
    (h2 : c05 * c45 * z01 * z14 = c01 * c14 * z05 * z45)
    (h3 : c12 * c14 * z02 * z04 = c02 * c04 * z12 * z14)
    (h4 : c35 * c45 * z03 * z04 = c03 * c04 * z35 * z45)
    (nc01 : c01 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc45 : c45 ≠ 0)
    (nz01 : z01 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz45 : z45 ≠ 0)
    : c03 * c25 * z02 * z35 + c02 * c35 * z03 * z25 = 0 := by
  have hM : c01 * c04 * c05 * c12 * c14 * c45 * z01 * z04 * z05 * z12 * z14 * z45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc01) (nc04)) (nc05)) (nc12)) (nc14)) (nc45)) (nz01)) (nz04)) (nz05)) (nz12)) (nz14)) (nz45)
  have hkey : (c01 * c04 * c05 * c12 * c14 * c45 * z01 * z04 * z05 * z12 * z14 * z45) * (c03 * c25 * z02 * z35 + c02 * c35 * z03 * z25) = 0 := by
    linear_combination (c03 * c04 * c05 * c12 * c14 * c45 * z01 * z02 * z04 * z14 * z35 * z45) * hd + (-1 * (c03 * c04 * c05 * c12 ^ 2 * c14 * z01 * z02 * z04 * z25 * z35 * z45)) * h2 + (-1 * (c01 * c03 * c04 * c05 * c12 * c14 * z01 * z05 * z25 * z35 * z45 ^ 2)) * h3 + (c01 * c02 * c04 * c05 * c12 * c14 * z01 * z05 * z12 * z14 * z25 * z45) * h4
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((0, 2, 5, -1), (2, 1, 5, -1))：退化 RIGHT・枡の歩数 1・掛けた単項式の次数 2。 -/
theorem translated_class_21_06 {z02 z05 z12 z15 z25 c02 c05 c12 c15 c25 : ℂ}
    (hd : c25 * z15 = -(c15 * z25))
    (h2 : c05 * c15 * z02 * z12 = c02 * c12 * z05 * z15)
    (nc15 : c15 ≠ 0)
    (nz15 : z15 ≠ 0)
    : c02 * c12 * z05 * z25 + c05 * c25 * z02 * z12 = 0 := by
  have hM : c15 * z15 ≠ 0 := mul_ne_zero (nc15) (nz15)
  have hkey : (c15 * z15) * (c02 * c12 * z05 * z25 + c05 * c25 * z02 * z12) = 0 := by
    linear_combination (c02 * c12 * z05 * z15) * hd + (c25 * z15) * h2
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((0, 3, 5, -1), (2, 3, 5, -1))：退化 CYC・枡の歩数 4・掛けた単項式の次数 16。 -/
theorem translated_class_21_07 {z01 z02 z03 z04 z05 z12 z14 z23 z24 z25 z45 c01 c02 c03 c04 c05 c12 c14 c23 c24 c25 c45 : ℂ}
    (hd : c05 * c12 * z01 * z25 = -(c01 * c25 * z05 * z12))
    (h2 : c04 * c24 * z03 * z23 = c03 * c23 * z04 * z24)
    (h3 : c05 * c45 * z01 * z14 = c01 * c14 * z05 * z45)
    (h4 : c12 * c14 * z02 * z04 = c02 * c04 * z12 * z14)
    (h5 : c24 * c45 * z02 * z05 = c02 * c05 * z24 * z45)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc45 : c45 ≠ 0)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz45 : z45 ≠ 0)
    : c03 * c23 * z05 * z25 + c05 * c25 * z03 * z23 = 0 := by
  have hM : c01 * c02 * c04 * c05 * c12 * c14 * c24 * c45 * z01 * z02 * z04 * z05 * z12 * z14 * z24 * z45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc01) (nc02)) (nc04)) (nc05)) (nc12)) (nc14)) (nc24)) (nc45)) (nz01)) (nz02)) (nz04)) (nz05)) (nz12)) (nz14)) (nz24)) (nz45)
  have hkey : (c01 * c02 * c04 * c05 * c12 * c14 * c24 * c45 * z01 * z02 * z04 * z05 * z12 * z14 * z24 * z45) * (c03 * c23 * z05 * z25 + c05 * c25 * z03 * z23) = 0 := by
    linear_combination (c01 * c02 * c03 * c04 * c14 * c23 * c24 * c45 * z02 * z04 * z05 ^ 2 * z12 * z14 * z24 * z45) * hd + (c01 ^ 2 * c02 * c04 * c14 * c24 * c25 * c45 * z02 * z05 ^ 3 * z12 ^ 2 * z14 * z45) * h2 + (c01 * c02 * c04 ^ 2 * c24 ^ 2 * c25 * c45 * z02 * z03 * z05 ^ 2 * z12 ^ 2 * z14 * z23) * h3 + (c01 * c04 * c05 * c24 ^ 2 * c25 * c45 ^ 2 * z01 * z02 * z03 * z05 ^ 2 * z12 * z14 * z23) * h4 + (-1 * (c01 * c04 * c05 * c12 * c14 * c24 * c25 * c45 * z01 * z02 * z03 * z04 * z05 * z12 * z14 * z23)) * h5
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((2, 1, 3, 1), (2, 1, 3, 1))：退化 CYC・枡の歩数 4・掛けた単項式の次数 16。 -/
theorem translated_class_21_08 {z01 z02 z05 z12 z13 z14 z23 z24 z25 z45 c01 c02 c05 c12 c13 c14 c23 c24 c25 c45 : ℂ}
    (hd : c05 * c12 * z01 * z25 = -(c01 * c25 * z05 * z12))
    (h2 : c13 * c23 * z01 * z02 = c01 * c02 * z13 * z23)
    (h3 : c14 * c45 * z12 * z25 = c12 * c25 * z14 * z45)
    (h4 : c24 * c45 * z02 * z05 = c02 * c05 * z24 * z45)
    (h5 : c23 * c24 * z13 * z14 = c13 * c14 * z23 * z24)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc45 : c45 ≠ 0)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz45 : z45 ≠ 0)
    : c23 ^ 2 * z12 ^ 2 + c12 ^ 2 * z23 ^ 2 = 0 := by
  have hM : c01 * c02 * c05 * c13 * c14 * c24 * c25 * c45 * z01 * z02 * z05 * z13 * z14 * z24 * z25 * z45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc01) (nc02)) (nc05)) (nc13)) (nc14)) (nc24)) (nc25)) (nc45)) (nz01)) (nz02)) (nz05)) (nz13)) (nz14)) (nz24)) (nz25)) (nz45)
  have hkey : (c01 * c02 * c05 * c13 * c14 * c24 * c25 * c45 * z01 * z02 * z05 * z13 * z14 * z24 * z25 * z45) * (c23 ^ 2 * z12 ^ 2 + c12 ^ 2 * z23 ^ 2) = 0 := by
    linear_combination (c02 * c05 * c13 * c14 * c23 ^ 2 * c24 * c45 * z01 * z02 * z12 * z13 * z14 * z24 * z25 * z45) * hd + (-1 * (c02 * c05 ^ 2 * c12 * c14 * c23 * c24 * c45 * z01 * z12 * z13 * z14 * z24 * z25 ^ 2 * z45)) * h2 + (-1 * (c01 * c02 ^ 2 * c05 ^ 2 * c12 * c23 * c24 * z01 * z13 ^ 2 * z14 * z23 * z24 * z25 * z45)) * h3 + (c01 * c02 * c05 * c12 ^ 2 * c23 * c24 * c25 * z01 * z13 ^ 2 * z14 ^ 2 * z23 * z25 * z45) * h4 + (-1 * (c01 * c02 * c05 * c12 ^ 2 * c24 * c25 * c45 * z01 * z02 * z05 * z13 * z14 * z23 * z25 * z45)) * h5
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((2, 1, 3, -1), (5, 1, 3, 1))：退化 CYC・枡の歩数 4・掛けた単項式の次数 16。 -/
theorem translated_class_21_09 {z01 z02 z05 z12 z13 z15 z23 z24 z25 z34 z35 z45 c01 c02 c05 c12 c13 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (hd : c05 * c12 * z01 * z25 = -(c01 * c25 * z05 * z12))
    (h2 : c13 * c23 * z01 * z02 = c01 * c02 * z13 * z23)
    (h3 : c15 * c45 * z13 * z34 = c13 * c34 * z15 * z45)
    (h4 : c25 * c35 * z24 * z34 = c24 * c34 * z25 * z35)
    (h5 : c24 * c45 * z02 * z05 = c02 * c05 * z24 * z45)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc45 : c45 ≠ 0)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz45 : z45 ≠ 0)
    : c12 * c35 * z15 * z23 + c15 * c23 * z12 * z35 = 0 := by
  have hM : c01 * c02 * c05 * c13 * c24 * c25 * c34 * c45 * z01 * z02 * z05 * z13 * z24 * z25 * z34 * z45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc01) (nc02)) (nc05)) (nc13)) (nc24)) (nc25)) (nc34)) (nc45)) (nz01)) (nz02)) (nz05)) (nz13)) (nz24)) (nz25)) (nz34)) (nz45)
  have hkey : (c01 * c02 * c05 * c13 * c24 * c25 * c34 * c45 * z01 * z02 * z05 * z13 * z24 * z25 * z34 * z45) * (c12 * c35 * z15 * z23 + c15 * c23 * z12 * z35) = 0 := by
    linear_combination (c01 * c02 * c13 * c24 * c25 * c34 * c35 * c45 * z02 * z05 * z13 * z15 * z23 * z24 * z34 * z45) * hd + (c01 * c13 * c24 * c25 ^ 2 * c34 * c35 * c45 * z02 * z05 ^ 2 * z12 * z15 * z24 * z34 * z45) * h2 + (c01 * c13 * c23 * c24 * c25 ^ 2 * c35 * c45 * z01 * z02 ^ 2 * z05 ^ 2 * z12 * z24 * z34) * h3 + (-1 * (c01 * c13 * c15 * c23 * c24 * c25 * c45 ^ 2 * z01 * z02 ^ 2 * z05 ^ 2 * z12 * z13 * z34)) * h4 + (-1 * (c01 * c13 * c15 * c23 * c24 * c25 * c34 * c45 * z01 * z02 * z05 * z12 * z13 * z25 * z34 * z35)) * h5
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((2, 1, 3, -1), (5, 2, 3, -1))：退化 RIGHT・枡の歩数 1・掛けた単項式の次数 2。 -/
theorem translated_class_21_10 {z12 z15 z23 z25 z35 c12 c15 c23 c25 c35 : ℂ}
    (hd : c25 * z15 = -(c15 * z25))
    (h2 : c23 * c35 * z12 * z15 = c12 * c15 * z23 * z35)
    (nc15 : c15 ≠ 0)
    (nz15 : z15 ≠ 0)
    : c12 * c25 * z23 * z35 + c23 * c35 * z12 * z25 = 0 := by
  have hM : c15 * z15 ≠ 0 := mul_ne_zero (nc15) (nz15)
  have hkey : (c15 * z15) * (c12 * c25 * z23 * z35 + c23 * c35 * z12 * z25) = 0 := by
    linear_combination (c12 * c15 * z23 * z35) * hd + (c15 * z25) * h2
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- 生成元 ((5, 2, 3, 1), (5, 2, 3, 1))：退化 CYC・枡の歩数 4・掛けた単項式の次数 16。 -/
theorem translated_class_21_11 {z01 z02 z03 z05 z12 z13 z15 z23 z25 z35 c01 c02 c03 c05 c12 c13 c15 c23 c25 c35 : ℂ}
    (hd : c05 * c12 * z01 * z25 = -(c01 * c25 * z05 * z12))
    (h2 : c03 * c35 * z02 * z25 = c02 * c25 * z03 * z35)
    (h3 : c13 * c23 * z01 * z02 = c01 * c02 * z13 * z23)
    (h4 : c23 * c35 * z12 * z15 = c12 * c15 * z23 * z35)
    (h5 : c13 * c15 * z03 * z05 = c03 * c05 * z13 * z15)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    : c35 ^ 2 * z25 ^ 2 + c25 ^ 2 * z35 ^ 2 = 0 := by
  have hM : c01 * c02 * c03 * c05 * c12 * c13 * c15 * c23 * z01 * z02 * z03 * z05 * z12 * z13 * z15 * z23 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nc01) (nc02)) (nc03)) (nc05)) (nc12)) (nc13)) (nc15)) (nc23)) (nz01)) (nz02)) (nz03)) (nz05)) (nz12)) (nz13)) (nz15)) (nz23)
  have hkey : (c01 * c02 * c03 * c05 * c12 * c13 * c15 * c23 * z01 * z02 * z03 * z05 * z12 * z13 * z15 * z23) * (c35 ^ 2 * z25 ^ 2 + c25 ^ 2 * z35 ^ 2) = 0 := by
    linear_combination (c01 * c02 * c03 * c13 * c15 * c23 * c35 ^ 2 * z02 * z03 * z05 * z12 * z13 * z15 * z23 * z25) * hd + (-1 * (c01 ^ 2 * c02 * c13 * c15 * c23 * c25 * c35 * z03 * z05 ^ 2 * z12 ^ 2 * z13 * z15 * z23)) * h2 + (c01 * c02 * c13 * c15 * c23 * c25 ^ 2 * c35 * z03 ^ 2 * z05 ^ 2 * z12 ^ 2 * z15 * z35) * h3 + (-1 * (c01 * c02 * c13 ^ 2 * c15 * c23 * c25 ^ 2 * z01 * z02 * z03 ^ 2 * z05 ^ 2 * z12 * z35)) * h4 + (-1 * (c01 * c02 * c12 * c13 * c15 * c23 * c25 ^ 2 * z01 * z02 * z03 * z05 * z12 * z23 * z35 ^ 2)) * h5
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hM
  · exact h

/-- K21 の非負結合の証書。生成元 11 本・支持 68 行・次数 3・分母 74。仮定は各生成元の「実部が 0」を 2 乗距離で読んだもの。結論の右辺は全部正の係数の単項式の和なので、2 乗距離が全部正であることと矛盾する。 -/
theorem certificate_class_21 (d01 d02 d03 _d04 d05 d12 d13 _d14 d15 d23 _d24 d25 _d34 d35 _d45 : ℝ)
    (q1 : -d12 + d15 + d25 = 0)
    (q2 : 2 * d01 * d25 - 2 * d02 * d15 + 2 * d05 * d12 = 0)
    (q3 : -2 * d01 * d23 - 2 * d02 * d12 + 2 * d02 * d13 + 2 * d12 * d23 = 0)
    (q4 : d01 * d23 - d01 * d25 + d01 * d35 - d02 * d13 + d02 * d15 + d02 * d35 + d03 * d12 - d03 * d15 - d03 * d25 - d05 * d12 + d05 * d13 + d05 * d23 - d12 * d35 + d13 * d25 - d15 * d23 = 0)
    (q5 : 2 * d02 * d35 + 2 * d03 * d25 - 2 * d05 * d23 = 0)
    (q6 : -2 * d01 * d25 + 2 * d02 * d25 + 2 * d05 * d12 - 2 * d05 * d15 + 2 * d05 * d25 + 2 * d15 * d25 - 2 * d25 * d25 = 0)
    (q7 : 2 * d02 * d35 + 2 * d03 * d23 - 2 * d03 * d35 + 2 * d05 * d25 - 2 * d05 * d35 - 2 * d23 * d35 - 2 * d25 * d35 + 2 * d35 * d35 = 0)
    (q8 : 2 * d12 * d12 - 4 * d12 * d13 + 2 * d13 * d13 - 4 * d13 * d23 + 2 * d23 * d23 = 0)
    (q9 : 2 * d12 * d35 - 2 * d13 * d25 + 2 * d15 * d23 = 0)
    (q10 : 2 * d12 * d35 + 2 * d13 * d23 - 2 * d13 * d35 - 2 * d15 * d23 - 2 * d23 * d23 + 2 * d23 * d25 + 2 * d23 * d35 = 0)
    (q11 : 2 * d23 * d23 - 4 * d23 * d25 - 4 * d23 * d35 + 2 * d25 * d25 + 2 * d35 * d35 = 0)
    : 592 * d01 * d23 * d35 + 412 * d01 * d35 * d35 + 32 * d02 * d25 * d35 + 712 * d02 * d35 * d35 + 368 * d03 * d15 * d23 + 68 * d03 * d15 * d25 + 36 * d03 * d15 * d35 + 64 * d03 * d23 * d25 + 4 * d03 * d25 * d25 + 584 * d03 * d25 * d35 + 300 * d05 * d13 * d35 + 136 * d05 * d15 * d25 + 112 * d05 * d35 * d35 + 16 * d15 * d35 * d35 + 200 * d25 * d25 * d35 + 64 * d25 * d35 * d35 = 0 := by
  linear_combination (-60 * d03 * d12 + 60 * d03 * d13 + 60 * d03 * d23 + 60 * d03 * d25 + 464 * d03 * d35 + 60 * d05 * d12 - 60 * d05 * d13 + 120 * d05 * d25 + 40 * d05 * d35 + 60 * d12 * d23 - 60 * d12 * d25 - 60 * d13 * d23 + 60 * d13 * d25 + 60 * d23 * d23 - 60 * d23 * d25 + 188 * d23 * d35 - 8 * d25 * d35) * q1 + (60 * d23 + 218 * d35) * q2 + (-30 * d12 + 60 * d13 - 30 * d15 + 30 * d25 - 30 * d35) * q3 + (-60 * d12 + 60 * d13 + 60 * d23 + 412 * d35) * q4 + (30 * d12 + 101 * d13 + 4 * d15 + 1 * d23 + 46 * d25 + 224 * d35) * q5 + (30 * d12 - 30 * d13 + 30 * d23 + 12 * d35) * q6 + (75 * d13 + 8 * d15 - 1 * d23 - 42 * d25 - 74 * d35) * q7 + (-30 * d02 - 30 * d05 + 60 * d23 - 30 * d25 - 60 * d35) * q8 + (101 * d03 + 15 * d05 + 122 * d23 - 2 * d25 + 133 * d35) * q9 + (30 * d01 - 30 * d02 - 75 * d03 - 19 * d05 + 30 * d12 - 60 * d13 + 122 * d23 - 2 * d25 + 13 * d35) * q10 + (-74 * d03 - 18 * d05 + 60 * d12 - 62 * d13 + 62 * d23 + 74 * d35) * q11

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

set_option maxHeartbeats 4000000 in
/-- **この類が強制する 2 本の退化。**格子の飽和の中にある位数 2 の形式は
共線形式 `COL(5; 1, 2)` 1 本と共円形式 `F(p0, p2; p1, p5)` 1 本の 2 類で、
どちらも証書を平方の等式として読んで一般の位置で片側を落とす。 -/
theorem degeneracies_of_class_21
    (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw2 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw9 : Psi (p 3) (p 4) (p 0) (p 2) = 0)
    (hw20 : Psi (p 1) (p 5) (p 0) (p 4) = 0)
    (hw27 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw30 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw47 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw59 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw60 : Psi (p 0) (p 1) (p 2) (p 4) = 0)
    (hw68 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw78 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : qq (p 1) (p 2) (p 5) = 0 ∧
      cyclicValue (p 0) (p 2) (p 1) (p 5)
        + cyclicValueBar (p 0) (p 2) (p 1) (p 5) = 0 := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have hcyc := hgp.2.2
  have hRP : (barC (p 2) - barC (p 5)) ^ 2 * (toC (p 1) - toC (p 5)) ^ 2
      = (barC (p 1) - barC (p 5)) ^ 2 * (toC (p 2) - toC (p 5)) ^ 2 :=
    rightAnglePairClass
      (show (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) = (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) from by
        linear_combination (1 : ℂ) * witnessEq hw27)
      (show (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) * (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) = (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) * (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) from by
        linear_combination (-1 : ℂ) * witnessEq hw47)
      (show (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) * (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) = (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) * (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) from by
        linear_combination (1 : ℂ) * witnessEq hw59)
      (show (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) = (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) * (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) from by
        linear_combination (-1 : ℂ) * witnessEq hw68)
      (show (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) = (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) * (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 5)) from by
        linear_combination (1 : ℂ) * witnessEq hw78)
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
  have hsqR : ((toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 2))) ^ 2
      = ((barC (p 5) - barC (p 1)) * (toC (p 5) - toC (p 2))) ^ 2 := by
    linear_combination hRP
  have hcrR : cross (p 5) (p 1) (p 2) ≠ 0 := by
    have h : cross (p 1) (p 2) (p 5) ≠ 0 := by
      have hh := hcol 1 2 5 (by decide) (by decide)
      simpa [Collinear3] using hh
    intro hz
    apply h
    simp only [cross] at hz ⊢
    linarith
  have hrR : qq (p 1) (p 2) (p 5) * cross (p 5) (p 1) (p 2) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq (a := p 5) (b := p 1) (c := p 2) hsqR
  have hR : qq (p 1) (p 2) (p 5) = 0 := by
    rcases mul_eq_zero.mp hrR with h | h
    · exact h
    · exact absurd h hcrR
  have hCP : (barC (p 0) - barC (p 5)) ^ 2 * (barC (p 1) - barC (p 2)) ^ 2 * (toC (p 0) - toC (p 1)) ^ 2 * (toC (p 2) - toC (p 5)) ^ 2
      = (barC (p 0) - barC (p 1)) ^ 2 * (barC (p 2) - barC (p 5)) ^ 2 * (toC (p 0) - toC (p 5)) ^ 2 * (toC (p 1) - toC (p 2)) ^ 2 :=
    crossRatioPairClass
      (show (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) = (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) * (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) from by
        linear_combination (1 : ℂ) * witnessEq hw2)
      (show (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) * (toC (p 0) - toC (p 3)) * (toC (p 2) - toC (p 3)) = (barC (p 0) - barC (p 3)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) from by
        linear_combination (1 : ℂ) * witnessEq hw9)
      (show (barC (p 0) - barC (p 5)) * (barC (p 4) - barC (p 5)) * (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) = (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) * (toC (p 0) - toC (p 5)) * (toC (p 4) - toC (p 5)) from by
        linear_combination (-1 : ℂ) * witnessEq hw20)
      (show (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) = (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) from by
        linear_combination (1 : ℂ) * witnessEq hw27)
      (show (barC (p 1) - barC (p 3)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) = (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) * (toC (p 1) - toC (p 3)) * (toC (p 2) - toC (p 3)) from by
        linear_combination (1 : ℂ) * witnessEq hw30)
      (show (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) * (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) = (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) * (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) from by
        linear_combination (-1 : ℂ) * witnessEq hw47)
      (show (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) * (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) = (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) * (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) from by
        linear_combination (1 : ℂ) * witnessEq hw59)
      (show (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) * (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 4)) = (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 4)) * (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) from by
        linear_combination (1 : ℂ) * witnessEq hw60)
      (show (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) = (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) * (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) from by
        linear_combination (-1 : ℂ) * witnessEq hw68)
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
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
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
      (toC_sub_ne_zero (hne 4 5 (by decide)))
  have hsqC : cyclicValue (p 0) (p 2) (p 1) (p 5) ^ 2
      = cyclicValueBar (p 0) (p 2) (p 1) (p 5) ^ 2 := by
    simp only [cyclicValue, cyclicValueBar]
    linear_combination hCP
  have hdet : det4 (p 0) (p 2) (p 1) (p 5) ≠ 0 := by
    have h0 : det4 (p 0) (p 1) (p 2) (p 5) ≠ 0 := by
      simpa [Concyclic4] using hcyc 0 1 2 5 (by decide) (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [det4, cross] at hx ⊢
    linear_combination -hx
  exact ⟨hR, cyc_add_bar_eq_zero hsqC hdet⟩

set_option maxHeartbeats 4000000 in
/-- **2 本の退化を「ずらした代表」で 11 回読むと矛盾する。**各代表の実部は
`re_atom_pair` / `re_atom_atomb` で 2 乗距離の 2 次式になり、
その非負結合が正の単項式の和になる。 -/
theorem no_general_position_of_the_degeneracies_21
    (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw2 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw9 : Psi (p 3) (p 4) (p 0) (p 2) = 0)
    (hw20 : Psi (p 1) (p 5) (p 0) (p 4) = 0)
    (hw27 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw30 : Psi (p 0) (p 3) (p 1) (p 2) = 0)
    (hw47 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw52 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw59 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw60 : Psi (p 0) (p 1) (p 2) (p 4) = 0)
    (hw68 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw69 : Psi (p 1) (p 3) (p 2) (p 5) = 0)
    (hw74 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw75 : Psi (p 1) (p 2) (p 3) (p 4) = 0)
    (hw78 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    (hR : qq (p 1) (p 2) (p 5) = 0)
    (hC : cyclicValue (p 0) (p 2) (p 1) (p 5)
      + cyclicValueBar (p 0) (p 2) (p 1) (p 5) = 0)
    : False := by
  have hne := hgp.1
  have hdR : (barC (p 2) - barC (p 5)) * (toC (p 1) - toC (p 5)) = -((barC (p 1) - barC (p 5)) * (toC (p 2) - toC (p 5))) := by
    have hh := atom_add_atomb_eq_zero (a := p 5) (b := p 1) (c := p 2) hR
    simp only [atom, atomb] at hh
    linear_combination (1 : ℂ) * hh
  have hdC : (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 2)) * (toC (p 0) - toC (p 1)) * (toC (p 2) - toC (p 5)) = -((barC (p 0) - barC (p 1)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 2))) := by
    simp only [cyclicValue, cyclicValueBar] at hC
    linear_combination (-1 : ℂ) * hC
  have E2 : (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) = (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) * (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) := by
    linear_combination (1 : ℂ) * witnessEq hw2
  have E9 : (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) * (toC (p 0) - toC (p 3)) * (toC (p 2) - toC (p 3)) = (barC (p 0) - barC (p 3)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) := by
    linear_combination (1 : ℂ) * witnessEq hw9
  have E20 : (barC (p 0) - barC (p 5)) * (barC (p 4) - barC (p 5)) * (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 4)) = (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 4)) * (toC (p 0) - toC (p 5)) * (toC (p 4) - toC (p 5)) := by
    linear_combination (-1 : ℂ) * witnessEq hw20
  have E27 : (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) = (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) := by
    linear_combination (1 : ℂ) * witnessEq hw27
  have E30 : (barC (p 1) - barC (p 3)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) = (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) * (toC (p 1) - toC (p 3)) * (toC (p 2) - toC (p 3)) := by
    linear_combination (1 : ℂ) * witnessEq hw30
  have E47 : (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) * (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) = (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) * (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) := by
    linear_combination (-1 : ℂ) * witnessEq hw47
  have E52 : (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) * (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) = (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) * (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) := by
    linear_combination (1 : ℂ) * witnessEq hw52
  have E59 : (barC (p 2) - barC (p 5)) * (barC (p 3) - barC (p 5)) * (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) = (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) * (toC (p 2) - toC (p 5)) * (toC (p 3) - toC (p 5)) := by
    linear_combination (1 : ℂ) * witnessEq hw59
  have E60 : (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 4)) * (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 4)) = (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 4)) * (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 4)) := by
    linear_combination (1 : ℂ) * witnessEq hw60
  have E68 : (barC (p 2) - barC (p 4)) * (barC (p 4) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 5)) = (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 5)) * (toC (p 2) - toC (p 4)) * (toC (p 4) - toC (p 5)) := by
    linear_combination (-1 : ℂ) * witnessEq hw68
  have E69 : (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 5)) * (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 5)) = (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 5)) * (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 5)) := by
    linear_combination (-1 : ℂ) * witnessEq hw69
  have E74 : (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 4)) = (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 4)) * (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) := by
    linear_combination (1 : ℂ) * witnessEq hw74
  have E75 : (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 4)) * (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) = (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) * (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 4)) := by
    linear_combination (1 : ℂ) * witnessEq hw75
  have E78 : (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) = (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) * (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 5)) := by
    linear_combination (1 : ℂ) * witnessEq hw78
  have s01 : sqdist (p 1) (p 0) = sqdist (p 0) (p 1) := sqdist_comm (p 1) (p 0)
  have s02 : sqdist (p 2) (p 0) = sqdist (p 0) (p 2) := sqdist_comm (p 2) (p 0)
  have s03 : sqdist (p 3) (p 0) = sqdist (p 0) (p 3) := sqdist_comm (p 3) (p 0)
  have s05 : sqdist (p 5) (p 0) = sqdist (p 0) (p 5) := sqdist_comm (p 5) (p 0)
  have s12 : sqdist (p 2) (p 1) = sqdist (p 1) (p 2) := sqdist_comm (p 2) (p 1)
  have s13 : sqdist (p 3) (p 1) = sqdist (p 1) (p 3) := sqdist_comm (p 3) (p 1)
  have s15 : sqdist (p 5) (p 1) = sqdist (p 1) (p 5) := sqdist_comm (p 5) (p 1)
  have s23 : sqdist (p 3) (p 2) = sqdist (p 2) (p 3) := sqdist_comm (p 3) (p 2)
  have s25 : sqdist (p 5) (p 2) = sqdist (p 2) (p 5) := sqdist_comm (p 5) (p 2)
  have s35 : sqdist (p 5) (p 3) = sqdist (p 3) (p 5) := sqdist_comm (p 5) (p 3)
  have q1 : -sqdist (p 1) (p 2) + sqdist (p 1) (p 5) + sqdist (p 2) (p 5) = 0 := by
    have hx := x2_eq_two_qq (p 5) (p 1) (p 2)
    rw [hR] at hx
    simp only [x2, dd, s15, s25] at hx
    linear_combination hx
  have T2 : (barC (p 0) - barC (p 1)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 2)) + (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 2)) * (toC (p 0) - toC (p 1)) * (toC (p 2) - toC (p 5)) = 0 :=
    translated_class_21_02
      hdC
  have S2 : atom (p 5) (p 0) (p 2) * atomb (p 1) (p 0) (p 2) + atomb (p 5) (p 0) (p 2) * atom (p 1) (p 0) (p 2) = 0 := by
    simp only [atom, atomb]
    linear_combination (-1 : ℂ) * T2
  have R2 : (atom (p 5) (p 0) (p 2) * atomb (p 1) (p 0) (p 2)).re = 0 := re_zero_of_sum (atomb_mul_atom_eq_conj (p 5) (p 0) (p 2) (p 1) (p 0) (p 2)) S2
  have q2 : 2 * sqdist (p 0) (p 1) * sqdist (p 2) (p 5) - 2 * sqdist (p 0) (p 2) * sqdist (p 1) (p 5) + 2 * sqdist (p 0) (p 5) * sqdist (p 1) (p 2) = 0 := by
    have hrp := re_atom_atomb (p 5) (p 0) (p 2) (p 1) (p 0) (p 2)
    rw [R2] at hrp
    simp only [x2, dd, sqdist_self, s01, s02, s05, s12, s15, s25] at hrp
    linear_combination -hrp
  have T3 : (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 3)) * (toC (p 1) - toC (p 2)) + (barC (p 0) - barC (p 3)) * (barC (p 1) - barC (p 2)) * (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 3)) = 0 :=
    translated_class_21_03
      hdR
      E27
      E69
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
  have S3 : atom (p 3) (p 0) (p 2) * atomb (p 2) (p 0) (p 1) + atomb (p 3) (p 0) (p 2) * atom (p 2) (p 0) (p 1) = 0 := by
    simp only [atom, atomb]
    linear_combination (1 : ℂ) * T3
  have R3 : (atom (p 3) (p 0) (p 2) * atomb (p 2) (p 0) (p 1)).re = 0 := re_zero_of_sum (atomb_mul_atom_eq_conj (p 3) (p 0) (p 2) (p 2) (p 0) (p 1)) S3
  have q3 : -2 * sqdist (p 0) (p 1) * sqdist (p 2) (p 3) - 2 * sqdist (p 0) (p 2) * sqdist (p 1) (p 2) + 2 * sqdist (p 0) (p 2) * sqdist (p 1) (p 3) + 2 * sqdist (p 1) (p 2) * sqdist (p 2) (p 3) = 0 := by
    have hrp := re_atom_atomb (p 3) (p 0) (p 2) (p 2) (p 0) (p 1)
    rw [R3] at hrp
    simp only [x2, dd, sqdist_self, s02, s03, s12, s13, s23] at hrp
    linear_combination -hrp
  have T4 : (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 1)) * (toC (p 3) - toC (p 5)) + (barC (p 0) - barC (p 1)) * (barC (p 3) - barC (p 5)) * (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 3)) = 0 :=
    translated_class_21_04
      hdR
      E27
      E30
      E78
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
  have S4 : atom (p 0) (p 1) (p 5) * atomb (p 3) (p 2) (p 5) + atomb (p 0) (p 1) (p 5) * atom (p 3) (p 2) (p 5) = 0 := by
    simp only [atom, atomb]
    linear_combination (-1 : ℂ) * T4
  have R4 : (atom (p 0) (p 1) (p 5) * atomb (p 3) (p 2) (p 5)).re = 0 := re_zero_of_sum (atomb_mul_atom_eq_conj (p 0) (p 1) (p 5) (p 3) (p 2) (p 5)) S4
  have q4 : sqdist (p 0) (p 1) * sqdist (p 2) (p 3) - sqdist (p 0) (p 1) * sqdist (p 2) (p 5) + sqdist (p 0) (p 1) * sqdist (p 3) (p 5) - sqdist (p 0) (p 2) * sqdist (p 1) (p 3) + sqdist (p 0) (p 2) * sqdist (p 1) (p 5) + sqdist (p 0) (p 2) * sqdist (p 3) (p 5) + sqdist (p 0) (p 3) * sqdist (p 1) (p 2) - sqdist (p 0) (p 3) * sqdist (p 1) (p 5) - sqdist (p 0) (p 3) * sqdist (p 2) (p 5) - sqdist (p 0) (p 5) * sqdist (p 1) (p 2) + sqdist (p 0) (p 5) * sqdist (p 1) (p 3) + sqdist (p 0) (p 5) * sqdist (p 2) (p 3) - sqdist (p 1) (p 2) * sqdist (p 3) (p 5) + sqdist (p 1) (p 3) * sqdist (p 2) (p 5) - sqdist (p 1) (p 5) * sqdist (p 2) (p 3) = 0 := by
    have hrp := re_atom_atomb (p 0) (p 1) (p 5) (p 3) (p 2) (p 5)
    rw [R4] at hrp
    simp only [x2, dd, sqdist_self, s23, s25, s35] at hrp
    linear_combination -hrp
  have T5 : (barC (p 0) - barC (p 3)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 3) - toC (p 5)) + (barC (p 0) - barC (p 2)) * (barC (p 3) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 2) - toC (p 5)) = 0 :=
    translated_class_21_05
      hdC
      E20
      E60
      E74
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
  have S5 : atom (p 0) (p 2) (p 3) * atomb (p 5) (p 2) (p 3) + atomb (p 0) (p 2) (p 3) * atom (p 5) (p 2) (p 3) = 0 := by
    simp only [atom, atomb]
    linear_combination (1 : ℂ) * T5
  have R5 : (atom (p 0) (p 2) (p 3) * atomb (p 5) (p 2) (p 3)).re = 0 := re_zero_of_sum (atomb_mul_atom_eq_conj (p 0) (p 2) (p 3) (p 5) (p 2) (p 3)) S5
  have q5 : 2 * sqdist (p 0) (p 2) * sqdist (p 3) (p 5) + 2 * sqdist (p 0) (p 3) * sqdist (p 2) (p 5) - 2 * sqdist (p 0) (p 5) * sqdist (p 2) (p 3) = 0 := by
    have hrp := re_atom_atomb (p 0) (p 2) (p 3) (p 5) (p 2) (p 3)
    rw [R5] at hrp
    simp only [x2, dd, sqdist_self, s23, s25, s35] at hrp
    linear_combination -hrp
  have T6 : (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) * (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) + (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) = 0 :=
    translated_class_21_06
      hdR
      E2
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
  have S6 : atom (p 0) (p 2) (p 5) * atom (p 2) (p 1) (p 5) + atomb (p 0) (p 2) (p 5) * atomb (p 2) (p 1) (p 5) = 0 := by
    simp only [atom, atomb]
    linear_combination (-1 : ℂ) * T6
  have R6 : (atom (p 0) (p 2) (p 5) * atom (p 2) (p 1) (p 5)).re = 0 := re_zero_of_sum (atomb_mul_atomb_eq_conj (p 0) (p 2) (p 5) (p 2) (p 1) (p 5)) S6
  have q6 : -2 * sqdist (p 0) (p 1) * sqdist (p 2) (p 5) + 2 * sqdist (p 0) (p 2) * sqdist (p 2) (p 5) + 2 * sqdist (p 0) (p 5) * sqdist (p 1) (p 2) - 2 * sqdist (p 0) (p 5) * sqdist (p 1) (p 5) + 2 * sqdist (p 0) (p 5) * sqdist (p 2) (p 5) + 2 * sqdist (p 1) (p 5) * sqdist (p 2) (p 5) - 2 * sqdist (p 2) (p 5) * sqdist (p 2) (p 5) = 0 := by
    have hrp := re_atom_pair (p 0) (p 2) (p 5) (p 2) (p 1) (p 5)
    rw [R6] at hrp
    simp only [x2, dd, sqdist_self, s12, s15, s25] at hrp
    linear_combination -hrp
  have T7 : (barC (p 0) - barC (p 3)) * (barC (p 2) - barC (p 3)) * (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) + (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) * (toC (p 0) - toC (p 3)) * (toC (p 2) - toC (p 3)) = 0 :=
    translated_class_21_07
      hdC
      E9
      E20
      E60
      E68
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
  have S7 : atom (p 0) (p 3) (p 5) * atom (p 2) (p 3) (p 5) + atomb (p 0) (p 3) (p 5) * atomb (p 2) (p 3) (p 5) = 0 := by
    simp only [atom, atomb]
    linear_combination (1 : ℂ) * T7
  have R7 : (atom (p 0) (p 3) (p 5) * atom (p 2) (p 3) (p 5)).re = 0 := re_zero_of_sum (atomb_mul_atomb_eq_conj (p 0) (p 3) (p 5) (p 2) (p 3) (p 5)) S7
  have q7 : 2 * sqdist (p 0) (p 2) * sqdist (p 3) (p 5) + 2 * sqdist (p 0) (p 3) * sqdist (p 2) (p 3) - 2 * sqdist (p 0) (p 3) * sqdist (p 3) (p 5) + 2 * sqdist (p 0) (p 5) * sqdist (p 2) (p 5) - 2 * sqdist (p 0) (p 5) * sqdist (p 3) (p 5) - 2 * sqdist (p 2) (p 3) * sqdist (p 3) (p 5) - 2 * sqdist (p 2) (p 5) * sqdist (p 3) (p 5) + 2 * sqdist (p 3) (p 5) * sqdist (p 3) (p 5) = 0 := by
    have hrp := re_atom_pair (p 0) (p 3) (p 5) (p 2) (p 3) (p 5)
    rw [R7] at hrp
    simp only [x2, dd, sqdist_self, s23, s25, s35] at hrp
    linear_combination -hrp
  have T8 : (barC (p 2) - barC (p 3)) ^ 2 * (toC (p 1) - toC (p 2)) ^ 2 + (barC (p 1) - barC (p 2)) ^ 2 * (toC (p 2) - toC (p 3)) ^ 2 = 0 :=
    translated_class_21_08
      hdC
      E30
      E52
      E68
      E75
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
  have S8 : atom (p 2) (p 1) (p 3) * atom (p 2) (p 1) (p 3) + atomb (p 2) (p 1) (p 3) * atomb (p 2) (p 1) (p 3) = 0 := by
    simp only [atom, atomb]
    linear_combination (1 : ℂ) * T8
  have R8 : (atom (p 2) (p 1) (p 3) * atom (p 2) (p 1) (p 3)).re = 0 := re_zero_of_sum (atomb_mul_atomb_eq_conj (p 2) (p 1) (p 3) (p 2) (p 1) (p 3)) S8
  have q8 : 2 * sqdist (p 1) (p 2) * sqdist (p 1) (p 2) - 4 * sqdist (p 1) (p 2) * sqdist (p 1) (p 3) + 2 * sqdist (p 1) (p 3) * sqdist (p 1) (p 3) - 4 * sqdist (p 1) (p 3) * sqdist (p 2) (p 3) + 2 * sqdist (p 2) (p 3) * sqdist (p 2) (p 3) = 0 := by
    have hrp := re_atom_pair (p 2) (p 1) (p 3) (p 2) (p 1) (p 3)
    rw [R8] at hrp
    simp only [x2, dd, sqdist_self, s12, s13, s23] at hrp
    linear_combination -hrp
  have T9 : (barC (p 1) - barC (p 2)) * (barC (p 3) - barC (p 5)) * (toC (p 1) - toC (p 5)) * (toC (p 2) - toC (p 3)) + (barC (p 1) - barC (p 5)) * (barC (p 2) - barC (p 3)) * (toC (p 1) - toC (p 2)) * (toC (p 3) - toC (p 5)) = 0 :=
    translated_class_21_09
      hdC
      E30
      E47
      E59
      E68
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
  have S9 : atom (p 5) (p 1) (p 3) * atomb (p 2) (p 1) (p 3) + atomb (p 5) (p 1) (p 3) * atom (p 2) (p 1) (p 3) = 0 := by
    simp only [atom, atomb]
    linear_combination (-1 : ℂ) * T9
  have R9 : (atom (p 5) (p 1) (p 3) * atomb (p 2) (p 1) (p 3)).re = 0 := re_zero_of_sum (atomb_mul_atom_eq_conj (p 5) (p 1) (p 3) (p 2) (p 1) (p 3)) S9
  have q9 : 2 * sqdist (p 1) (p 2) * sqdist (p 3) (p 5) - 2 * sqdist (p 1) (p 3) * sqdist (p 2) (p 5) + 2 * sqdist (p 1) (p 5) * sqdist (p 2) (p 3) = 0 := by
    have hrp := re_atom_atomb (p 5) (p 1) (p 3) (p 2) (p 1) (p 3)
    rw [R9] at hrp
    simp only [x2, dd, sqdist_self, s12, s13, s15, s23, s25, s35] at hrp
    linear_combination -hrp
  have T10 : (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) * (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 5)) + (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 5)) * (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) = 0 :=
    translated_class_21_10
      hdR
      E69
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
  have S10 : atom (p 2) (p 1) (p 3) * atom (p 5) (p 2) (p 3) + atomb (p 2) (p 1) (p 3) * atomb (p 5) (p 2) (p 3) = 0 := by
    simp only [atom, atomb]
    linear_combination (-1 : ℂ) * T10
  have R10 : (atom (p 2) (p 1) (p 3) * atom (p 5) (p 2) (p 3)).re = 0 := re_zero_of_sum (atomb_mul_atomb_eq_conj (p 2) (p 1) (p 3) (p 5) (p 2) (p 3)) S10
  have q10 : 2 * sqdist (p 1) (p 2) * sqdist (p 3) (p 5) + 2 * sqdist (p 1) (p 3) * sqdist (p 2) (p 3) - 2 * sqdist (p 1) (p 3) * sqdist (p 3) (p 5) - 2 * sqdist (p 1) (p 5) * sqdist (p 2) (p 3) - 2 * sqdist (p 2) (p 3) * sqdist (p 2) (p 3) + 2 * sqdist (p 2) (p 3) * sqdist (p 2) (p 5) + 2 * sqdist (p 2) (p 3) * sqdist (p 3) (p 5) = 0 := by
    have hrp := re_atom_pair (p 2) (p 1) (p 3) (p 5) (p 2) (p 3)
    rw [R10] at hrp
    simp only [x2, dd, sqdist_self, s12, s23, s25, s35] at hrp
    linear_combination -hrp
  have T11 : (barC (p 3) - barC (p 5)) ^ 2 * (toC (p 2) - toC (p 5)) ^ 2 + (barC (p 2) - barC (p 5)) ^ 2 * (toC (p 3) - toC (p 5)) ^ 2 = 0 :=
    translated_class_21_11
      hdC
      E27
      E30
      E69
      E78
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
  have S11 : atom (p 5) (p 2) (p 3) * atom (p 5) (p 2) (p 3) + atomb (p 5) (p 2) (p 3) * atomb (p 5) (p 2) (p 3) = 0 := by
    simp only [atom, atomb]
    linear_combination (1 : ℂ) * T11
  have R11 : (atom (p 5) (p 2) (p 3) * atom (p 5) (p 2) (p 3)).re = 0 := re_zero_of_sum (atomb_mul_atomb_eq_conj (p 5) (p 2) (p 3) (p 5) (p 2) (p 3)) S11
  have q11 : 2 * sqdist (p 2) (p 3) * sqdist (p 2) (p 3) - 4 * sqdist (p 2) (p 3) * sqdist (p 2) (p 5) - 4 * sqdist (p 2) (p 3) * sqdist (p 3) (p 5) + 2 * sqdist (p 2) (p 5) * sqdist (p 2) (p 5) + 2 * sqdist (p 3) (p 5) * sqdist (p 3) (p 5) = 0 := by
    have hrp := re_atom_pair (p 5) (p 2) (p 3) (p 5) (p 2) (p 3)
    rw [R11] at hrp
    simp only [x2, dd, sqdist_self, s23, s25, s35] at hrp
    linear_combination -hrp
  have neg := certificate_class_21
    (sqdist (p 0) (p 1))
    (sqdist (p 0) (p 2))
    (sqdist (p 0) (p 3))
    (sqdist (p 0) (p 4))
    (sqdist (p 0) (p 5))
    (sqdist (p 1) (p 2))
    (sqdist (p 1) (p 3))
    (sqdist (p 1) (p 4))
    (sqdist (p 1) (p 5))
    (sqdist (p 2) (p 3))
    (sqdist (p 2) (p 4))
    (sqdist (p 2) (p 5))
    (sqdist (p 3) (p 4))
    (sqdist (p 3) (p 5))
    (sqdist (p 4) (p 5))
    q1
    q2
    q3
    q4
    q5
    q6
    q7
    q8
    q9
    q10
    q11
  have P01 : 0 < sqdist (p 0) (p 1) := sqdist_pos (hne 0 1 (by decide))
  have P02 : 0 < sqdist (p 0) (p 2) := sqdist_pos (hne 0 2 (by decide))
  have P03 : 0 < sqdist (p 0) (p 3) := sqdist_pos (hne 0 3 (by decide))
  have P04 : 0 < sqdist (p 0) (p 4) := sqdist_pos (hne 0 4 (by decide))
  have P05 : 0 < sqdist (p 0) (p 5) := sqdist_pos (hne 0 5 (by decide))
  have P12 : 0 < sqdist (p 1) (p 2) := sqdist_pos (hne 1 2 (by decide))
  have P13 : 0 < sqdist (p 1) (p 3) := sqdist_pos (hne 1 3 (by decide))
  have P14 : 0 < sqdist (p 1) (p 4) := sqdist_pos (hne 1 4 (by decide))
  have P15 : 0 < sqdist (p 1) (p 5) := sqdist_pos (hne 1 5 (by decide))
  have P23 : 0 < sqdist (p 2) (p 3) := sqdist_pos (hne 2 3 (by decide))
  have P24 : 0 < sqdist (p 2) (p 4) := sqdist_pos (hne 2 4 (by decide))
  have P25 : 0 < sqdist (p 2) (p 5) := sqdist_pos (hne 2 5 (by decide))
  have P34 : 0 < sqdist (p 3) (p 4) := sqdist_pos (hne 3 4 (by decide))
  have P35 : 0 < sqdist (p 3) (p 5) := sqdist_pos (hne 3 5 (by decide))
  have P45 : 0 < sqdist (p 4) (p 5) := sqdist_pos (hne 4 5 (by decide))
  linarith [neg, mul_pos (mul_pos P01 P23) P35, mul_pos (mul_pos P01 P35) P35, mul_pos (mul_pos P02 P25) P35, mul_pos (mul_pos P02 P35) P35, mul_pos (mul_pos P03 P15) P23, mul_pos (mul_pos P03 P15) P25, mul_pos (mul_pos P03 P15) P35, mul_pos (mul_pos P03 P23) P25, mul_pos (mul_pos P03 P25) P25, mul_pos (mul_pos P03 P25) P35, mul_pos (mul_pos P05 P13) P35, mul_pos (mul_pos P05 P15) P25, mul_pos (mul_pos P05 P35) P35, mul_pos (mul_pos P15 P35) P35, mul_pos (mul_pos P25 P25) P35, mul_pos (mul_pos P25 P35) P35]

/-! ## The class, in the shape of the census -/

/-- The mask of class 21 (entry 20 of `censusRest`). -/
def maskK21 : Mask := 359787030440226329731588

/-- Class 21 is one of the thirty-four census representatives. -/
theorem maskK21_mem : maskK21 ∈ censusRest := by decide

set_option maxHeartbeats 800000 in
/-- **Class 21, sharp form.**  No six points in general position support the
mask of class 21.  Fourteen of its fifteen cells are used: the two lattice
certificates take 2, 9, 20, 27, 30, 47, 59, 60, 68,
and 78, and the eleven translated representatives take 2, 9, 20, 27, 30, 47, 52, 59, 60, 68, 69, 74, 75 and 78. -/
theorem not_supports_k21 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK21) : False := by
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have c9 : Psi (p 3) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 9 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 9 = ((0, 2), (3, 4)) from by decide)] at h
  have c20 : Psi (p 1) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 20 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 20 = ((0, 4), (1, 5)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hs 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  have c47 : Psi (p 3) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 47 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 47 = ((1, 4), (3, 5)) from by decide)] at h
  have c52 : Psi (p 2) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 52 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 52 = ((1, 5), (2, 4)) from by decide)] at h
  have c59 : Psi (p 4) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 59 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 59 = ((2, 3), (4, 5)) from by decide)] at h
  have c60 : Psi (p 0) (p 1) (p 2) (p 4) = 0 := by
    have h := hs 60 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 60 = ((2, 4), (0, 1)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have c69 : Psi (p 1) (p 3) (p 2) (p 5) = 0 := by
    have h := hs 69 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 69 = ((2, 5), (1, 3)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c75 : Psi (p 1) (p 2) (p 3) (p 4) = 0 := by
    have h := hs 75 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 75 = ((3, 4), (1, 2)) from by decide)] at h
  have c78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hs 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  obtain ⟨hR, hC⟩ :=
    degeneracies_of_class_21 p hgp c2 c9 c20 c27 c30 c47 c59 c60 c68 c78
  exact no_general_position_of_the_degeneracies_21 p hgp
    c2 c9 c20 c27 c30 c47 c52 c59 c60 c68 c69 c74 c75 c78 hR hC

/-- **Class 21.**  No six points in general position carry the mask of
class 21. -/
theorem not_carries_k21 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK21) : False :=
  not_supports_k21 p hgp (supports_of_carries hc)



end QU7

end DistinctCircumradii

#print axioms DistinctCircumradii.QU7.sq_split
#print axioms DistinctCircumradii.QU7.re_eq_zero_of_eq_neg_conj
#print axioms DistinctCircumradii.QU7.im_eq_zero_of_eq_conj
#print axioms DistinctCircumradii.QU7.re_atom
#print axioms DistinctCircumradii.QU7.im_atom
#print axioms DistinctCircumradii.QU7.im_pair
#print axioms DistinctCircumradii.QU7.re_atom_pair
#print axioms DistinctCircumradii.QU7.sqdist_pos
#print axioms DistinctCircumradii.QU7.atomb_eq_conj
#print axioms DistinctCircumradii.QU7.x2_eq_two_qq
#print axioms DistinctCircumradii.QU7.atom_add_atomb_eq_zero
#print axioms DistinctCircumradii.QU7.eq_of_cert
#print axioms DistinctCircumradii.QU7.im_cyclicValue
#print axioms DistinctCircumradii.QU7.cyclicValueBar_eq_conj
#print axioms DistinctCircumradii.QU7.cyc_add_bar_eq_zero
#print axioms DistinctCircumradii.QU7.sqdist_comm
#print axioms DistinctCircumradii.QU7.re_cyclic_sum
#print axioms DistinctCircumradii.QU7.sqdist_self
#print axioms DistinctCircumradii.QU7.atom_eq_conj_atomb
#print axioms DistinctCircumradii.QU7.atomb_mul_atomb_eq_conj
#print axioms DistinctCircumradii.QU7.atomb_mul_atom_eq_conj
#print axioms DistinctCircumradii.QU7.re_zero_of_sum
#print axioms DistinctCircumradii.QU7.re_atom_atomb
#print axioms DistinctCircumradii.QU7.rightAnglePairClass
#print axioms DistinctCircumradii.QU7.crossRatioPairClass
#print axioms DistinctCircumradii.QU7.translated_class_21_01
#print axioms DistinctCircumradii.QU7.translated_class_21_02
#print axioms DistinctCircumradii.QU7.translated_class_21_03
#print axioms DistinctCircumradii.QU7.translated_class_21_04
#print axioms DistinctCircumradii.QU7.translated_class_21_05
#print axioms DistinctCircumradii.QU7.translated_class_21_06
#print axioms DistinctCircumradii.QU7.translated_class_21_07
#print axioms DistinctCircumradii.QU7.translated_class_21_08
#print axioms DistinctCircumradii.QU7.translated_class_21_09
#print axioms DistinctCircumradii.QU7.translated_class_21_10
#print axioms DistinctCircumradii.QU7.translated_class_21_11
#print axioms DistinctCircumradii.QU7.certificate_class_21
#print axioms DistinctCircumradii.QU7.cellPsi_eq
#print axioms DistinctCircumradii.QU7.degeneracies_of_class_21
#print axioms DistinctCircumradii.QU7.no_general_position_of_the_degeneracies_21
#print axioms DistinctCircumradii.QU7.maskK21_mem
#print axioms DistinctCircumradii.QU7.not_supports_k21
#print axioms DistinctCircumradii.QU7.not_carries_k21
