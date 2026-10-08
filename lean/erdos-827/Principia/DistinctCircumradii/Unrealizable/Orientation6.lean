import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU6` の k20

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QU6

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

/-! ### The lattice certificates, one declaration each

Splitting these off keeps each `ring` / `linear_combination` in its own
declaration, which is what keeps the elaboration inside the memory budget. -/

set_option maxHeartbeats 400000 in
theorem lattice_step_one (p : Fin 6 → Pt)
    (hw5 : Psi (p 1) (p 5) (p 0) (p 4) = 0)
    (hw7 : Psi (p 0) (p 4) (p 1) (p 2) = 0) :
    (toC (p 0) - toC (p 1)) ^ 2 * ((toC (p 1) - toC (p 4)) * (barC (p 5) - barC (p 0)) * (barC (p 5) - barC (p 4)) * (toC (p 0) - toC (p 2)) * (barC (p 4) - barC (p 1)) * (barC (p 4) - barC (p 2)))
      = (barC (p 0) - barC (p 1)) ^ 2 * ((barC (p 1) - barC (p 4)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (toC (p 4) - toC (p 1)) * (toC (p 4) - toC (p 2))) := by
  have E5 := witnessEq hw5
  have E7 := witnessEq hw7
  linear_combination -((toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) * (barC (p 4) - barC (p 1)) * (barC (p 4) - barC (p 2))) * E5 - ((barC (p 1) - barC (p 0)) * (barC (p 1) - barC (p 4)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 4))) * E7

set_option maxHeartbeats 400000 in
theorem lattice_step_two (p : Fin 6 → Pt)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw13 : Psi (p 1) (p 4) (p 2) (p 5) = 0) :
    (toC (p 1) - toC (p 2)) ^ 2 * ((toC (p 2) - toC (p 0)) * (barC (p 5) - barC (p 0)) * (barC (p 5) - barC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 5)))
      = (barC (p 1) - barC (p 2)) ^ 2 * ((barC (p 2) - barC (p 0)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 1)) * (barC (p 1) - barC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 5))) := by
  have E1 := witnessEq hw1
  have E13 := witnessEq hw13
  linear_combination -((toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 5)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 5))) * E1 - ((barC (p 2) - barC (p 0)) * (barC (p 2) - barC (p 1)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 1))) * E13

set_option maxHeartbeats 400000 in
theorem pairing_identity_one (p : Fin 6 → Pt) :
    ((toC (p 1) - toC (p 4)) * (barC (p 5) - barC (p 0)) * (barC (p 5) - barC (p 4)) * (toC (p 0) - toC (p 2)) * (barC (p 4) - barC (p 1)) * (barC (p 4) - barC (p 2))) * ((barC (p 2) - barC (p 0)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 1)) * (barC (p 1) - barC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 5)))
      = ((toC (p 2) - toC (p 0)) * (barC (p 5) - barC (p 0)) * (barC (p 5) - barC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 5))) * ((barC (p 1) - barC (p 4)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (toC (p 4) - toC (p 1)) * (toC (p 4) - toC (p 2))) := by
  ring

set_option maxHeartbeats 400000 in
theorem lattice_step_three (p : Fin 6 → Pt)
    (hw13 : Psi (p 1) (p 4) (p 2) (p 5) = 0)
    (hw9 : Psi (p 3) (p 5) (p 1) (p 4) = 0) :
    (toC (p 1) - toC (p 5)) ^ 2 * ((toC (p 1) - toC (p 2)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 5)) * (barC (p 3) - barC (p 1)) * (barC (p 3) - barC (p 4)) * (toC (p 5) - toC (p 4)))
      = (barC (p 1) - barC (p 5)) ^ 2 * ((barC (p 1) - barC (p 2)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 5)) * (toC (p 3) - toC (p 1)) * (toC (p 3) - toC (p 4)) * (barC (p 5) - barC (p 4))) := by
  have E13 := witnessEq hw13
  have E9 := witnessEq hw9
  linear_combination -((barC (p 3) - barC (p 1)) * (barC (p 3) - barC (p 4)) * (toC (p 5) - toC (p 1)) * (toC (p 5) - toC (p 4))) * E13 + ((barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 5))) * E9

set_option maxHeartbeats 400000 in
theorem lattice_step_four (p : Fin 6 → Pt)
    (hw10 : Psi (p 2) (p 3) (p 1) (p 5) = 0)
    (hw11 : Psi (p 4) (p 5) (p 2) (p 3) = 0) :
    (toC (p 2) - toC (p 5)) ^ 2 * ((toC (p 2) - toC (p 1)) * (barC (p 3) - barC (p 1)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 3)) * (toC (p 5) - toC (p 3)))
      = (barC (p 2) - barC (p 5)) ^ 2 * ((barC (p 2) - barC (p 1)) * (toC (p 3) - toC (p 1)) * (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 3)) * (barC (p 5) - barC (p 3))) := by
  have E10 := witnessEq hw10
  have E11 := witnessEq hw11
  linear_combination -((barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 3)) * (toC (p 5) - toC (p 2)) * (toC (p 5) - toC (p 3))) * E10 + ((barC (p 2) - barC (p 1)) * (barC (p 2) - barC (p 5)) * (toC (p 3) - toC (p 1)) * (toC (p 3) - toC (p 5))) * E11

set_option maxHeartbeats 400000 in
theorem pairing_identity_two (p : Fin 6 → Pt) :
    ((toC (p 1) - toC (p 2)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 5)) * (barC (p 3) - barC (p 1)) * (barC (p 3) - barC (p 4)) * (toC (p 5) - toC (p 4))) * ((barC (p 2) - barC (p 1)) * (toC (p 3) - toC (p 1)) * (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 3)) * (barC (p 5) - barC (p 3)))
      = ((toC (p 2) - toC (p 1)) * (barC (p 3) - barC (p 1)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 3)) * (toC (p 5) - toC (p 3))) * ((barC (p 1) - barC (p 2)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 5)) * (toC (p 3) - toC (p 1)) * (toC (p 3) - toC (p 4)) * (barC (p 5) - barC (p 4))) := by
  ring


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

/-! ### One pattern of fifteen witnesses on six points

The pattern is the direction class whose lattice has elementary divisors
`1⁹, 2, 2, 2, 2`; its torsion is `(ℤ/2)⁴`, so sixteen branches, and twelve of
them die because a collinearity form is forced.  Only two collinearity forms lie
in the saturation, at the vertices `p 1` and `p 5`, with the certificates

  `2 * (e_{01} - e_{12}) = F₅ + F₇ - F₁ - F₁₃`
  `2 * (e_{15} - e_{25}) = (F₁₃ - F₉) + (F₁₁ - F₁₀)`,

so both angles are right angles.  The four surviving branches are then killed by
*one* further reading: the class of the second right angle also contains

  `G = (e_{02} - e_{05}) + (e_{12} - e_{25}) = (e_{15} - e_{25}) + F₁`,

which is a product of **two** atoms, and `Re` of a two-atom product is a
distance polynomial of degree two (`re_atom_pair`).  The three vanishing facts
then combine with positive coefficients into a positive sum of distance
monomials, which is the contradiction.  Only seven of the fifteen witnesses are
used. -/

set_option maxHeartbeats 400000 in
/-- **Both angles are right angles.**  The two collinearity forms of the
saturation, at the vertices `p 1` and `p 5`, have order two in `ℤ¹⁵ / L(S)`; the
collinear alternative is excluded by general position. -/
theorem right_angles_of_the_orientation_class
    (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw5 : Psi (p 1) (p 5) (p 0) (p 4) = 0)
    (hw7 : Psi (p 0) (p 4) (p 1) (p 2) = 0)
    (hw9 : Psi (p 3) (p 5) (p 1) (p 4) = 0)
    (hw10 : Psi (p 2) (p 3) (p 1) (p 5) = 0)
    (hw11 : Psi (p 4) (p 5) (p 2) (p 3) = 0)
    (hw13 : Psi (p 1) (p 4) (p 2) (p 5) = 0) :
    qq (p 0) (p 2) (p 1) = 0 ∧ qq (p 1) (p 2) (p 5) = 0 := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have n01 : p 0 ≠ p 1 := hne 0 1 (by decide)
  have n02 : p 0 ≠ p 2 := hne 0 2 (by decide)
  have n03 : p 0 ≠ p 3 := hne 0 3 (by decide)
  have n04 : p 0 ≠ p 4 := hne 0 4 (by decide)
  have n05 : p 0 ≠ p 5 := hne 0 5 (by decide)
  have n12 : p 1 ≠ p 2 := hne 1 2 (by decide)
  have n13 : p 1 ≠ p 3 := hne 1 3 (by decide)
  have n14 : p 1 ≠ p 4 := hne 1 4 (by decide)
  have n15 : p 1 ≠ p 5 := hne 1 5 (by decide)
  have n23 : p 2 ≠ p 3 := hne 2 3 (by decide)
  have n24 : p 2 ≠ p 4 := hne 2 4 (by decide)
  have n25 : p 2 ≠ p 5 := hne 2 5 (by decide)
  have n34 : p 3 ≠ p 4 := hne 3 4 (by decide)
  have n35 : p 3 ≠ p 5 := hne 3 5 (by decide)
  have n45 : p 4 ≠ p 5 := hne 4 5 (by decide)
  have E1 := witnessEq hw1
  have E5 := witnessEq hw5
  have E7 := witnessEq hw7
  have E9 := witnessEq hw9
  have E10 := witnessEq hw10
  have E11 := witnessEq hw11
  have E13 := witnessEq hw13
  -- first right angle, at `p 1`
  have ha1 := lattice_step_one p hw5 hw7
  have hb1 := lattice_step_two p hw1 hw13
  have hPQ1 := pairing_identity_one p
  have hP1 : ((toC (p 1) - toC (p 4)) * (barC (p 5) - barC (p 0)) * (barC (p 5) - barC (p 4)) * (toC (p 0) - toC (p 2)) * (barC (p 4) - barC (p 1)) * (barC (p 4) - barC (p 2))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact toC_sub_ne_zero n14
    · exact barC_sub_ne_zero n05.symm
    · exact barC_sub_ne_zero n45.symm
    · exact toC_sub_ne_zero n02
    · exact barC_sub_ne_zero n14.symm
    · exact barC_sub_ne_zero n24.symm
  have hQ1 : ((barC (p 2) - barC (p 0)) * (toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 1)) * (barC (p 1) - barC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 5))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact barC_sub_ne_zero n02.symm
    · exact toC_sub_ne_zero n05.symm
    · exact toC_sub_ne_zero n15.symm
    · exact barC_sub_ne_zero n15
    · exact toC_sub_ne_zero n24.symm
    · exact toC_sub_ne_zero n45
  have hsq1 : (toC (p 0) - toC (p 1)) ^ 2 * (barC (p 1) - barC (p 2)) ^ 2
      = (barC (p 0) - barC (p 1)) ^ 2 * (toC (p 1) - toC (p 2)) ^ 2 :=
    sq_mul_sq_eq_of_two_products ha1 hb1 hPQ1 hP1 hQ1
  -- second right angle, at `p 5`
  have ha2 := lattice_step_three p hw13 hw9
  have hb2 := lattice_step_four p hw10 hw11
  have hPQ2 := pairing_identity_two p
  have hP2 : ((toC (p 1) - toC (p 2)) * (barC (p 4) - barC (p 2)) * (barC (p 4) - barC (p 5)) * (barC (p 3) - barC (p 1)) * (barC (p 3) - barC (p 4)) * (toC (p 5) - toC (p 4))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact toC_sub_ne_zero n12
    · exact barC_sub_ne_zero n24.symm
    · exact barC_sub_ne_zero n45
    · exact barC_sub_ne_zero n13.symm
    · exact barC_sub_ne_zero n34
    · exact toC_sub_ne_zero n45.symm
  have hQ2 : ((barC (p 2) - barC (p 1)) * (toC (p 3) - toC (p 1)) * (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 2)) * (toC (p 4) - toC (p 3)) * (barC (p 5) - barC (p 3))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact barC_sub_ne_zero n12.symm
    · exact toC_sub_ne_zero n13.symm
    · exact toC_sub_ne_zero n35
    · exact toC_sub_ne_zero n24.symm
    · exact toC_sub_ne_zero n34.symm
    · exact barC_sub_ne_zero n35.symm
  have hsq2 : (toC (p 1) - toC (p 5)) ^ 2 * (barC (p 2) - barC (p 5)) ^ 2
      = (barC (p 1) - barC (p 5)) ^ 2 * (toC (p 2) - toC (p 5)) ^ 2 :=
    sq_mul_sq_eq_of_two_products ha2 hb2 hPQ2 hP2 hQ2
  -- read the two right angles off
  have hcr1 : cross (p 1) (p 0) (p 2) ≠ 0 := by
    have h : cross (p 0) (p 1) (p 2) ≠ 0 := by
      have hh := hcol 0 1 2 (by decide) (by decide)
      simpa [Collinear3] using hh
    intro hz
    apply h
    simp only [cross] at hz ⊢
    linarith
  have hcr2 : cross (p 5) (p 1) (p 2) ≠ 0 := by
    have h : cross (p 1) (p 2) (p 5) ≠ 0 := by
      have hh := hcol 1 2 5 (by decide) (by decide)
      simpa [Collinear3] using hh
    intro hz
    apply h
    simp only [cross] at hz ⊢
    linarith
  have hr1 : qq (p 0) (p 2) (p 1) * cross (p 1) (p 0) (p 2) = 0 := by
    refine qq_mul_cross_eq_zero_of_sq_eq (a := p 1) (b := p 0) (c := p 2) ?_
    linear_combination hsq1
  have hr2 : qq (p 1) (p 2) (p 5) * cross (p 5) (p 1) (p 2) = 0 := by
    refine qq_mul_cross_eq_zero_of_sq_eq (a := p 5) (b := p 1) (c := p 2) ?_
    linear_combination hsq2
  have h1 : qq (p 0) (p 2) (p 1) = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact h
    · exact absurd h hcr1
  have h2 : qq (p 1) (p 2) (p 5) = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact h
    · exact absurd h hcr2
  exact ⟨h1, h2⟩

set_option maxHeartbeats 400000 in
/-- **No six points in general position carry this pattern of witnesses.**
The two right angles are the ones its companion file derives from seven
equal-circumradius conditions; `hw1` is one of those seven.  The proof reads the
class of the second right angle a second time, at the translated representative
`G = (e₁₅ - e₂₅) + F₁`, which is a product of two atoms, so that `Re` of it is a
distance polynomial of degree two. -/
theorem no_general_position_of_two_right_angles_and_a_translated_class
    (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (h1 : qq (p 0) (p 2) (p 1) = 0)
    (h2 : qq (p 1) (p 2) (p 5) = 0) :
    False := by
  have hne := hgp.1
  have n05 : p 0 ≠ p 5 := hne 0 5 (by decide)
  have n15 : p 1 ≠ p 5 := hne 1 5 (by decide)
  have n25 : p 2 ≠ p 5 := hne 2 5 (by decide)
  have E1 := witnessEq hw1
  -- the same class read at the translated representative `G = (e15 - e25) + F1`
  have hAv : (toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 2))
      + (barC (p 5) - barC (p 1)) * (toC (p 5) - toC (p 2)) = 0 := by
    have hh := atom_add_atomb_eq_zero (a := p 5) (b := p 1) (c := p 2) h2
    simpa [atom, atomb] using hh
  have hkey : ((toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 1)))
      * (atom (p 0) (p 2) (p 5) * atom (p 2) (p 1) (p 5)
          + atomb (p 0) (p 2) (p 5) * atomb (p 2) (p 1) (p 5)) = 0 := by
    simp only [atom, atomb]
    linear_combination (-((toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 2)))) * E1
      - ((barC (p 2) - barC (p 0)) * (barC (p 2) - barC (p 1))
          * ((toC (p 5) - toC (p 0)) * (toC (p 5) - toC (p 1)))) * hAv
  have hM : ((toC (p 5) - toC (p 1)) * (barC (p 5) - barC (p 1))) ≠ 0 :=
    mul_ne_zero (toC_sub_ne_zero n15.symm) (barC_sub_ne_zero n15.symm)
  have hsum : atom (p 0) (p 2) (p 5) * atom (p 2) (p 1) (p 5)
      + atomb (p 0) (p 2) (p 5) * atomb (p 2) (p 1) (p 5) = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hM
    · exact h
  have hre : (atom (p 0) (p 2) (p 5) * atom (p 2) (p 1) (p 5)).re = 0 := by
    have hb : atomb (p 0) (p 2) (p 5) * atomb (p 2) (p 1) (p 5)
        = (starRingEnd ℂ) (atom (p 0) (p 2) (p 5) * atom (p 2) (p 1) (p 5)) := by
      rw [atomb_eq_conj, atomb_eq_conj, map_mul]
    rw [hb] at hsum
    have := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  -- the degree-two certificate
  have hx1 : x2 (p 1) (p 0) (p 2) = 0 := by rw [x2_eq_two_qq, h1]; ring
  have hx2 : x2 (p 5) (p 1) (p 2) = 0 := by rw [x2_eq_two_qq, h2]; ring
  -- the two-atom bridge turns the vanishing real part into a distance identity
  have hrp := re_atom_pair (p 0) (p 2) (p 5) (p 2) (p 1) (p 5)
  rw [hre] at hrp
  have hzero : x2 (p 0) (p 2) (p 5) * x2 (p 2) (p 1) (p 5)
      - (dd (p 2) (p 0) (p 1) (p 2) * dd (p 5) (p 0) (p 5) (p 2)
          - dd (p 2) (p 0) (p 5) (p 2) * dd (p 5) (p 0) (p 1) (p 2)) = 0 := by
    linarith [hrp]
  have cert : sqdist (p 2) (p 5) * x2 (p 1) (p 0) (p 2)
      + sqdist (p 0) (p 5) * x2 (p 5) (p 1) (p 2)
      + sqdist (p 2) (p 5) * x2 (p 5) (p 1) (p 2)
      + (x2 (p 0) (p 2) (p 5) * x2 (p 2) (p 1) (p 5)
          - (dd (p 2) (p 0) (p 1) (p 2) * dd (p 5) (p 0) (p 5) (p 2)
              - dd (p 2) (p 0) (p 5) (p 2) * dd (p 5) (p 0) (p 1) (p 2))) / 2
      = 2 * (sqdist (p 0) (p 5) * sqdist (p 2) (p 5))
        + 2 * (sqdist (p 1) (p 5) * sqdist (p 2) (p 5)) := by
    simp only [x2, dd, sqdist]
    ring
  rw [hx1, hx2, hzero] at cert
  have p05 := sqdist_pos n05
  have p15 := sqdist_pos n15
  have p25 := sqdist_pos n25
  nlinarith [cert, mul_pos p05 p25, mul_pos p15 p25]

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## The class, in the shape of the census -/

/-- The mask of class 20 (entry 19 of `censusRest`). -/
def maskK20 : Mask := 322304397152704277779468

/-- Class 20 is one of the thirty-four census representatives. -/
theorem maskK20_mem : maskK20 ∈ censusRest := by decide

set_option maxHeartbeats 800000 in
/-- **Class 20, sharp form.**  No six points in general position support the
mask of class 20.  Seven of its fifteen cells are used: the ones with indices
2, 20, 31, 47, 51, 59 and 70. -/
theorem not_supports_k20 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK20) : False := by
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have c20 : Psi (p 1) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 20 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 20 = ((0, 4), (1, 5)) from by decide)] at h
  have c31 : Psi (p 0) (p 4) (p 1) (p 2) = 0 := by
    have h := hs 31 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 31 = ((1, 2), (0, 4)) from by decide)] at h
  have c47 : Psi (p 3) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 47 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 47 = ((1, 4), (3, 5)) from by decide)] at h
  have c51 : Psi (p 2) (p 3) (p 1) (p 5) = 0 := by
    have h := hs 51 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 51 = ((1, 5), (2, 3)) from by decide)] at h
  have c59 : Psi (p 4) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 59 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 59 = ((2, 3), (4, 5)) from by decide)] at h
  have c70 : Psi (p 1) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 70 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 70 = ((2, 5), (1, 4)) from by decide)] at h
  obtain ⟨h1, h2⟩ :=
    right_angles_of_the_orientation_class p hgp c2 c20 c31 c47 c51 c59 c70
  exact no_general_position_of_two_right_angles_and_a_translated_class p hgp c2 h1 h2

/-- **Class 20.**  No six points in general position carry the mask of
class 20. -/
theorem not_carries_k20 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK20) : False :=
  not_supports_k20 p hgp (supports_of_carries hc)



end QU6

end DistinctCircumradii

#print axioms DistinctCircumradii.QU6.sq_split
#print axioms DistinctCircumradii.QU6.re_eq_zero_of_eq_neg_conj
#print axioms DistinctCircumradii.QU6.im_eq_zero_of_eq_conj
#print axioms DistinctCircumradii.QU6.re_atom
#print axioms DistinctCircumradii.QU6.im_atom
#print axioms DistinctCircumradii.QU6.im_pair
#print axioms DistinctCircumradii.QU6.re_atom_pair
#print axioms DistinctCircumradii.QU6.sqdist_pos
#print axioms DistinctCircumradii.QU6.lattice_step_one
#print axioms DistinctCircumradii.QU6.lattice_step_two
#print axioms DistinctCircumradii.QU6.pairing_identity_one
#print axioms DistinctCircumradii.QU6.lattice_step_three
#print axioms DistinctCircumradii.QU6.lattice_step_four
#print axioms DistinctCircumradii.QU6.pairing_identity_two
#print axioms DistinctCircumradii.QU6.atomb_eq_conj
#print axioms DistinctCircumradii.QU6.x2_eq_two_qq
#print axioms DistinctCircumradii.QU6.atom_add_atomb_eq_zero
#print axioms DistinctCircumradii.QU6.right_angles_of_the_orientation_class
#print axioms DistinctCircumradii.QU6.no_general_position_of_two_right_angles_and_a_translated_class
#print axioms DistinctCircumradii.QU6.cellPsi_eq
#print axioms DistinctCircumradii.QU6.maskK20_mem
#print axioms DistinctCircumradii.QU6.not_supports_k20
#print axioms DistinctCircumradii.QU6.not_carries_k20
