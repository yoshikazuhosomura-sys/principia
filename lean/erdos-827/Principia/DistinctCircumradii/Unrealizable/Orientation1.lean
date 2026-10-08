import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU1` の k1

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

set_option linter.unusedVariables false

namespace QU1

/-- **No six points in general position carry these seven witnesses.**  The
argument uses only the seven equal-circumradius conditions, eleven
non-coincidences and one non-collinearity. -/
theorem no_six_points_of_seven_witnesses (a b c d e f : Pt)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbf : b ≠ f)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hef : e ≠ f)
    (hcr : cross a b c ≠ 0)
    (hw1 : Psi c d a b = 0) (hw2 : Psi b e a c = 0) (hw3 : Psi c e a f = 0)
    (hw4 : Psi a f b c = 0) (hw5 : Psi a d b e = 0) (hw6 : Psi c f b e = 0)
    (hw7 : Psi a e c d = 0) :
    False := by
  have E1 := witnessEq hw1
  have E2 := witnessEq hw2
  have E3 := witnessEq hw3
  have E4 := witnessEq hw4
  have E5 := witnessEq hw5
  have E6 := witnessEq hw6
  have E7 := witnessEq hw7
  -- first certificate: `2 * (e_ab - e_ac)` lies in the lattice
  have ha1 : (toC a - toC b) ^ 2 *
      ((toC b - toC c) * (toC a - toC e) * (barC a - barC e) * (barC c - barC e) *
        (barC b - barC d) * (barC d - barC e))
      = (barC a - barC b) ^ 2 *
      ((barC b - barC c) * (barC a - barC e) * (toC a - toC e) * (toC c - toC e) *
        (toC b - toC d) * (toC d - toC e)) := by
    linear_combination
      ((toC a - toC b) * (toC a - toC e) * ((barC d - barC b) * (barC d - barC e))) * E2
      + ((barC b - barC a) * (barC b - barC c) * ((toC e - toC a) * (toC e - toC c))) * E5
  have hb1 : (toC a - toC c) ^ 2 *
      ((toC b - toC c) * (toC a - toC d) * (barC a - barC d) * (barC b - barC d) *
        (barC c - barC e) * (barC d - barC e))
      = (barC a - barC c) ^ 2 *
      ((barC b - barC c) * (barC a - barC d) * (toC a - toC d) * (toC b - toC d) *
        (toC c - toC e) * (toC d - toC e)) := by
    linear_combination
      ((toC a - toC c) * (toC a - toC d) * ((barC e - barC c) * (barC e - barC d))) * E1
      + ((barC c - barC a) * (barC c - barC b) * ((toC d - toC a) * (toC d - toC b))) * E7
  have hP1 : ((toC b - toC c) * (toC a - toC e) * (barC a - barC e) * (barC c - barC e) *
      (barC b - barC d) * (barC d - barC e)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact toC_sub_ne_zero hbc
    · exact toC_sub_ne_zero hae
    · exact barC_sub_ne_zero hae
    · exact barC_sub_ne_zero hce
    · exact barC_sub_ne_zero hbd
    · exact barC_sub_ne_zero hde
  have hQ1 : ((barC b - barC c) * (barC a - barC d) * (toC a - toC d) * (toC b - toC d) *
      (toC c - toC e) * (toC d - toC e)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact barC_sub_ne_zero hbc
    · exact barC_sub_ne_zero had
    · exact toC_sub_ne_zero had
    · exact toC_sub_ne_zero hbd
    · exact toC_sub_ne_zero hce
    · exact toC_sub_ne_zero hde
  have hPQ1 : ((toC b - toC c) * (toC a - toC e) * (barC a - barC e) * (barC c - barC e) *
        (barC b - barC d) * (barC d - barC e)) *
      ((barC b - barC c) * (barC a - barC d) * (toC a - toC d) * (toC b - toC d) *
        (toC c - toC e) * (toC d - toC e))
      = ((toC b - toC c) * (toC a - toC d) * (barC a - barC d) * (barC b - barC d) *
        (barC c - barC e) * (barC d - barC e)) *
      ((barC b - barC c) * (barC a - barC e) * (toC a - toC e) * (toC c - toC e) *
        (toC b - toC d) * (toC d - toC e)) := by
    ring
  have hsq1 : (toC a - toC b) ^ 2 * (barC a - barC c) ^ 2
      = (barC a - barC b) ^ 2 * (toC a - toC c) ^ 2 :=
    sq_mul_sq_eq_of_two_products ha1 hb1 hPQ1 hP1 hQ1
  -- second certificate: `2 * (e_ac - e_bc)` lies in the lattice
  have ha2 : (toC a - toC c) ^ 2 *
      ((toC a - toC b) * (toC c - toC f) * (barC a - barC e) * (barC e - barC f) *
        (barC b - barC f) * (barC c - barC f))
      = (barC a - barC c) ^ 2 *
      ((barC a - barC b) * (barC c - barC f) * (toC a - toC e) * (toC e - toC f) *
        (toC b - toC f) * (toC c - toC f)) := by
    linear_combination
      ((toC a - toC b) * (toC a - toC c) * ((barC f - barC b) * (barC f - barC c))) * E3
      + ((barC c - barC a) * (barC c - barC f) * ((toC e - toC a) * (toC e - toC f))) * E4
  have hb2 : (toC b - toC c) ^ 2 *
      ((toC a - toC b) * (toC c - toC e) * (barC a - barC e) * (barC c - barC e) *
        (barC b - barC f) * (barC e - barC f))
      = (barC b - barC c) ^ 2 *
      ((barC a - barC b) * (barC c - barC e) * (toC a - toC e) * (toC c - toC e) *
        (toC b - toC f) * (toC e - toC f)) := by
    linear_combination
      ((toC c - toC b) * (toC c - toC e) * ((barC f - barC b) * (barC f - barC e))) * E2
      + ((barC b - barC a) * (barC b - barC c) * ((toC e - toC a) * (toC e - toC c))) * E6
  have hP2 : ((toC a - toC b) * (toC c - toC f) * (barC a - barC e) * (barC e - barC f) *
      (barC b - barC f) * (barC c - barC f)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact toC_sub_ne_zero hab
    · exact toC_sub_ne_zero hcf
    · exact barC_sub_ne_zero hae
    · exact barC_sub_ne_zero hef
    · exact barC_sub_ne_zero hbf
    · exact barC_sub_ne_zero hcf
  have hQ2 : ((barC a - barC b) * (barC c - barC e) * (toC a - toC e) * (toC c - toC e) *
      (toC b - toC f) * (toC e - toC f)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact barC_sub_ne_zero hab
    · exact barC_sub_ne_zero hce
    · exact toC_sub_ne_zero hae
    · exact toC_sub_ne_zero hce
    · exact toC_sub_ne_zero hbf
    · exact toC_sub_ne_zero hef
  have hPQ2 : ((toC a - toC b) * (toC c - toC f) * (barC a - barC e) * (barC e - barC f) *
        (barC b - barC f) * (barC c - barC f)) *
      ((barC a - barC b) * (barC c - barC e) * (toC a - toC e) * (toC c - toC e) *
        (toC b - toC f) * (toC e - toC f))
      = ((toC a - toC b) * (toC c - toC e) * (barC a - barC e) * (barC c - barC e) *
        (barC b - barC f) * (barC e - barC f)) *
      ((barC a - barC b) * (barC c - barC f) * (toC a - toC e) * (toC e - toC f) *
        (toC b - toC f) * (toC c - toC f)) := by
    ring
  have hsq2 : (toC a - toC c) ^ 2 * (barC b - barC c) ^ 2
      = (barC a - barC c) ^ 2 * (toC b - toC c) ^ 2 :=
    sq_mul_sq_eq_of_two_products ha2 hb2 hPQ2 hP2 hQ2
  -- read the two right angles off
  have hr1 : qq b c a * cross a b c = 0 := by
    refine qq_mul_cross_eq_zero_of_sq_eq ?_
    linear_combination hsq1
  have hr2 : qq a b c * cross c a b = 0 := by
    refine qq_mul_cross_eq_zero_of_sq_eq (a := c) (b := a) (c := b) ?_
    linear_combination hsq2
  have hcr' : cross c a b ≠ 0 := by
    have hc : cross c a b = cross a b c := by simp only [cross]; ring
    rw [hc]
    exact hcr
  have h1 : qq b c a = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact h
    · exact absurd h hcr
  have h2 : qq a b c = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact h
    · exact absurd h hcr'
  exact hac (eq_of_sqdist_eq_zero (sqdist_eq_zero_of_two_right_angles h1 h2))

/-- The same statement for a general-position family of six points. -/
theorem no_general_position_of_seven_witnesses (p : Fin 6 → Pt)
    (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 3) (p 0) (p 1) = 0)
    (hw2 : Psi (p 1) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 2) (p 4) (p 0) (p 5) = 0)
    (hw4 : Psi (p 0) (p 5) (p 1) (p 2) = 0)
    (hw5 : Psi (p 0) (p 3) (p 1) (p 4) = 0)
    (hw6 : Psi (p 2) (p 5) (p 1) (p 4) = 0)
    (hw7 : Psi (p 0) (p 4) (p 2) (p 3) = 0) :
    False := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have hcr : cross (p 0) (p 1) (p 2) ≠ 0 := by
    have h := hcol 0 1 2 (by decide) (by decide)
    simpa [Collinear3] using h
  exact no_six_points_of_seven_witnesses (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 0 4 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
    (hne 1 5 (by decide)) (hne 2 4 (by decide)) (hne 2 5 (by decide))
    (hne 3 4 (by decide)) (hne 4 5 (by decide))
    hcr hw1 hw2 hw3 hw4 hw5 hw6 hw7

set_option linter.unusedVariables false

/-- The fifteen cells of the direction class, as a statement about the whole
witness pattern: a configuration in general position cannot have all fifteen.
Only seven of the fifteen are used. -/
theorem no_general_position_of_fifteen_witnesses (p : Fin 6 → Pt)
    (hgp : GeneralPosition p)
    (h00 : Psi (p 2) (p 3) (p 0) (p 1) = 0)
    (h07 : Psi (p 1) (p 4) (p 0) (p 2) = 0)
    (h17 : Psi (p 4) (p 5) (p 0) (p 3) = 0)
    (h20 : Psi (p 1) (p 5) (p 0) (p 4) = 0)
    (h25 : Psi (p 1) (p 3) (p 0) (p 5) = 0)
    (h28 : Psi (p 2) (p 4) (p 0) (p 5) = 0)
    (h32 : Psi (p 0) (p 5) (p 1) (p 2) = 0)
    (h39 : Psi (p 2) (p 4) (p 1) (p 3) = 0)
    (h43 : Psi (p 0) (p 3) (p 1) (p 4) = 0)
    (h46 : Psi (p 2) (p 5) (p 1) (p 4) = 0)
    (h53 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    (h55 : Psi (p 0) (p 4) (p 2) (p 3) = 0)
    (h58 : Psi (p 1) (p 5) (p 2) (p 3) = 0)
    (h65 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (h67 : Psi (p 0) (p 3) (p 2) (p 5) = 0) :
    False :=
  no_general_position_of_seven_witnesses p hgp h00 h07 h28 h32 h43 h46 h55

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## The direction classes, in the shape of the census -/

/-! ### Class 1 -/

/-- The mask of class 1 (entry 0 of `censusRest`). -/
def maskK1 : Mask := 184800786828712083585

/-- Class 1 is one of the thirty-four census representatives. -/
theorem maskK1_mem : maskK1 ∈ censusRest := by decide

/-- **Class 1, sharp form.**  No six points in general position support
the mask of class 1.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k1 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK1) : False := by
  have c0 : Psi (p 2) (p 3) (p 0) (p 1) = 0 := by
    have h := hs 0 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 0 = ((0, 1), (2, 3)) from by decide)] at h
  have c7 : Psi (p 1) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 7 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 7 = ((0, 2), (1, 4)) from by decide)] at h
  have c17 : Psi (p 4) (p 5) (p 0) (p 3) = 0 := by
    have h := hs 17 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 17 = ((0, 3), (4, 5)) from by decide)] at h
  have c20 : Psi (p 1) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 20 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 20 = ((0, 4), (1, 5)) from by decide)] at h
  have c25 : Psi (p 1) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 25 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 25 = ((0, 5), (1, 3)) from by decide)] at h
  have c28 : Psi (p 2) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 28 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 28 = ((0, 5), (2, 4)) from by decide)] at h
  have c32 : Psi (p 0) (p 5) (p 1) (p 2) = 0 := by
    have h := hs 32 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 32 = ((1, 2), (0, 5)) from by decide)] at h
  have c39 : Psi (p 2) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 39 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 39 = ((1, 3), (2, 4)) from by decide)] at h
  have c43 : Psi (p 0) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 43 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 43 = ((1, 4), (0, 3)) from by decide)] at h
  have c46 : Psi (p 2) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 46 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 46 = ((1, 4), (2, 5)) from by decide)] at h
  have c53 : Psi (p 3) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 53 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 53 = ((1, 5), (3, 4)) from by decide)] at h
  have c55 : Psi (p 0) (p 4) (p 2) (p 3) = 0 := by
    have h := hs 55 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 55 = ((2, 3), (0, 4)) from by decide)] at h
  have c58 : Psi (p 1) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 58 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 58 = ((2, 3), (1, 5)) from by decide)] at h
  have c65 : Psi (p 3) (p 5) (p 2) (p 4) = 0 := by
    have h := hs 65 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 65 = ((2, 4), (3, 5)) from by decide)] at h
  have c67 : Psi (p 0) (p 3) (p 2) (p 5) = 0 := by
    have h := hs 67 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 67 = ((2, 5), (0, 3)) from by decide)] at h
  exact no_general_position_of_fifteen_witnesses p hgp c0 c7 c17 c20 c25 c28 c32 c39 c43 c46 c53 c55 c58 c65 c67

/-- **Class 1.**  No six points in general position carry the mask of
class 1. -/
theorem not_carries_k1 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK1) : False :=
  not_supports_k1 p hgp (supports_of_carries hc)



end QU1

end DistinctCircumradii

#print axioms DistinctCircumradii.QU1.no_six_points_of_seven_witnesses
#print axioms DistinctCircumradii.QU1.no_general_position_of_seven_witnesses
#print axioms DistinctCircumradii.QU1.no_general_position_of_fifteen_witnesses
#print axioms DistinctCircumradii.QU1.cellPsi_eq
#print axioms DistinctCircumradii.QU1.maskK1_mem
#print axioms DistinctCircumradii.QU1.not_supports_k1
#print axioms DistinctCircumradii.QU1.not_carries_k1
