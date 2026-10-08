import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（根基の議論）：名前空間 `QR11` の k29

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QR11

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## Translation invariance -/

/-- `Psi` does not see a translation. -/
theorem psi_shift (a b c d t : Pt) :
    Psi (a.1 - t.1, a.2 - t.2) (b.1 - t.1, b.2 - t.2) (c.1 - t.1, c.2 - t.2)
      (d.1 - t.1, d.2 - t.2) = Psi a b c d := by
  simp only [Psi, qq, cross]; ring

/-- `cross` does not see a translation. -/
theorem cross_shift (a b c t : Pt) :
    cross (a.1 - t.1, a.2 - t.2) (b.1 - t.1, b.2 - t.2) (c.1 - t.1, c.2 - t.2)
      = cross a b c := by
  simp only [cross]; ring

/-- `sqdist` does not see a translation. -/
theorem sqdist_shift (a b t : Pt) :
    sqdist (a.1 - t.1, a.2 - t.2) (b.1 - t.1, b.2 - t.2) = sqdist a b := by
  simp only [sqdist]; ring

/-! ## The similarity that puts `p₀` at the origin and `p₅` on the x-axis -/

/-- First coordinate of `conj z * (a - t)`. -/
def simx (t z a : Pt) : ℝ := z.1 * (a.1 - t.1) + z.2 * (a.2 - t.2)

/-- Second coordinate of `conj z * (a - t)`. -/
def simy (t z a : Pt) : ℝ := z.1 * (a.2 - t.2) - z.2 * (a.1 - t.1)

/-- `Psi` is multiplied by `|z|⁴` under `a ↦ conj z * (a - t)`: the map is
complex multiplication by a constant, hence a rotation composed with a
dilation, and `Psi` is a product of one inner product and one determinant. -/
theorem psi_sim (t z a b c d : Pt) :
    Psi (simx t z a, simy t z a) (simx t z b, simy t z b) (simx t z c, simy t z c)
        (simx t z d, simy t z d)
      = (z.1 ^ 2 + z.2 ^ 2) ^ 2 * Psi a b c d := by
  simp only [Psi, qq, cross, simx, simy]
  ring

/-- `cross` is multiplied by `|z|²`. -/
theorem cross_sim (t z a b c : Pt) :
    cross (simx t z a, simy t z a) (simx t z b, simy t z b) (simx t z c, simy t z c)
      = (z.1 ^ 2 + z.2 ^ 2) * cross a b c := by
  simp only [cross, simx, simy]
  ring

/-- `sqdist` is multiplied by `|z|²`. -/
theorem sqdist_sim (t z a b : Pt) :
    sqdist (simx t z a, simy t z a) (simx t z b, simy t z b)
      = (z.1 ^ 2 + z.2 ^ 2) * sqdist a b := by
  simp only [sqdist, simx, simy]
  ring

/-! ## The circumradius, copied from the census files -/

def maskK29 : Mask := 19967383271954623119001604

/-- **Class 29.**  No six points in general position support the mask of
class 29.  Five of its cells make a closed walk of odd length through five
triangles; the alternating sum of the five one-cell identities leaves
`2 · O_(0, 2, 3) = 2 · p 0`, so the circumcentre of that triangle is one of its own
vertices and its circumradius is `0`. -/
theorem not_supports_k29 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK29) : False := by
  have c79 : Psi (p 0) (p 2) (p 3) (p 5) = 0 := by
    have h := hs 79 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 79 = ((3, 5), (0, 2)) from by decide)] at h
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have c58 : Psi (p 1) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 58 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 58 = ((2, 3), (1, 5)) from by decide)] at h
  have c25 : Psi (p 1) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 25 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 25 = ((0, 5), (1, 3)) from by decide)] at h
  have c30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hs 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  obtain ⟨rA, oA, hA0, hA2, hA3⟩ :=
    exists_circumRadiusSq (a := p 0) (b := p 2) (c := p 3)
      (fun hz => ncol_of_gp hgp (show (0 : Fin 6) ≠ 2 by decide)
        (show (0 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide) hz)
  obtain ⟨rB, oB, hB0, hB2, hB5⟩ :=
    exists_circumRadiusSq (a := p 0) (b := p 2) (c := p 5)
      (fun hz => ncol_of_gp hgp (show (0 : Fin 6) ≠ 2 by decide)
        (show (0 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide) hz)
  obtain ⟨rC, oC, hC1, hC2, hC5⟩ :=
    exists_circumRadiusSq (a := p 1) (b := p 2) (c := p 5)
      (fun hz => ncol_of_gp hgp (show (1 : Fin 6) ≠ 2 by decide)
        (show (1 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide) hz)
  obtain ⟨rD, oD, hD1, hD3, hD5⟩ :=
    exists_circumRadiusSq (a := p 1) (b := p 3) (c := p 5)
      (fun hz => ncol_of_gp hgp (show (1 : Fin 6) ≠ 3 by decide)
        (show (1 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide) hz)
  obtain ⟨rE, oE, hE0, hE1, hE3⟩ :=
    exists_circumRadiusSq (a := p 0) (b := p 1) (c := p 3)
      (fun hz => ncol_of_gp hgp (show (0 : Fin 6) ≠ 1 by decide)
        (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 3 by decide) hz)
  obtain ⟨g79x, g79y⟩ :=
    centers_sum_of_psi (p := p) (oa := oA) (ob := oB) (ra := rA) (rb := rB) hgp
      (a := 3) (b := 5) (c := 0) (d := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hA0 hA2 hA3 hB0 hB2 hB5 c79
  obtain ⟨g2x, g2y⟩ :=
    centers_sum_of_psi (p := p) (oa := oB) (ob := oC) (ra := rB) (rb := rC) hgp
      (a := 0) (b := 1) (c := 2) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hB2 hB5 hB0 hC2 hC5 hC1 c2
  obtain ⟨g58x, g58y⟩ :=
    centers_sum_of_psi (p := p) (oa := oC) (ob := oD) (ra := rC) (rb := rD) hgp
      (a := 2) (b := 3) (c := 1) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hC1 hC5 hC2 hD1 hD5 hD3 c58
  obtain ⟨g25x, g25y⟩ :=
    centers_sum_of_psi (p := p) (oa := oE) (ob := oD) (ra := rE) (rb := rD) hgp
      (a := 0) (b := 5) (c := 1) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hE1 hE3 hE0 hD1 hD3 hD5 c25
  obtain ⟨g30x, g30y⟩ :=
    centers_sum_of_psi (p := p) (oa := oE) (ob := oA) (ra := rE) (rb := rA) hgp
      (a := 1) (b := 2) (c := 0) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hE0 hE3 hE1 hA0 hA3 hA2 c30
  have hox : oA.1 = (p 0).1 := by linarith
  have hoy : oA.2 = (p 0).2 := by linarith
  have hoc : oA = p 0 := Prod.ext hox hoy
  have hr0 : rA = 0 := by
    rw [← hA0, hoc]; simp only [sqdist]; ring
  have hz : sqdist oA (p 2) = 0 := by rw [hA2, hr0]
  have heq : p 0 = p 2 := by
    have h := eq_of_sqdist_eq_zero hz
    rwa [hoc] at h
  exact ne_of_gp hgp (show (0 : Fin 6) ≠ 2 by decide) heq

/-- **Class 29.**  No six points in general position carry the mask of class 29. -/
theorem not_carries_k29 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK29) : False :=
  not_supports_k29 p hgp (supports_of_carries hc)

theorem maskK29_mem : maskK29 ∈ censusRest := by decide









end QR11

end DistinctCircumradii

#print axioms DistinctCircumradii.QR11.cellPsi_eq
#print axioms DistinctCircumradii.QR11.psi_shift
#print axioms DistinctCircumradii.QR11.cross_shift
#print axioms DistinctCircumradii.QR11.sqdist_shift
#print axioms DistinctCircumradii.QR11.psi_sim
#print axioms DistinctCircumradii.QR11.cross_sim
#print axioms DistinctCircumradii.QR11.sqdist_sim
#print axioms DistinctCircumradii.QR11.not_supports_k29
#print axioms DistinctCircumradii.QR11.not_carries_k29
#print axioms DistinctCircumradii.QR11.maskK29_mem
