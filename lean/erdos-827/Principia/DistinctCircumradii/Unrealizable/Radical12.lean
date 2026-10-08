import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（根基の議論）：名前空間 `QR12` の k32

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QR12

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

def maskK32 : Mask := 20023461099188482019461124

/-- **Class 32.**  No six points in general position support the mask of
class 32.  Five of its cells make a closed walk of odd length through five
triangles; the alternating sum of the five one-cell identities leaves
`2 · O_(0, 1, 2) = 2 · p 0`, so the circumcentre of that triangle is one of its own
vertices and its circumradius is `0`. -/
theorem not_supports_k32 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK32) : False := by
  have c42 : Psi (p 0) (p 2) (p 1) (p 4) = 0 := by
    have h := hs 42 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 42 = ((1, 4), (0, 2)) from by decide)] at h
  have c15 : Psi (p 2) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 15 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 15 = ((0, 3), (2, 4)) from by decide)] at h
  have c33 : Psi (p 3) (p 4) (p 1) (p 2) = 0 := by
    have h := hs 33 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 33 = ((1, 2), (3, 4)) from by decide)] at h
  have c19 : Psi (p 1) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 19 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 19 = ((0, 4), (1, 3)) from by decide)] at h
  have c54 : Psi (p 0) (p 1) (p 2) (p 3) = 0 := by
    have h := hs 54 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 54 = ((2, 3), (0, 1)) from by decide)] at h
  obtain ⟨rA, oA, hA0, hA1, hA2⟩ :=
    exists_circumRadiusSq (a := p 0) (b := p 1) (c := p 2)
      (fun hz => ncol_of_gp hgp (show (0 : Fin 6) ≠ 1 by decide)
        (show (0 : Fin 6) ≠ 2 by decide) (show (1 : Fin 6) ≠ 2 by decide) hz)
  obtain ⟨rB, oB, hB0, hB2, hB4⟩ :=
    exists_circumRadiusSq (a := p 0) (b := p 2) (c := p 4)
      (fun hz => ncol_of_gp hgp (show (0 : Fin 6) ≠ 2 by decide)
        (show (0 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide) hz)
  obtain ⟨rC, oC, hC2, hC3, hC4⟩ :=
    exists_circumRadiusSq (a := p 2) (b := p 3) (c := p 4)
      (fun hz => ncol_of_gp hgp (show (2 : Fin 6) ≠ 3 by decide)
        (show (2 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide) hz)
  obtain ⟨rD, oD, hD1, hD3, hD4⟩ :=
    exists_circumRadiusSq (a := p 1) (b := p 3) (c := p 4)
      (fun hz => ncol_of_gp hgp (show (1 : Fin 6) ≠ 3 by decide)
        (show (1 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide) hz)
  obtain ⟨rE, oE, hE0, hE1, hE3⟩ :=
    exists_circumRadiusSq (a := p 0) (b := p 1) (c := p 3)
      (fun hz => ncol_of_gp hgp (show (0 : Fin 6) ≠ 1 by decide)
        (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 3 by decide) hz)
  obtain ⟨g42x, g42y⟩ :=
    centers_sum_of_psi (p := p) (oa := oA) (ob := oB) (ra := rA) (rb := rB) hgp
      (a := 1) (b := 4) (c := 0) (d := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hA0 hA2 hA1 hB0 hB2 hB4 c42
  obtain ⟨g15x, g15y⟩ :=
    centers_sum_of_psi (p := p) (oa := oB) (ob := oC) (ra := rB) (rb := rC) hgp
      (a := 0) (b := 3) (c := 2) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hB2 hB4 hB0 hC2 hC4 hC3 c15
  obtain ⟨g33x, g33y⟩ :=
    centers_sum_of_psi (p := p) (oa := oD) (ob := oC) (ra := rD) (rb := rC) hgp
      (a := 1) (b := 2) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hD3 hD4 hD1 hC3 hC4 hC2 c33
  obtain ⟨g19x, g19y⟩ :=
    centers_sum_of_psi (p := p) (oa := oE) (ob := oD) (ra := rE) (rb := rD) hgp
      (a := 0) (b := 4) (c := 1) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hE1 hE3 hE0 hD1 hD3 hD4 c19
  obtain ⟨g54x, g54y⟩ :=
    centers_sum_of_psi (p := p) (oa := oA) (ob := oE) (ra := rA) (rb := rE) hgp
      (a := 2) (b := 3) (c := 0) (d := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hA0 hA1 hA2 hE0 hE1 hE3 c54
  have hox : oA.1 = (p 0).1 := by linarith
  have hoy : oA.2 = (p 0).2 := by linarith
  have hoc : oA = p 0 := Prod.ext hox hoy
  have hr0 : rA = 0 := by
    rw [← hA0, hoc]; simp only [sqdist]; ring
  have hz : sqdist oA (p 1) = 0 := by rw [hA1, hr0]
  have heq : p 0 = p 1 := by
    have h := eq_of_sqdist_eq_zero hz
    rwa [hoc] at h
  exact ne_of_gp hgp (show (0 : Fin 6) ≠ 1 by decide) heq

/-- **Class 32.**  No six points in general position carry the mask of class 32. -/
theorem not_carries_k32 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK32) : False :=
  not_supports_k32 p hgp (supports_of_carries hc)

theorem maskK32_mem : maskK32 ∈ censusRest := by decide









end QR12

end DistinctCircumradii

#print axioms DistinctCircumradii.QR12.cellPsi_eq
#print axioms DistinctCircumradii.QR12.psi_shift
#print axioms DistinctCircumradii.QR12.cross_shift
#print axioms DistinctCircumradii.QR12.sqdist_shift
#print axioms DistinctCircumradii.QR12.psi_sim
#print axioms DistinctCircumradii.QR12.cross_sim
#print axioms DistinctCircumradii.QR12.sqdist_sim
#print axioms DistinctCircumradii.QR12.not_supports_k32
#print axioms DistinctCircumradii.QR12.not_carries_k32
#print axioms DistinctCircumradii.QR12.maskK32_mem
