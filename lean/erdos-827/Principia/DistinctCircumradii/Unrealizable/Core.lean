import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現：名前空間 `QU0` の 10 類（k2・k7・k8・k9・k10・k12・k15・k18・k19・k30）

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QU0

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-- The two-term identity behind the first pattern.  Under the single midpoint
equation `p₀ + p₅ = p₁ + p₂` the two witness forms add up to a product of a
signed area and a squared distance. -/
theorem psi_add_psi_of_one_midpoint (p₀ p₁ p₂ p₃ p₅ : Pt)
    (hx : p₀.1 + p₅.1 = p₁.1 + p₂.1) (hy : p₀.2 + p₅.2 = p₁.2 + p₂.2) :
    Psi p₃ p₅ p₀ p₁ + Psi p₀ p₃ p₂ p₅
      = -2 * cross p₀ p₅ p₃ * sqdist p₁ p₅ := by
  have h2x : p₂.1 = p₀.1 + p₅.1 - p₁.1 := by linarith
  have h2y : p₂.2 = p₀.2 + p₅.2 - p₁.2 := by linarith
  simp only [Psi, qq, cross, sqdist, h2x, h2y]
  ring

/-- The first pattern is not carried by six points in general position: the four
points `p₀ p₁ p₂ p₅` form a parallelogram and the two witnesses
`({p₀,p₁},{p₃,p₅})` and `({p₂,p₅},{p₀,p₃})` are present. -/
theorem not_one_midpoint_pattern (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hx : (p 0).1 + (p 5).1 = (p 1).1 + (p 2).1)
    (hy : (p 0).2 + (p 5).2 = (p 1).2 + (p 2).2)
    (hw₁ : Psi (p 3) (p 5) (p 0) (p 1) = 0)
    (hw₂ : Psi (p 0) (p 3) (p 2) (p 5) = 0) : False := by
  obtain ⟨hne, hcol, -⟩ := hgp
  have key := psi_add_psi_of_one_midpoint (p 0) (p 1) (p 2) (p 3) (p 5) hx hy
  rw [hw₁, hw₂] at key
  have hzero : -2 * cross (p 0) (p 5) (p 3) * sqdist (p 1) (p 5) = 0 := by
    linarith [key]
  rcases mul_eq_zero.mp hzero with hA | hB
  · rcases mul_eq_zero.mp hA with hc | hc
    · norm_num at hc
    · refine hcol 0 3 5 (by decide) (by decide) ?_
      simp only [Collinear3, cross] at hc ⊢
      linarith [hc]
  · exact hne 1 5 (by decide) (eq_of_sqdist_eq_zero hB)

/-- The two-term identity behind the second pattern.  Under the two midpoint
equations `p₀ + p₅ = p₃ + p₄` and `p₁ + p₄ = p₂ + p₃` the two witness forms add
up to a product of a signed area and a squared distance. -/
theorem psi_add_psi_of_two_midpoints (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (h0x : p₀.1 = p₃.1 + p₄.1 - p₅.1) (h0y : p₀.2 = p₃.2 + p₄.2 - p₅.2)
    (h1x : p₁.1 = p₂.1 + p₃.1 - p₄.1) (h1y : p₁.2 = p₂.2 + p₃.2 - p₄.2) :
    Psi p₁ p₅ p₀ p₄ + Psi p₀ p₁ p₃ p₅
      = 2 * cross p₀ p₁ p₅ * sqdist p₄ p₅ := by
  simp only [Psi, qq, cross, sqdist, h0x, h0y, h1x, h1y]
  ring

/-- The second pattern is not carried by six points in general position: the two
four-point subsets `p₀ p₅ p₃ p₄` and `p₁ p₄ p₂ p₃` are parallelograms and the
witnesses `({p₀,p₄},{p₁,p₅})` and `({p₃,p₅},{p₀,p₁})` are present. -/
theorem not_two_midpoint_pattern (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (h0x : (p 0).1 = (p 3).1 + (p 4).1 - (p 5).1)
    (h0y : (p 0).2 = (p 3).2 + (p 4).2 - (p 5).2)
    (h1x : (p 1).1 = (p 2).1 + (p 3).1 - (p 4).1)
    (h1y : (p 1).2 = (p 2).2 + (p 3).2 - (p 4).2)
    (hw₁ : Psi (p 1) (p 5) (p 0) (p 4) = 0)
    (hw₂ : Psi (p 0) (p 1) (p 3) (p 5) = 0) : False := by
  obtain ⟨hne, hcol, -⟩ := hgp
  have key := psi_add_psi_of_two_midpoints (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    h0x h0y h1x h1y
  rw [hw₁, hw₂] at key
  have hzero : 2 * cross (p 0) (p 1) (p 5) * sqdist (p 4) (p 5) = 0 := by
    linarith [key]
  rcases mul_eq_zero.mp hzero with hA | hB
  · rcases mul_eq_zero.mp hA with hc | hc
    · norm_num at hc
    · exact hcol 0 1 5 (by decide) (by decide) hc
  · exact hne 4 5 (by decide) (eq_of_sqdist_eq_zero hB)

/-- The identity behind witness pattern ONE: under the midpoint equation
`p₀ + p₁ = p₂ + p₅` the two witness forms combine into a product of a
signed area and a squared distance. -/
theorem psi_identity_pattern_one (p₀ p₁ p₂ p₄ p₅ : Pt)
    (hx : p₀.1 + p₁.1 = p₂.1 + p₅.1) (hy : p₀.2 + p₁.2 = p₂.2 + p₅.2) :
    Psi p₂ p₄ p₀ p₅ + Psi p₄ p₅ p₁ p₂ = 2 * cross p₂ p₄ p₅ * sqdist p₀ p₂ := by
  have hex : p₅.1 = p₀.1 + p₁.1 - p₂.1 := by linarith
  have hey : p₅.2 = p₀.2 + p₁.2 - p₂.2 := by linarith
  simp only [Psi, qq, cross, sqdist, hex, hey]
  ring

/-- Witness pattern ONE is not carried by six points in general position. -/
theorem not_witness_pattern_one (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hx : (p 0).1 + (p 1).1 = (p 2).1 + (p 5).1)
    (hy : (p 0).2 + (p 1).2 = (p 2).2 + (p 5).2)
    (hw₁ : Psi (p 2) (p 4) (p 0) (p 5) = 0) (hw₂ : Psi (p 4) (p 5) (p 1) (p 2) = 0) : False := by
  obtain ⟨hne, hcol, -⟩ := hgp
  have key := psi_identity_pattern_one (p 0) (p 1) (p 2) (p 4) (p 5) hx hy
  rw [hw₁, hw₂] at key
  have hzero : 2 * cross (p 2) (p 4) (p 5) * sqdist (p 0) (p 2) = 0 := by
    linarith
  rcases mul_eq_zero.mp hzero with hA | hB
  · rcases mul_eq_zero.mp hA with hc | hc
    · norm_num at hc
    · exact hcol 2 4 5 (by decide) (by decide) hc
  · exact hne 0 2 (by decide) (eq_of_sqdist_eq_zero hB)

/-- The identity behind witness pattern TWO: under the midpoint equation
`p₀ + p₂ = p₃ + p₄` the two witness forms combine into a product of a
signed area and a squared distance. -/
theorem psi_identity_pattern_two (p₀ p₂ p₃ p₄ p₅ : Pt)
    (hx : p₀.1 + p₂.1 = p₃.1 + p₄.1) (hy : p₀.2 + p₂.2 = p₃.2 + p₄.2) :
    Psi p₃ p₅ p₀ p₄ - Psi p₄ p₅ p₂ p₃ = -2 * cross p₃ p₄ p₅ * sqdist p₀ p₃ := by
  have hex : p₄.1 = p₀.1 + p₂.1 - p₃.1 := by linarith
  have hey : p₄.2 = p₀.2 + p₂.2 - p₃.2 := by linarith
  simp only [Psi, qq, cross, sqdist, hex, hey]
  ring

/-- Witness pattern TWO is not carried by six points in general position. -/
theorem not_witness_pattern_two (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hx : (p 0).1 + (p 2).1 = (p 3).1 + (p 4).1)
    (hy : (p 0).2 + (p 2).2 = (p 3).2 + (p 4).2)
    (hw₁ : Psi (p 3) (p 5) (p 0) (p 4) = 0) (hw₂ : Psi (p 4) (p 5) (p 2) (p 3) = 0) : False := by
  obtain ⟨hne, hcol, -⟩ := hgp
  have key := psi_identity_pattern_two (p 0) (p 2) (p 3) (p 4) (p 5) hx hy
  rw [hw₁, hw₂] at key
  have hzero : 2 * cross (p 3) (p 4) (p 5) * sqdist (p 0) (p 3) = 0 := by
    linarith
  rcases mul_eq_zero.mp hzero with hA | hB
  · rcases mul_eq_zero.mp hA with hc | hc
    · norm_num at hc
    · exact hcol 3 4 5 (by decide) (by decide) hc
  · exact hne 0 3 (by decide) (eq_of_sqdist_eq_zero hB)

/-- The identity behind witness pattern THREE: under the midpoint equation
`p₀ + p₃ = p₂ + p₄` the two witness forms combine into a product of a
signed area and a squared distance. -/
theorem psi_identity_pattern_three (p₀ p₂ p₃ p₄ p₅ : Pt)
    (hx : p₀.1 + p₃.1 = p₂.1 + p₄.1) (hy : p₀.2 + p₃.2 = p₂.2 + p₄.2) :
    Psi p₂ p₅ p₀ p₄ - Psi p₄ p₅ p₂ p₃ = -2 * cross p₂ p₄ p₅ * sqdist p₀ p₂ := by
  have hex : p₄.1 = p₀.1 + p₃.1 - p₂.1 := by linarith
  have hey : p₄.2 = p₀.2 + p₃.2 - p₂.2 := by linarith
  simp only [Psi, qq, cross, sqdist, hex, hey]
  ring

/-- Witness pattern THREE is not carried by six points in general position. -/
theorem not_witness_pattern_three (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hx : (p 0).1 + (p 3).1 = (p 2).1 + (p 4).1)
    (hy : (p 0).2 + (p 3).2 = (p 2).2 + (p 4).2)
    (hw₁ : Psi (p 2) (p 5) (p 0) (p 4) = 0) (hw₂ : Psi (p 4) (p 5) (p 2) (p 3) = 0) : False := by
  obtain ⟨hne, hcol, -⟩ := hgp
  have key := psi_identity_pattern_three (p 0) (p 2) (p 3) (p 4) (p 5) hx hy
  rw [hw₁, hw₂] at key
  have hzero : 2 * cross (p 2) (p 4) (p 5) * sqdist (p 0) (p 2) = 0 := by
    linarith
  rcases mul_eq_zero.mp hzero with hA | hB
  · rcases mul_eq_zero.mp hA with hc | hc
    · norm_num at hc
    · exact hcol 2 4 5 (by decide) (by decide) hc
  · exact hne 0 2 (by decide) (eq_of_sqdist_eq_zero hB)

/-- The identity behind witness pattern FOUR: under the midpoint equation
`p₀ + p₂ = p₁ + p₃` the two witness forms combine into a product of a
signed area and a squared distance. -/
theorem psi_identity_pattern_four (p₀ p₁ p₂ p₃ p₄ : Pt)
    (hx : p₀.1 + p₂.1 = p₁.1 + p₃.1) (hy : p₀.2 + p₂.2 = p₁.2 + p₃.2) :
    Psi p₁ p₄ p₀ p₃ - Psi p₃ p₄ p₁ p₂ = -2 * cross p₁ p₃ p₄ * sqdist p₀ p₁ := by
  have hex : p₂.1 = p₁.1 + p₃.1 - p₀.1 := by linarith
  have hey : p₂.2 = p₁.2 + p₃.2 - p₀.2 := by linarith
  simp only [Psi, qq, cross, sqdist, hex, hey]
  ring

/-- Witness pattern FOUR is not carried by six points in general position. -/
theorem not_witness_pattern_four (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hx : (p 0).1 + (p 2).1 = (p 1).1 + (p 3).1)
    (hy : (p 0).2 + (p 2).2 = (p 1).2 + (p 3).2)
    (hw₁ : Psi (p 1) (p 4) (p 0) (p 3) = 0) (hw₂ : Psi (p 3) (p 4) (p 1) (p 2) = 0) : False := by
  obtain ⟨hne, hcol, -⟩ := hgp
  have key := psi_identity_pattern_four (p 0) (p 1) (p 2) (p 3) (p 4) hx hy
  rw [hw₁, hw₂] at key
  have hzero : 2 * cross (p 1) (p 3) (p 4) * sqdist (p 0) (p 1) = 0 := by
    linarith
  rcases mul_eq_zero.mp hzero with hA | hB
  · rcases mul_eq_zero.mp hA with hc | hc
    · norm_num at hc
    · exact hcol 1 3 4 (by decide) (by decide) hc
  · exact hne 0 1 (by decide) (eq_of_sqdist_eq_zero hB)

/-- The polynomial identity behind class 8.  Under the forced midpoint relations,
the witness forms listed here combine into a product of quantities that are
nonzero for six points in general position. -/
theorem psi_identity_k8 (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (hr1x : p₁.1 = p₀.1 - p₃.1 + p₄.1)
    (hr1y : p₁.2 = p₀.2 - p₃.2 + p₄.2)
    (hr2x : p₂.1 = p₀.1 + p₄.1 - p₅.1)
    (hr2y : p₂.2 = p₀.2 + p₄.2 - p₅.2)
    :
      ((1 / 2) * (p₅.2 - p₀.2) ^ 2 + (1 / 2) * (p₅.1 - p₀.1) ^ 2 - (1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 - (p₃.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₁ p₄ p₀ p₅
    + (-(1 / 2) * (p₄.2 - p₀.2) ^ 2 - (1 / 2) * (p₄.1 - p₀.1) ^ 2 + (1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1))
      * Psi p₂ p₃ p₀ p₅
    + ((1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (1 / 2) * (p₃.2 - p₀.2) ^ 2 + (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) - (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₀ p₂ p₁ p₅
    + ((1 / 2) * (p₅.2 - p₀.2) ^ 2 + (1 / 2) * (p₅.1 - p₀.1) ^ 2 - (1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.2 - p₀.2) ^ 2 - (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₄.1 - p₀.1) ^ 2 - (1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1))
      * Psi p₃ p₄ p₁ p₅
      = cross p₀ p₁ p₂ * cross p₀ p₁ p₃ * cross p₀ p₂ p₄ := by
  simp only [Psi, qq, cross, sqdist, det4, hr1x, hr1y, hr2x, hr2y]
  ring

/-- No six points in general position carry the witness set of class 8.
The hypotheses name the forced midpoint relations and the 4 witnesses used.
-/
theorem not_pattern_k8 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hr1x : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (hr1y : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (hr2x : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (hr2y : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    (hw1 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw2 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw3 : Psi (p 0) (p 2) (p 1) (p 5) = 0)
    (hw4 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    : False := by
  obtain ⟨hne, hcol, hcyc⟩ := hgp
  have key := psi_identity_k8 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    hr1x hr1y hr2x hr2y
  rw [hw1, hw2, hw3, hw4] at key
  have hz : cross (p 0) (p 1) (p 2) * cross (p 0) (p 1) (p 3) * cross (p 0) (p 2) (p 4) = 0 := by
    rw [← key]; ring
  have hf1 : cross (p 0) (p 1) (p 2) ≠ 0 := fun h => hcol 0 1 2 (by decide) (by decide) h
  have hf2 : cross (p 0) (p 1) (p 3) ≠ 0 := fun h => hcol 0 1 3 (by decide) (by decide) h
  have hf3 : cross (p 0) (p 2) (p 4) ≠ 0 := fun h => hcol 0 2 4 (by decide) (by decide) h
  exact (mul_ne_zero (mul_ne_zero hf1 hf2) (hf3)) hz

/-- The polynomial identity behind class 12.  Under the forced midpoint relations,
the witness forms listed here combine into a product of quantities that are
nonzero for six points in general position. -/
theorem psi_identity_k12 (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (hr1x : p₁.1 = p₀.1 - p₃.1 + p₄.1)
    (hr1y : p₁.2 = p₀.2 - p₃.2 + p₄.2)
    (hr2x : p₂.1 = p₀.1 + p₄.1 - p₅.1)
    (hr2y : p₂.2 = p₀.2 + p₄.2 - p₅.2)
    :
      (-(1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.2 - p₀.2) ^ 2 - (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₄.1 - p₀.1) ^ 2 + (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (3 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (p₃.2 - p₀.2) ^ 2 + (p₃.1 - p₀.1) * (p₅.1 - p₀.1) - (3 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) + (p₃.1 - p₀.1) ^ 2)
      * Psi p₂ p₄ p₀ p₁
    + (-(1 / 2) * (p₅.2 - p₀.2) ^ 2 - (1 / 2) * (p₅.1 - p₀.1) ^ 2 + (1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (p₃.1 - p₀.1) * (p₅.1 - p₀.1) - (p₃.1 - p₀.1) * (p₄.1 - p₀.1))
      * Psi p₃ p₅ p₀ p₁
    + (-(1 / 2) * (p₅.2 - p₀.2) ^ 2 - (1 / 2) * (p₅.1 - p₀.1) ^ 2 + (1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 - (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₁ p₄ p₀ p₅
    + (-(1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.2 - p₀.2) ^ 2 - (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₄.1 - p₀.1) ^ 2 + (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 + (p₃.1 - p₀.1) * (p₅.1 - p₀.1) - (p₃.1 - p₀.1) * (p₄.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₂ p₃ p₀ p₅
      = cross p₀ p₁ p₃ * cross p₀ p₂ p₃ * cross p₁ p₂ p₃ := by
  simp only [Psi, qq, cross, sqdist, det4, hr1x, hr1y, hr2x, hr2y]
  ring

/-- No six points in general position carry the witness set of class 12.
The hypotheses name the forced midpoint relations and the 4 witnesses used.
-/
theorem not_pattern_k12 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hr1x : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (hr1y : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (hr2x : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (hr2y : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    (hw1 : Psi (p 2) (p 4) (p 0) (p 1) = 0)
    (hw2 : Psi (p 3) (p 5) (p 0) (p 1) = 0)
    (hw3 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw4 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    : False := by
  obtain ⟨hne, hcol, hcyc⟩ := hgp
  have key := psi_identity_k12 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    hr1x hr1y hr2x hr2y
  rw [hw1, hw2, hw3, hw4] at key
  have hz : cross (p 0) (p 1) (p 3) * cross (p 0) (p 2) (p 3) * cross (p 1) (p 2) (p 3) = 0 := by
    rw [← key]; ring
  have hf1 : cross (p 0) (p 1) (p 3) ≠ 0 := fun h => hcol 0 1 3 (by decide) (by decide) h
  have hf2 : cross (p 0) (p 2) (p 3) ≠ 0 := fun h => hcol 0 2 3 (by decide) (by decide) h
  have hf3 : cross (p 1) (p 2) (p 3) ≠ 0 := fun h => hcol 1 2 3 (by decide) (by decide) h
  exact (mul_ne_zero (mul_ne_zero hf1 hf2) (hf3)) hz

/-- The polynomial identity behind class 18.  Under the forced midpoint relations,
the witness forms listed here combine into a product of quantities that are
nonzero for six points in general position. -/
theorem psi_identity_k18 (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (hr1x : p₁.1 = p₀.1 - p₃.1 + p₄.1)
    (hr1y : p₁.2 = p₀.2 - p₃.2 + p₄.2)
    (hr2x : p₂.1 = p₀.1 + p₄.1 - p₅.1)
    (hr2y : p₂.2 = p₀.2 + p₄.2 - p₅.2)
    :
      (-(1 / 2) * (p₅.2 - p₀.2) ^ 2 - (1 / 2) * (p₅.1 - p₀.1) ^ 2 + (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 - (p₃.1 - p₀.1) * (p₄.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₂ p₄ p₀ p₁
    + (-(p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (p₃.1 - p₀.1) * (p₅.1 - p₀.1) + (p₃.1 - p₀.1) * (p₄.1 - p₀.1))
      * Psi p₁ p₂ p₀ p₃
    + ((3 / 2) * (p₅.2 - p₀.2) ^ 2 + (3 / 2) * (p₅.1 - p₀.1) ^ 2 - (1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 - (p₃.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₁ p₄ p₀ p₅
    + ((1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (p₄.2 - p₀.2) ^ 2 + (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (p₄.1 - p₀.1) ^ 2 - (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + 2 * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (1 / 2) * (p₃.2 - p₀.2) ^ 2 - (p₃.1 - p₀.1) * (p₅.1 - p₀.1) + 2 * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) - (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₂ p₃ p₀ p₅
    + ((1 / 2) * (p₅.2 - p₀.2) ^ 2 + (1 / 2) * (p₅.1 - p₀.1) ^ 2 - (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.2 - p₀.2) ^ 2 - (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₄.1 - p₀.1) ^ 2)
      * Psi p₃ p₄ p₁ p₂
    + (-(1 / 2) * (p₅.2 - p₀.2) ^ 2 - (1 / 2) * (p₅.1 - p₀.1) ^ 2 + (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₄.2 - p₀.2) ^ 2 + (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 2) * (p₄.1 - p₀.1) ^ 2 - (1 / 2) * (p₃.2 - p₀.2) ^ 2 - (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₀ p₂ p₁ p₅
      = cross p₀ p₁ p₂ * sqdist p₀ p₂ * sqdist p₁ p₂ := by
  simp only [Psi, qq, cross, sqdist, det4, hr1x, hr1y, hr2x, hr2y]
  ring

/-- No six points in general position carry the witness set of class 18.
The hypotheses name the forced midpoint relations and the 6 witnesses used.
-/
theorem not_pattern_k18 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hr1x : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (hr1y : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (hr2x : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (hr2y : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    (hw1 : Psi (p 2) (p 4) (p 0) (p 1) = 0)
    (hw2 : Psi (p 1) (p 2) (p 0) (p 3) = 0)
    (hw3 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw4 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw5 : Psi (p 3) (p 4) (p 1) (p 2) = 0)
    (hw6 : Psi (p 0) (p 2) (p 1) (p 5) = 0)
    : False := by
  obtain ⟨hne, hcol, hcyc⟩ := hgp
  have key := psi_identity_k18 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    hr1x hr1y hr2x hr2y
  rw [hw1, hw2, hw3, hw4, hw5, hw6] at key
  have hz : cross (p 0) (p 1) (p 2) * sqdist (p 0) (p 2) * sqdist (p 1) (p 2) = 0 := by
    rw [← key]; ring
  have hf1 : cross (p 0) (p 1) (p 2) ≠ 0 := fun h => hcol 0 1 2 (by decide) (by decide) h
  have hf2 : sqdist (p 0) (p 2) ≠ 0 := fun h => hne 0 2 (by decide) (eq_of_sqdist_eq_zero h)
  have hf3 : sqdist (p 1) (p 2) ≠ 0 := fun h => hne 1 2 (by decide) (eq_of_sqdist_eq_zero h)
  exact (mul_ne_zero (mul_ne_zero hf1 hf2) (hf3)) hz

/-- The polynomial identity behind class 30.  Under the forced midpoint relations,
the witness forms listed here combine into a product of quantities that are
nonzero for six points in general position. -/
theorem psi_identity_k30 (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (hr1x : p₁.1 = p₀.1 - p₃.1 + p₄.1)
    (hr1y : p₁.2 = p₀.2 - p₃.2 + p₄.2)
    (hr2x : p₂.1 = p₀.1 + p₄.1 - p₅.1)
    (hr2y : p₂.2 = p₀.2 + p₄.2 - p₅.2)
    :
      (-(1 / 2) * (p₅.2 - p₀.2) ^ 2 - (1 / 2) * (p₅.1 - p₀.1) ^ 2 + (1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 2) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1))
      * Psi p₃ p₅ p₀ p₁
    + ((1 / 2) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 + (1 / 2) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₃ p₄ p₀ p₂
    + (-(1 / 2) * (p₅.2 - p₀.2) ^ 2 - (1 / 2) * (p₅.1 - p₀.1) ^ 2 + (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₄.2 - p₀.2) ^ 2 + (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 2) * (p₄.1 - p₀.1) ^ 2 - (3 / 2) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (3 / 2) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) + (p₃.1 - p₀.1) * (p₄.1 - p₀.1))
      * Psi p₄ p₅ p₀ p₃
    + (-(1 / 2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₃.2 - p₀.2) ^ 2 + (1 / 2) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₃.1 - p₀.1) ^ 2)
      * Psi p₁ p₂ p₀ p₅
    + ((1 / 2) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1))
      * Psi p₄ p₅ p₁ p₂
    + (-(p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 2) * (p₄.2 - p₀.2) ^ 2 - (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 2) * (p₄.1 - p₀.1) ^ 2 + (1 / 2) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 2) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (1 / 2) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 2) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1))
      * Psi p₃ p₄ p₁ p₅
      = cross p₀ p₁ p₃ * cross p₀ p₂ p₄ * cross p₁ p₂ p₃ := by
  simp only [Psi, qq, cross, sqdist, det4, hr1x, hr1y, hr2x, hr2y]
  ring

/-- No six points in general position carry the witness set of class 30.
The hypotheses name the forced midpoint relations and the 6 witnesses used.
-/
theorem not_pattern_k30 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hr1x : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (hr1y : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (hr2x : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (hr2y : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    (hw1 : Psi (p 3) (p 5) (p 0) (p 1) = 0)
    (hw2 : Psi (p 3) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 4) (p 5) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 5) = 0)
    (hw5 : Psi (p 4) (p 5) (p 1) (p 2) = 0)
    (hw6 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    : False := by
  obtain ⟨hne, hcol, hcyc⟩ := hgp
  have key := psi_identity_k30 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    hr1x hr1y hr2x hr2y
  rw [hw1, hw2, hw3, hw4, hw5, hw6] at key
  have hz : cross (p 0) (p 1) (p 3) * cross (p 0) (p 2) (p 4) * cross (p 1) (p 2) (p 3) = 0 := by
    rw [← key]; ring
  have hf1 : cross (p 0) (p 1) (p 3) ≠ 0 := fun h => hcol 0 1 3 (by decide) (by decide) h
  have hf2 : cross (p 0) (p 2) (p 4) ≠ 0 := fun h => hcol 0 2 4 (by decide) (by decide) h
  have hf3 : cross (p 1) (p 2) (p 3) ≠ 0 := fun h => hcol 1 2 3 (by decide) (by decide) h
  exact (mul_ne_zero (mul_ne_zero hf1 hf2) (hf3)) hz
/-! ## The ten classes -/

/-! ### Class 2 -/

/-- The mask of class 2 (entry 1 of `censusRest`). -/
def maskK2 : Mask := 4907131196476393390608

/-- **Class 2, sharp form.**  No six points in general position support the
mask of class 2 while the 1 listed cell outside the mask
is not a witness.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k2 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK2) (hf1 : cellPsi p 66 ≠ 0) : False := by
  have c4 : Psi (p 3) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 4 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 4 = ((0, 1), (3, 5)) from by decide)] at h
  have c67 : Psi (p 0) (p 3) (p 2) (p 5) = 0 := by
    have h := hs 67 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 67 = ((2, 5), (0, 3)) from by decide)] at h
  have c32 : Psi (p 0) (p 5) (p 1) (p 2) = 0 := by
    have h := hs 32 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 32 = ((1, 2), (0, 5)) from by decide)] at h
  have c24 : Psi (p 1) (p 2) (p 0) (p 5) = 0 := by
    have h := hs 24 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 24 = ((0, 5), (1, 2)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 0) (p 5) (p 1) (p 2)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c32) (c24)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 66 = ((2, 5), (0, 1)) from by decide)]; exact (psi_eq_zero_swap₃₄ (p 0) (p 1) (p 2) (p 5)).1 (hh)))
  exact not_one_midpoint_pattern p hgp
    (by linarith [hm1.1] : (p 0).1 + (p 5).1 = (p 1).1 + (p 2).1)
    (by linarith [hm1.2] : (p 0).2 + (p 5).2 = (p 1).2 + (p 2).2)
    c4 c67

/-- **Class 2.**  No six points in general position carry the mask of class 2. -/
theorem not_carries_k2 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK2) : False :=
  not_supports_free_k2 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 66 (by norm_num)).1 hh) (by decide))

/-! ### Class 7 -/

/-- The mask of class 7 (entry 6 of `censusRest`). -/
def maskK7 : Mask := 19738061199847925489685

/-- **Class 7, sharp form.**  No six points in general position support the
mask of class 7 while the 1 listed cell outside the mask
is not a witness.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k7 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK7) (hf1 : cellPsi p 48 ≠ 0) : False := by
  have c28 : Psi (p 2) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 28 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 28 = ((0, 5), (2, 4)) from by decide)] at h
  have c35 : Psi (p 4) (p 5) (p 1) (p 2) = 0 := by
    have h := hs 35 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 35 = ((1, 2), (4, 5)) from by decide)] at h
  have c66 : Psi (p 0) (p 1) (p 2) (p 5) = 0 := by
    have h := hs 66 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 66 = ((2, 5), (0, 1)) from by decide)] at h
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 0) (p 1) (p 2) (p 5)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c66) (c2)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 48 = ((1, 5), (0, 2)) from by decide)]; exact hh))
  exact not_witness_pattern_one p hgp
    (by linarith [hm1.1] : (p 0).1 + (p 1).1 = (p 2).1 + (p 5).1)
    (by linarith [hm1.2] : (p 0).2 + (p 1).2 = (p 2).2 + (p 5).2)
    c28 c35

/-- **Class 7.**  No six points in general position carry the mask of class 7. -/
theorem not_carries_k7 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK7) : False :=
  not_supports_free_k7 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 48 (by norm_num)).1 hh) (by decide))

/-! ### Class 9 -/

/-- The mask of class 9 (entry 8 of `censusRest`). -/
def maskK9 : Mask := 52112637776347992703680

/-- **Class 9, sharp form.**  No six points in general position support the
mask of class 9 while the 1 listed cell outside the mask
is not a witness.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k9 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK9) (hf1 : cellPsi p 61 ≠ 0) : False := by
  have c23 : Psi (p 3) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 23 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 23 = ((0, 4), (3, 5)) from by decide)] at h
  have c59 : Psi (p 4) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 59 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 59 = ((2, 3), (4, 5)) from by decide)] at h
  have c73 : Psi (p 0) (p 2) (p 3) (p 4) = 0 := by
    have h := hs 73 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 73 = ((3, 4), (0, 2)) from by decide)] at h
  have c9 : Psi (p 3) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 9 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 9 = ((0, 2), (3, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 0) (p 2) (p 3) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c73) (c9)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 61 = ((2, 4), (0, 3)) from by decide)]; exact hh))
  exact not_witness_pattern_two p hgp
    (by linarith [hm1.1] : (p 0).1 + (p 2).1 = (p 3).1 + (p 4).1)
    (by linarith [hm1.2] : (p 0).2 + (p 2).2 = (p 3).2 + (p 4).2)
    c23 c59

/-- **Class 9.**  No six points in general position carry the mask of class 9. -/
theorem not_carries_k9 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK9) : False :=
  not_supports_free_k9 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 61 (by norm_num)).1 hh) (by decide))

/-! ### Class 10 -/

/-- The mask of class 10 (entry 9 of `censusRest`). -/
def maskK10 : Mask := 56763522831400264826960

/-- **Class 10, sharp form.**  No six points in general position support the
mask of class 10 while the 1 listed cell outside the mask
is not a witness.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k10 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK10) (hf1 : cellPsi p 73 ≠ 0) : False := by
  have c22 : Psi (p 2) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 22 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 22 = ((0, 4), (2, 5)) from by decide)] at h
  have c59 : Psi (p 4) (p 5) (p 2) (p 3) = 0 := by
    have h := hs 59 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 59 = ((2, 3), (4, 5)) from by decide)] at h
  have c61 : Psi (p 0) (p 3) (p 2) (p 4) = 0 := by
    have h := hs 61 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 61 = ((2, 4), (0, 3)) from by decide)] at h
  have c15 : Psi (p 2) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 15 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 15 = ((0, 3), (2, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 0) (p 3) (p 2) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c61) (c15)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 73 = ((3, 4), (0, 2)) from by decide)]; exact hh))
  exact not_witness_pattern_three p hgp
    (by linarith [hm1.1] : (p 0).1 + (p 3).1 = (p 2).1 + (p 4).1)
    (by linarith [hm1.2] : (p 0).2 + (p 3).2 = (p 2).2 + (p 4).2)
    c22 c59

/-- **Class 10.**  No six points in general position carry the mask of class 10. -/
theorem not_carries_k10 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK10) : False :=
  not_supports_free_k10 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 73 (by norm_num)).1 hh) (by decide))

/-! ### Class 19 -/

/-- The mask of class 19 (entry 18 of `censusRest`). -/
def maskK19 : Mask := 322303244230729373130848

/-- **Class 19, sharp form.**  No six points in general position support the
mask of class 19 while the 1 listed cell outside the mask
is not a witness.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k19 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK19) (hf1 : cellPsi p 54 ≠ 0) : False := by
  have c13 : Psi (p 1) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 13 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 13 = ((0, 3), (1, 4)) from by decide)] at h
  have c33 : Psi (p 3) (p 4) (p 1) (p 2) = 0 := by
    have h := hs 33 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 33 = ((1, 2), (3, 4)) from by decide)] at h
  have c36 : Psi (p 0) (p 2) (p 1) (p 3) = 0 := by
    have h := hs 36 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 36 = ((1, 3), (0, 2)) from by decide)] at h
  have c6 : Psi (p 1) (p 3) (p 0) (p 2) = 0 := by
    have h := hs 6 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 6 = ((0, 2), (1, 3)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 0) (p 2) (p 1) (p 3)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c36) (c6)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 54 = ((2, 3), (0, 1)) from by decide)]; exact hh))
  exact not_witness_pattern_four p hgp
    (by linarith [hm1.1] : (p 0).1 + (p 2).1 = (p 1).1 + (p 3).1)
    (by linarith [hm1.2] : (p 0).2 + (p 2).2 = (p 1).2 + (p 3).2)
    c13 c33

/-- **Class 19.**  No six points in general position carry the mask of class 19. -/
theorem not_carries_k19 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK19) : False :=
  not_supports_free_k19 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 54 (by norm_num)).1 hh) (by decide))

/-! ### Class 15 -/

/-- The mask of class 15 (entry 14 of `censusRest`). -/
def maskK15 : Mask := 321419383917544530313282

/-- **Class 15, sharp form.**  No six points in general position support the
mask of class 15 while the 2 listed cells outside the mask
are not witnesses.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k15 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK15) (hf1 : cellPsi p 86 ≠ 0) (hf2 : cellPsi p 75 ≠ 0) : False := by
  have c20 : Psi (p 1) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 20 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 20 = ((0, 4), (1, 5)) from by decide)] at h
  have c78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hs 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  have c29 : Psi (p 3) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 29 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 29 = ((0, 5), (3, 4)) from by decide)] at h
  have c45 : Psi (p 2) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 45 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 45 = ((1, 4), (2, 3)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c57 : Psi (p 1) (p 4) (p 2) (p 3) = 0 := by
    have h := hs 57 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 57 = ((2, 3), (1, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 3) (p 4) (p 0) (p 5)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c29) (c74)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 86 = ((4, 5), (0, 3)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 3) (p 4) (p 5)).1 (hh)))
  have hm2 := midpoint_of_two_complementary_witnesses (p 2) (p 3) (p 1) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c45) (c57)
    (fun hh => hf2 (by rw [cellPsi_eq (show cellOf 75 = ((3, 4), (1, 2)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 1) (p 2) (p 3) (p 4)).1 (hh)))
  exact not_two_midpoint_pattern p hgp
    (by linarith [hm1.1] : (p 0).1 = (p 3).1 + (p 4).1 - (p 5).1)
    (by linarith [hm1.2] : (p 0).2 = (p 3).2 + (p 4).2 - (p 5).2)
    (by linarith [hm2.1] : (p 1).1 = (p 2).1 + (p 3).1 - (p 4).1)
    (by linarith [hm2.2] : (p 1).2 = (p 2).2 + (p 3).2 - (p 4).2)
    c20 c78

/-- **Class 15.**  No six points in general position carry the mask of class 15. -/
theorem not_carries_k15 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK15) : False :=
  not_supports_free_k15 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 86 (by norm_num)).1 hh) (by decide))
    (fun hh => absurd ((hc 75 (by norm_num)).1 hh) (by decide))

/-! ### Class 8 -/

/-- The mask of class 8 (entry 7 of `censusRest`). -/
def maskK8 : Mask := 19796266034346135666690

/-- **Class 8, sharp form.**  No six points in general position support the
mask of class 8 while the 2 listed cells outside the mask
are not witnesses.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k8 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK8) (hf1 : cellPsi p 72 ≠ 0) (hf2 : cellPsi p 85 ≠ 0) : False := by
  have c26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c48 : Psi (p 0) (p 2) (p 1) (p 5) = 0 := by
    have h := hs 48 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 48 = ((1, 5), (0, 2)) from by decide)] at h
  have c53 : Psi (p 3) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 53 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 53 = ((1, 5), (3, 4)) from by decide)] at h
  have c19 : Psi (p 1) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 19 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 19 = ((0, 4), (1, 3)) from by decide)] at h
  have c22 : Psi (p 2) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 22 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 22 = ((0, 4), (2, 5)) from by decide)] at h
  have c37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 1) (p 3) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c19) (c37)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 72 = ((3, 4), (0, 1)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 1) (p 3) (p 4)).1 (hh)))
  have hm2 := midpoint_of_two_complementary_witnesses (p 2) (p 5) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c22) (c68)
    (fun hh => hf2 (by rw [cellPsi_eq (show cellOf 85 = ((4, 5), (0, 2)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 2) (p 4) (p 5)).1 ((psi_eq_zero_swap₃₄ (p 2) (p 0) (p 4) (p 5)).1 (hh))))
  exact not_pattern_k8 p hgp
    (by linarith [hm1.1] : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (by linarith [hm1.2] : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (by linarith [hm2.1] : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (by linarith [hm2.2] : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    c26 c27 c48 c53

/-- **Class 8.**  No six points in general position carry the mask of class 8. -/
theorem not_carries_k8 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK8) : False :=
  not_supports_free_k8 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 72 (by norm_num)).1 hh) (by decide))
    (fun hh => absurd ((hc 85 (by norm_num)).1 hh) (by decide))

/-! ### Class 12 -/

/-- The mask of class 12 (entry 11 of `censusRest`). -/
def maskK12 : Mask := 57575197862118925271058

/-- **Class 12, sharp form.**  No six points in general position support the
mask of class 12 while the 2 listed cells outside the mask
are not witnesses.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k12 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK12) (hf1 : cellPsi p 72 ≠ 0) (hf2 : cellPsi p 85 ≠ 0) : False := by
  have c1 : Psi (p 2) (p 4) (p 0) (p 1) = 0 := by
    have h := hs 1 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 1 = ((0, 1), (2, 4)) from by decide)] at h
  have c4 : Psi (p 3) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 4 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 4 = ((0, 1), (3, 5)) from by decide)] at h
  have c26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c19 : Psi (p 1) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 19 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 19 = ((0, 4), (1, 3)) from by decide)] at h
  have c22 : Psi (p 2) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 22 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 22 = ((0, 4), (2, 5)) from by decide)] at h
  have c37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 1) (p 3) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c19) (c37)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 72 = ((3, 4), (0, 1)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 1) (p 3) (p 4)).1 (hh)))
  have hm2 := midpoint_of_two_complementary_witnesses (p 2) (p 5) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c22) (c68)
    (fun hh => hf2 (by rw [cellPsi_eq (show cellOf 85 = ((4, 5), (0, 2)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 2) (p 4) (p 5)).1 ((psi_eq_zero_swap₃₄ (p 2) (p 0) (p 4) (p 5)).1 (hh))))
  exact not_pattern_k12 p hgp
    (by linarith [hm1.1] : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (by linarith [hm1.2] : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (by linarith [hm2.1] : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (by linarith [hm2.2] : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    c1 c4 c26 c27

/-- **Class 12.**  No six points in general position carry the mask of class 12. -/
theorem not_carries_k12 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK12) : False :=
  not_supports_free_k12 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 72 (by norm_num)).1 hh) (by decide))
    (fun hh => absurd ((hc 85 (by norm_num)).1 hh) (by decide))

/-! ### Class 18 -/

/-- The mask of class 18 (entry 17 of `censusRest`). -/
def maskK18 : Mask := 322027694021967371309058

/-- **Class 18, sharp form.**  No six points in general position support the
mask of class 18 while the 2 listed cells outside the mask
are not witnesses.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k18 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK18) (hf1 : cellPsi p 72 ≠ 0) (hf2 : cellPsi p 85 ≠ 0) : False := by
  have c1 : Psi (p 2) (p 4) (p 0) (p 1) = 0 := by
    have h := hs 1 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 1 = ((0, 1), (2, 4)) from by decide)] at h
  have c12 : Psi (p 1) (p 2) (p 0) (p 3) = 0 := by
    have h := hs 12 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 12 = ((0, 3), (1, 2)) from by decide)] at h
  have c26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c33 : Psi (p 3) (p 4) (p 1) (p 2) = 0 := by
    have h := hs 33 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 33 = ((1, 2), (3, 4)) from by decide)] at h
  have c48 : Psi (p 0) (p 2) (p 1) (p 5) = 0 := by
    have h := hs 48 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 48 = ((1, 5), (0, 2)) from by decide)] at h
  have c19 : Psi (p 1) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 19 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 19 = ((0, 4), (1, 3)) from by decide)] at h
  have c22 : Psi (p 2) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 22 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 22 = ((0, 4), (2, 5)) from by decide)] at h
  have c37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 1) (p 3) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c19) (c37)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 72 = ((3, 4), (0, 1)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 1) (p 3) (p 4)).1 (hh)))
  have hm2 := midpoint_of_two_complementary_witnesses (p 2) (p 5) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c22) (c68)
    (fun hh => hf2 (by rw [cellPsi_eq (show cellOf 85 = ((4, 5), (0, 2)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 2) (p 4) (p 5)).1 ((psi_eq_zero_swap₃₄ (p 2) (p 0) (p 4) (p 5)).1 (hh))))
  exact not_pattern_k18 p hgp
    (by linarith [hm1.1] : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (by linarith [hm1.2] : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (by linarith [hm2.1] : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (by linarith [hm2.2] : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    c1 c12 c26 c27 c33 c48

/-- **Class 18.**  No six points in general position carry the mask of class 18. -/
theorem not_carries_k18 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK18) : False :=
  not_supports_free_k18 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 72 (by norm_num)).1 hh) (by decide))
    (fun hh => absurd ((hc 85 (by norm_num)).1 hh) (by decide))

/-! ### Class 30 -/

/-- The mask of class 30 (entry 29 of `censusRest`). -/
def maskK30 : Mask := 19985977319735291164623376

/-- **Class 30, sharp form.**  No six points in general position support the
mask of class 30 while the 2 listed cells outside the mask
are not witnesses.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k30 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK30) (hf1 : cellPsi p 72 ≠ 0) (hf2 : cellPsi p 85 ≠ 0) : False := by
  have c4 : Psi (p 3) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 4 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 4 = ((0, 1), (3, 5)) from by decide)] at h
  have c9 : Psi (p 3) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 9 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 9 = ((0, 2), (3, 4)) from by decide)] at h
  have c17 : Psi (p 4) (p 5) (p 0) (p 3) = 0 := by
    have h := hs 17 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 17 = ((0, 3), (4, 5)) from by decide)] at h
  have c24 : Psi (p 1) (p 2) (p 0) (p 5) = 0 := by
    have h := hs 24 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 24 = ((0, 5), (1, 2)) from by decide)] at h
  have c35 : Psi (p 4) (p 5) (p 1) (p 2) = 0 := by
    have h := hs 35 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 35 = ((1, 2), (4, 5)) from by decide)] at h
  have c53 : Psi (p 3) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 53 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 53 = ((1, 5), (3, 4)) from by decide)] at h
  have c19 : Psi (p 1) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 19 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 19 = ((0, 4), (1, 3)) from by decide)] at h
  have c22 : Psi (p 2) (p 5) (p 0) (p 4) = 0 := by
    have h := hs 22 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 22 = ((0, 4), (2, 5)) from by decide)] at h
  have c37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have hm1 := midpoint_of_two_complementary_witnesses (p 1) (p 3) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c19) (c37)
    (fun hh => hf1 (by rw [cellPsi_eq (show cellOf 72 = ((3, 4), (0, 1)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 1) (p 3) (p 4)).1 (hh)))
  have hm2 := midpoint_of_two_complementary_witnesses (p 2) (p 5) (p 0) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    (c22) (c68)
    (fun hh => hf2 (by rw [cellPsi_eq (show cellOf 85 = ((4, 5), (0, 2)) from by decide)]; exact (psi_eq_zero_swap₁₂ (p 0) (p 2) (p 4) (p 5)).1 ((psi_eq_zero_swap₃₄ (p 2) (p 0) (p 4) (p 5)).1 (hh))))
  exact not_pattern_k30 p hgp
    (by linarith [hm1.1] : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (by linarith [hm1.2] : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (by linarith [hm2.1] : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (by linarith [hm2.2] : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    c4 c9 c17 c24 c35 c53

/-- **Class 30.**  No six points in general position carry the mask of class 30. -/
theorem not_carries_k30 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK30) : False :=
  not_supports_free_k30 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 72 (by norm_num)).1 hh) (by decide))
    (fun hh => absurd ((hc 85 (by norm_num)).1 hh) (by decide))

/-! ## The ten masks are ten of the 34 -/

theorem maskK2_mem : maskK2 ∈ censusRest := by decide

theorem maskK7_mem : maskK7 ∈ censusRest := by decide

theorem maskK9_mem : maskK9 ∈ censusRest := by decide

theorem maskK10_mem : maskK10 ∈ censusRest := by decide

theorem maskK19_mem : maskK19 ∈ censusRest := by decide

theorem maskK15_mem : maskK15 ∈ censusRest := by decide

theorem maskK8_mem : maskK8 ∈ censusRest := by decide

theorem maskK12_mem : maskK12 ∈ censusRest := by decide

theorem maskK18_mem : maskK18 ∈ censusRest := by decide

theorem maskK30_mem : maskK30 ∈ censusRest := by decide

/-! ## The census bridge with the `Carries` form

The class-by-class arguments of this file deliver `¬ Carries`, not `¬ Supports`,
so the hypothesis of the census bridge has to be read in the `Carries` form.
It still closes: `CensusComplete` hands out a mask that the configuration
*carries*, and the `Supports` form was obtained from it only by weakening.
-/

/-- **The `Carries` form of the non-realizability hypothesis.**  Weaker than the
`Supports` form of `Principia.DistinctCircumradii.Census.Statement`, and it is
this form that `not_carries_k*` proves for ten of the 34 masks.  Not proved
here. -/
def RestUnrealizableCarries : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w ∈ censusRest, ¬ Carries p w

/-- The `Supports` form implies the `Carries` form, not the other way round. -/
theorem restUnrealizableCarries_of_supports
    (h : ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w ∈ censusRest, ¬ Supports p w) :
    RestUnrealizableCarries :=
  fun p hgp w hw hc => h p hgp w hw (supports_of_carries hc)

/-- **The bridge, with the `Carries` form of non-realizability.**  The one step
that is not repeated here is the octahedral branch: `hK0` is the type of
`octahedralSix_of_supports_K0` of `Principia.DistinctCircumradii.Census.Statement`
verbatim, so that theorem can be handed to this one. -/
theorem octahedralSix_of_census_carries
    (hK0 : ∀ {q : Fin 6 → Pt}, GeneralPosition q → Supports q censusK0 → OctahedralSix q)
    (hc : CensusComplete) (hr : RestUnrealizableCarries)
    (p : Fin 6 → Pt) (hgp : GeneralPosition p) (hrep : EveryQuadrupleRepeats p) :
    OctahedralSix p := by
  obtain ⟨w, hwlt, hw⟩ := exists_carries p
  obtain ⟨σ, hmem⟩ := hc p hgp hrep w hwlt hw
  have hmem2 : permMask σ w = censusK0 ∨ permMask σ w ∈ censusRest := by
    simpa [censusList] using hmem
  rcases hmem2 with heq | hmem'
  · refine octahedralSix_comp (σ := σ) (hK0 (generalPosition_comp hgp σ) ?_)
    rw [← heq]
    exact supports_of_carries (carries_comp σ hw)
  · exact absurd (carries_comp σ hw) (hr _ (generalPosition_comp hgp σ) _ hmem')

/-- The hypothesis of the conditional seven-point theorem, in the shape in which
`isGood_seven_of_octahedral_six` of `Principia.DistinctCircumradii.SevenPoints`
takes it. -/
theorem octahedral_hypothesis_carries
    (hK0 : ∀ {q : Fin 6 → Pt}, GeneralPosition q → Supports q censusK0 → OctahedralSix q)
    (hc : CensusComplete) (hr : RestUnrealizableCarries) :
    ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → OctahedralSix q :=
  fun q hgp hrep => octahedralSix_of_census_carries hK0 hc hr q hgp hrep

/-- The same in the two-star form. -/
theorem twoStars_hypothesis_carries
    (hK0 : ∀ {q : Fin 6 → Pt}, GeneralPosition q → Supports q censusK0 → OctahedralSix q)
    (hc : CensusComplete) (hr : RestUnrealizableCarries) :
    ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → TwoStars q :=
  fun q hgp hrep => twoStars_of_octahedral (octahedral_hypothesis_carries hK0 hc hr q hgp hrep)






































end QU0

end DistinctCircumradii

#print axioms DistinctCircumradii.QU0.cellPsi_eq
#print axioms DistinctCircumradii.QU0.psi_add_psi_of_one_midpoint
#print axioms DistinctCircumradii.QU0.not_one_midpoint_pattern
#print axioms DistinctCircumradii.QU0.psi_add_psi_of_two_midpoints
#print axioms DistinctCircumradii.QU0.not_two_midpoint_pattern
#print axioms DistinctCircumradii.QU0.psi_identity_pattern_one
#print axioms DistinctCircumradii.QU0.not_witness_pattern_one
#print axioms DistinctCircumradii.QU0.psi_identity_pattern_two
#print axioms DistinctCircumradii.QU0.not_witness_pattern_two
#print axioms DistinctCircumradii.QU0.psi_identity_pattern_three
#print axioms DistinctCircumradii.QU0.not_witness_pattern_three
#print axioms DistinctCircumradii.QU0.psi_identity_pattern_four
#print axioms DistinctCircumradii.QU0.not_witness_pattern_four
#print axioms DistinctCircumradii.QU0.psi_identity_k8
#print axioms DistinctCircumradii.QU0.not_pattern_k8
#print axioms DistinctCircumradii.QU0.psi_identity_k12
#print axioms DistinctCircumradii.QU0.not_pattern_k12
#print axioms DistinctCircumradii.QU0.psi_identity_k18
#print axioms DistinctCircumradii.QU0.not_pattern_k18
#print axioms DistinctCircumradii.QU0.psi_identity_k30
#print axioms DistinctCircumradii.QU0.not_pattern_k30
#print axioms DistinctCircumradii.QU0.not_supports_free_k2
#print axioms DistinctCircumradii.QU0.not_carries_k2
#print axioms DistinctCircumradii.QU0.not_supports_free_k7
#print axioms DistinctCircumradii.QU0.not_carries_k7
#print axioms DistinctCircumradii.QU0.not_supports_free_k9
#print axioms DistinctCircumradii.QU0.not_carries_k9
#print axioms DistinctCircumradii.QU0.not_supports_free_k10
#print axioms DistinctCircumradii.QU0.not_carries_k10
#print axioms DistinctCircumradii.QU0.not_supports_free_k19
#print axioms DistinctCircumradii.QU0.not_carries_k19
#print axioms DistinctCircumradii.QU0.not_supports_free_k15
#print axioms DistinctCircumradii.QU0.not_carries_k15
#print axioms DistinctCircumradii.QU0.not_supports_free_k8
#print axioms DistinctCircumradii.QU0.not_carries_k8
#print axioms DistinctCircumradii.QU0.not_supports_free_k12
#print axioms DistinctCircumradii.QU0.not_carries_k12
#print axioms DistinctCircumradii.QU0.not_supports_free_k18
#print axioms DistinctCircumradii.QU0.not_carries_k18
#print axioms DistinctCircumradii.QU0.not_supports_free_k30
#print axioms DistinctCircumradii.QU0.not_carries_k30
#print axioms DistinctCircumradii.QU0.maskK2_mem
#print axioms DistinctCircumradii.QU0.maskK7_mem
#print axioms DistinctCircumradii.QU0.maskK9_mem
#print axioms DistinctCircumradii.QU0.maskK10_mem
#print axioms DistinctCircumradii.QU0.maskK19_mem
#print axioms DistinctCircumradii.QU0.maskK15_mem
#print axioms DistinctCircumradii.QU0.maskK8_mem
#print axioms DistinctCircumradii.QU0.maskK12_mem
#print axioms DistinctCircumradii.QU0.maskK18_mem
#print axioms DistinctCircumradii.QU0.maskK30_mem
#print axioms DistinctCircumradii.QU0.restUnrealizableCarries_of_supports
#print axioms DistinctCircumradii.QU0.octahedralSix_of_census_carries
#print axioms DistinctCircumradii.QU0.octahedral_hypothesis_carries
#print axioms DistinctCircumradii.QU0.twoStars_hypothesis_carries
