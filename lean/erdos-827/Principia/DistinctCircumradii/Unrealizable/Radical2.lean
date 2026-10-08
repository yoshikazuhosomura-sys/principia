import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（根基の議論）：名前空間 `QR2` の k28

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QR2

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

set_option maxHeartbeats 4000000 in
/-- The polynomial identity behind class 28, with the first point at the
origin.  Under the forced midpoint relations the witness forms listed here
combine into a product of quantities that are nonzero for six points in general
position.  The cofactors are the ones the previous flight computed; the two
extra hypotheses `h0x`, `h0y` are what makes `ring` fit in memory. -/
theorem psi_identity_k28 (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (hr1x : p₁.1 = p₀.1 - p₃.1 + p₄.1)
    (hr1y : p₁.2 = p₀.2 - p₃.2 + p₄.2)
    (hr2x : p₂.1 = p₀.1 + p₄.1 - p₅.1)
    (hr2y : p₂.2 = p₀.2 + p₄.2 - p₅.2)
    (h0x : p₀.1 = 0)
    (h0y : p₀.2 = 0)
    :
      (-(27 / 34) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) ^ 3 - (27 / 34) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) + (65 / 34) * (p₄.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 - (19 / 17) * (p₄.2 - p₀.2) ^ 3 * (p₅.2 - p₀.2) - (27 / 34) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 - (27 / 34) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) ^ 3 + (65 / 17) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (19 / 17) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) + (65 / 34) * (p₄.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 - (19 / 17) * (p₄.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (19 / 17) * (p₄.1 - p₀.1) ^ 3 * (p₅.1 - p₀.1) + (81 / 68) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) ^ 3 + (81 / 68) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) - (295 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) ^ 2 + (33 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 + (163 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) + (73 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 3 - (82 / 17) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (37 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) + (50 / 17) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) + (73 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) + (44 / 17) * (p₃.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 - (11 / 34) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) ^ 2 - (155 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (173 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) ^ 2 + (57 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (31 / 34) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) ^ 2 + (p₃.2 - p₀.2) ^ 3 * (p₅.2 - p₀.2) + (127 / 68) * (p₃.2 - p₀.2) ^ 3 * (p₄.2 - p₀.2) - (27 / 68) * (p₃.2 - p₀.2) ^ 4 + (81 / 68) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 + (81 / 68) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) ^ 3 - (82 / 17) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (50 / 17) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) + (33 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 - (295 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) ^ 2 - (37 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (73 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 + (163 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) + (73 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 3 + (99 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (53 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) - (53 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) - (111 / 34) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) + (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) + (127 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) - (11 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) ^ 2 + (44 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 + (57 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (31 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) ^ 2 - (155 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (173 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) ^ 2 + (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (127 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (27 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) ^ 2 + (p₃.1 - p₀.1) ^ 3 * (p₅.1 - p₀.1) + (127 / 68) * (p₃.1 - p₀.1) ^ 3 * (p₄.1 - p₀.1) - (27 / 68) * (p₃.1 - p₀.1) ^ 4)
      * Psi p₂ p₄ p₀ p₁
    + (-(27 / 34) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) ^ 3 - (27 / 34) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) + (65 / 34) * (p₄.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 - (19 / 17) * (p₄.2 - p₀.2) ^ 3 * (p₅.2 - p₀.2) - (27 / 34) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 - (27 / 34) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) ^ 3 + (65 / 17) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (19 / 17) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) + (65 / 34) * (p₄.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 - (19 / 17) * (p₄.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (19 / 17) * (p₄.1 - p₀.1) ^ 3 * (p₅.1 - p₀.1) - (9 / 34) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) ^ 3 - (9 / 34) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) + (77 / 34) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) ^ 2 + (12 / 17) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 - (33 / 17) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) + (77 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 3 + (53 / 34) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (129 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) - (3 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) + (77 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) - (189 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 + (107 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) ^ 2 + (41 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (19 / 34) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) ^ 2 - (33 / 17) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) ^ 2 + (157 / 68) * (p₃.2 - p₀.2) ^ 3 * (p₅.2 - p₀.2) - (7 / 17) * (p₃.2 - p₀.2) ^ 3 * (p₄.2 - p₀.2) - (6 / 17) * (p₃.2 - p₀.2) ^ 4 - (9 / 34) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 - (9 / 34) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) ^ 3 + (53 / 34) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (3 / 68) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) + (12 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 + (77 / 34) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) ^ 2 - (129 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (77 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 - (33 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) + (77 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 3 - (148 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (173 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) + (173 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) - (39 / 34) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) + (157 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) - (7 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) + (107 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) ^ 2 - (189 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 - (33 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) ^ 2 + (41 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (19 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) ^ 2 + (157 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (7 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (12 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) ^ 2 + (157 / 68) * (p₃.1 - p₀.1) ^ 3 * (p₅.1 - p₀.1) - (7 / 17) * (p₃.1 - p₀.1) ^ 3 * (p₄.1 - p₀.1) - (6 / 17) * (p₃.1 - p₀.1) ^ 4)
      * Psi p₃ p₄ p₀ p₂
    + ((9 / 68) * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) ^ 3 + (9 / 68) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) - (1 / 17) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 - (5 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) - (1 / 17) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 3 + (1 / 17) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (2 / 17) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) - (13 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) - (1 / 17) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) + (67 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 + (3 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) ^ 2 + (5 / 34) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (1 / 17) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) ^ 2 - (3 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (6 / 17) * (p₃.2 - p₀.2) ^ 3 * (p₄.2 - p₀.2) + (9 / 68) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 + (9 / 68) * (p₃.1 - p₀.1) * (p₅.1 - p₀.1) ^ 3 + (1 / 17) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (13 / 68) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) - (1 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 + (2 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) ^ 2 - (5 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) - (1 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 3 + (32 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (13 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) + (13 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) + (2 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) - (6 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) + (3 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) ^ 2 + (67 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 - (3 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (5 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (1 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) ^ 2 - (6 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) - (6 / 17) * (p₃.1 - p₀.1) ^ 3 * (p₄.1 - p₀.1))
      * Psi p₁ p₅ p₀ p₃
    + ((63 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) ^ 2 - (1 / 17) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) + (63 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) - (1 / 17) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) - (45 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 + (19 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) ^ 2 + (7 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (8 / 17) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (8 / 17) * (p₃.2 - p₀.2) ^ 3 * (p₅.2 - p₀.2) + (63 / 68) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (63 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) ^ 2 - (1 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 17) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) - (32 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (39 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) + (39 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) + (8 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) + (19 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) ^ 2 - (45 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 - (8 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) + (7 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) + (8 / 17) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) + (8 / 17) * (p₃.1 - p₀.1) ^ 3 * (p₅.1 - p₀.1))
      * Psi p₁ p₂ p₀ p₅
    + ((19 / 68) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) ^ 2 - (19 / 68) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (27 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.2 - p₀.2) ^ 2 - (19 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) ^ 2 + (3 / 4) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.2 - p₀.2) ^ 2 + (5 / 34) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 68) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) ^ 2 - (67 / 68) * (p₃.2 - p₀.2) ^ 3 * (p₅.2 - p₀.2) - (13 / 68) * (p₃.2 - p₀.2) ^ 3 * (p₄.2 - p₀.2) + (3 / 68) * (p₃.2 - p₀.2) ^ 4 - (19 / 68) * (p₃.1 - p₀.1) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (19 / 68) * (p₃.1 - p₀.1) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) ^ 2 + (23 / 17) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₅.1 - p₀.1) * (p₅.2 - p₀.2) + (41 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) * (p₅.1 - p₀.1) + (41 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) * (p₄.1 - p₀.1) * (p₅.2 - p₀.2) - (67 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₅.1 - p₀.1) - (13 / 68) * (p₃.1 - p₀.1) * (p₃.2 - p₀.2) ^ 2 * (p₄.1 - p₀.1) - (19 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.2 - p₀.2) ^ 2 + (27 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₅.1 - p₀.1) ^ 2 + (5 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) * (p₅.2 - p₀.2) - (1 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.2 - p₀.2) ^ 2 + (3 / 4) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) * (p₅.1 - p₀.1) - (1 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₄.1 - p₀.1) ^ 2 - (67 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₅.2 - p₀.2) - (13 / 68) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) * (p₄.2 - p₀.2) + (3 / 34) * (p₃.1 - p₀.1) ^ 2 * (p₃.2 - p₀.2) ^ 2 - (67 / 68) * (p₃.1 - p₀.1) ^ 3 * (p₅.1 - p₀.1) - (13 / 68) * (p₃.1 - p₀.1) ^ 3 * (p₄.1 - p₀.1) + (3 / 68) * (p₃.1 - p₀.1) ^ 4)
      * Psi p₄ p₅ p₁ p₂
      = cross p₀ p₁ p₂ * cross p₀ p₂ p₄ * cross p₀ p₂ p₄ * sqdist p₀ p₃ := by
  simp only [Psi, qq, cross, sqdist, h0x, h0y, hr1x, hr1y, hr2x, hr2y]
  ring

/-- No six points in general position carry the witness set of class 28.
The hypotheses name the forced midpoint relations and the 5 witnesses used. -/
theorem not_pattern_k28 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hr1x : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (hr1y : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (hr2x : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (hr2y : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    (hw1 : Psi (p 2) (p 4) (p 0) (p 1) = 0)
    (hw2 : Psi (p 3) (p 4) (p 0) (p 2) = 0)
    (hw3 : Psi (p 1) (p 5) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 2) (p 0) (p 5) = 0)
    (hw5 : Psi (p 4) (p 5) (p 1) (p 2) = 0)
    : False := by
  obtain ⟨hne, hcol, hcyc⟩ := hgp
  have key := psi_identity_k28
    ((p 0).1 - (p 0).1, (p 0).2 - (p 0).2)
    ((p 1).1 - (p 0).1, (p 1).2 - (p 0).2)
    ((p 2).1 - (p 0).1, (p 2).2 - (p 0).2)
    ((p 3).1 - (p 0).1, (p 3).2 - (p 0).2)
    ((p 4).1 - (p 0).1, (p 4).2 - (p 0).2)
    ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2)
    (show (p 1).1 - (p 0).1
        = ((p 0).1 - (p 0).1) - ((p 3).1 - (p 0).1) + ((p 4).1 - (p 0).1) by
      linarith [hr1x])
    (show (p 1).2 - (p 0).2
        = ((p 0).2 - (p 0).2) - ((p 3).2 - (p 0).2) + ((p 4).2 - (p 0).2) by
      linarith [hr1y])
    (show (p 2).1 - (p 0).1
        = ((p 0).1 - (p 0).1) + ((p 4).1 - (p 0).1) - ((p 5).1 - (p 0).1) by
      linarith [hr2x])
    (show (p 2).2 - (p 0).2
        = ((p 0).2 - (p 0).2) + ((p 4).2 - (p 0).2) - ((p 5).2 - (p 0).2) by
      linarith [hr2y])
    (show (p 0).1 - (p 0).1 = 0 by ring)
    (show (p 0).2 - (p 0).2 = 0 by ring)
  simp only [psi_shift, cross_shift, sqdist_shift] at key
  rw [hw1, hw2, hw3, hw4, hw5] at key
  have hz : cross (p 0) (p 1) (p 2) * cross (p 0) (p 2) (p 4) * cross (p 0) (p 2) (p 4)
      * sqdist (p 0) (p 3) = 0 := by
    rw [← key]; ring
  have hf1 : cross (p 0) (p 1) (p 2) ≠ 0 := fun h => hcol 0 1 2 (by decide) (by decide) h
  have hf2 : cross (p 0) (p 2) (p 4) ≠ 0 := fun h => hcol 0 2 4 (by decide) (by decide) h
  have hf4 : sqdist (p 0) (p 3) ≠ 0 := fun h => hne 0 3 (by decide) (eq_of_sqdist_eq_zero h)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hf1 hf2) hf2) hf4) hz


/-! ### Class 28 -/

/-- The mask of class 28 (entry 27 of `censusRest`). -/
def maskK28 : Mask := 19967087853834598909231618

/-- **Class 28, sharp form.**  No six points in general position support the
mask of class 28 while the 2 listed cells outside the mask
are not witnesses.  The cells outside the mask are needed only to
rule out the orthocentric branch of the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k28 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK28) (hf1 : cellPsi p 72 ≠ 0) (hf2 : cellPsi p 85 ≠ 0) : False := by
  have c1 : Psi (p 2) (p 4) (p 0) (p 1) = 0 := by
    have h := hs 1 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 1 = ((0, 1), (2, 4)) from by decide)] at h
  have c9 : Psi (p 3) (p 4) (p 0) (p 2) = 0 := by
    have h := hs 9 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 9 = ((0, 2), (3, 4)) from by decide)] at h
  have c14 : Psi (p 1) (p 5) (p 0) (p 3) = 0 := by
    have h := hs 14 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 14 = ((0, 3), (1, 5)) from by decide)] at h
  have c24 : Psi (p 1) (p 2) (p 0) (p 5) = 0 := by
    have h := hs 24 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 24 = ((0, 5), (1, 2)) from by decide)] at h
  have c35 : Psi (p 4) (p 5) (p 1) (p 2) = 0 := by
    have h := hs 35 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 35 = ((1, 2), (4, 5)) from by decide)] at h
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
  exact not_pattern_k28 p hgp
    (by linarith [hm1.1] : (p 1).1 = (p 0).1 - (p 3).1 + (p 4).1)
    (by linarith [hm1.2] : (p 1).2 = (p 0).2 - (p 3).2 + (p 4).2)
    (by linarith [hm2.1] : (p 2).1 = (p 0).1 + (p 4).1 - (p 5).1)
    (by linarith [hm2.2] : (p 2).2 = (p 0).2 + (p 4).2 - (p 5).2)
    c1 c9 c14 c24 c35

/-- **Class 28.**  No six points in general position carry the mask of class 28. -/
theorem not_carries_k28 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK28) : False :=
  not_supports_free_k28 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 72 (by norm_num)).1 hh) (by decide))
    (fun hh => absurd ((hc 85 (by norm_num)).1 hh) (by decide))

theorem maskK28_mem : maskK28 ∈ censusRest := by decide












end QR2

end DistinctCircumradii

#print axioms DistinctCircumradii.QR2.cellPsi_eq
#print axioms DistinctCircumradii.QR2.psi_shift
#print axioms DistinctCircumradii.QR2.cross_shift
#print axioms DistinctCircumradii.QR2.sqdist_shift
#print axioms DistinctCircumradii.QR2.psi_identity_k28
#print axioms DistinctCircumradii.QR2.not_pattern_k28
#print axioms DistinctCircumradii.QR2.not_supports_free_k28
#print axioms DistinctCircumradii.QR2.not_carries_k28
#print axioms DistinctCircumradii.QR2.maskK28_mem
