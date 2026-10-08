import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（根基の議論）：名前空間 `QR3` の k14

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QR3

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

/-! ### Class 14 -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The polynomial identity behind class 14, in the chart where `p₀` is the
origin and `p₅` lies on the x-axis.  Under the forced midpoint relation the
witness forms listed here combine into a product of quantities that are
nonzero for six points in general position.  The chart has seven variables
instead of eight, so the normal form `ring` builds lives in the 3003
monomials of degree 8 in seven variables. -/
theorem psi_identity_k14 (p₀ p₁ p₂ p₃ p₄ p₅ : Pt)
    (hr1x : p₁.1 = p₂.1 + p₃.1 - p₄.1)
    (hr1y : p₁.2 = p₂.2 + p₃.2 - p₄.2)
    (h0x : p₀.1 = 0)
    (h0y : p₀.2 = 0)
    (h5y : p₅.2 = 0)
    :
      (-(2971 / 7980) * p₄.2 ^ 3 * p₅.1 + (2035 / 266) * p₄.1 * p₄.2 * p₅.1 ^ 2 - (9017 / 2660) * p₄.1 ^ 2 * p₄.2 * p₅.1 + (61141 / 15960) * p₃.2 * p₄.2 ^ 2 * p₅.1 - (5879 / 1064) * p₃.2 * p₄.1 * p₅.1 ^ 2 - (3747 / 760) * p₃.2 * p₄.1 * p₄.2 ^ 2 + (6747 / 1064) * p₃.2 * p₄.1 ^ 2 * p₅.1 - (3747 / 760) * p₃.2 * p₄.1 ^ 3 - (55199 / 15960) * p₃.2 ^ 2 * p₄.2 * p₅.1 + (3747 / 380) * p₃.2 ^ 2 * p₄.1 * p₄.2 - (3747 / 760) * p₃.2 ^ 3 * p₄.1 + (597 / 760) * p₃.1 * p₄.2 * p₅.1 ^ 2 + (3747 / 760) * p₃.1 * p₄.2 ^ 3 - (4588 / 1995) * p₃.1 * p₄.1 * p₄.2 * p₅.1 + (3747 / 760) * p₃.1 * p₄.1 ^ 2 * p₄.2 - (3747 / 380) * p₃.1 * p₃.2 * p₄.2 ^ 2 - (56473 / 7980) * p₃.1 * p₃.2 * p₄.1 * p₅.1 + (3747 / 380) * p₃.1 * p₃.2 * p₄.1 ^ 2 + (3747 / 760) * p₃.1 * p₃.2 ^ 2 * p₄.2 + (19249 / 5320) * p₃.1 ^ 2 * p₄.2 * p₅.1 - (3747 / 380) * p₃.1 ^ 2 * p₄.1 * p₄.2 - (3747 / 760) * p₃.1 ^ 2 * p₃.2 * p₄.1 + (3747 / 760) * p₃.1 ^ 3 * p₄.2 + (472 / 1995) * p₂.2 * p₄.2 ^ 2 * p₅.1 + (40861 / 7980) * p₂.2 * p₄.1 * p₅.1 ^ 2 - (16181 / 3990) * p₂.2 * p₄.1 ^ 2 * p₅.1 + (7649 / 2660) * p₂.2 * p₃.2 * p₄.2 * p₅.1 + (439 / 798) * p₂.2 * p₃.2 * p₄.1 * p₄.2 - (171037 / 15960) * p₂.2 * p₃.2 ^ 2 * p₄.1 + (3541 / 7980) * p₂.2 * p₃.1 * p₅.1 ^ 2 - (171037 / 15960) * p₂.2 * p₃.1 * p₄.2 ^ 2 - (54001 / 7980) * p₂.2 * p₃.1 * p₄.1 * p₅.1 - (162257 / 15960) * p₂.2 * p₃.1 * p₄.1 ^ 2 + (55549 / 2660) * p₂.2 * p₃.1 * p₃.2 * p₄.2 + (162257 / 15960) * p₂.2 * p₃.1 ^ 2 * p₄.1 - (236 / 1995) * p₂.2 ^ 2 * p₄.2 * p₅.1 + (162257 / 15960) * p₂.2 ^ 2 * p₃.2 * p₄.1 - (162257 / 15960) * p₂.2 ^ 2 * p₃.1 * p₄.2 - (25623 / 2660) * p₂.1 * p₄.2 * p₅.1 ^ 2 + (2747 / 266) * p₂.1 * p₄.1 * p₄.2 * p₅.1 + (239 / 228) * p₂.1 * p₃.2 * p₅.1 ^ 2 + (162257 / 15960) * p₂.1 * p₃.2 * p₄.2 ^ 2 + (2369 / 266) * p₂.1 * p₃.2 * p₄.1 * p₅.1 + (171037 / 15960) * p₂.1 * p₃.2 * p₄.1 ^ 2 - (162257 / 15960) * p₂.1 * p₃.2 ^ 2 * p₄.2 - (640 / 399) * p₂.1 * p₃.1 * p₄.2 * p₅.1 - (439 / 798) * p₂.1 * p₃.1 * p₄.1 * p₄.2 - (55549 / 2660) * p₂.1 * p₃.1 * p₃.2 * p₄.1 + (171037 / 15960) * p₂.1 * p₃.1 ^ 2 * p₄.2 - (4603 / 1596) * p₂.1 * p₂.2 * p₅.1 ^ 2 - (1241 / 3990) * p₂.1 * p₂.2 * p₄.1 * p₅.1 + (841 / 133) * p₂.1 * p₂.2 * p₃.1 * p₅.1 - (659 / 133) * p₂.1 ^ 2 * p₄.2 * p₅.1 - (5577 / 1330) * p₂.1 ^ 2 * p₃.2 * p₅.1 + (162257 / 15960) * p₂.1 ^ 2 * p₃.2 * p₄.1 - (162257 / 15960) * p₂.1 ^ 2 * p₃.1 * p₄.2 + (2833 / 1330) * p₂.1 ^ 2 * p₂.2 * p₅.1)
      * Psi p₂ p₃ p₀ p₅
    + ((2853 / 2660) * p₂.2 * p₅.1 ^ 3 - (2027 / 15960) * p₂.2 * p₄.2 ^ 2 * p₅.1 - (45119 / 7980) * p₂.2 * p₄.1 * p₅.1 ^ 2 + (1828 / 399) * p₂.2 * p₄.1 ^ 2 * p₅.1 - (13967 / 5320) * p₂.2 * p₃.2 * p₄.2 * p₅.1 - (1123 / 1995) * p₂.2 * p₃.1 * p₅.1 ^ 2 - (1009 / 456) * p₂.2 * p₃.1 * p₄.1 * p₅.1 + (24417 / 5320) * p₂.2 * p₃.1 ^ 2 * p₅.1 + (33367 / 15960) * p₂.2 ^ 2 * p₄.2 * p₅.1 - (2027 / 7980) * p₂.2 ^ 2 * p₄.1 * p₄.2 + (1107 / 760) * p₂.2 ^ 2 * p₃.2 * p₅.1 + (2027 / 7980) * p₂.2 ^ 2 * p₃.2 * p₄.1 - (5074 / 1995) * p₂.2 ^ 2 * p₃.1 * p₄.2 - (401 / 168) * p₂.2 ^ 2 * p₃.1 * p₃.2 + (38317 / 7980) * p₂.1 * p₄.2 * p₅.1 ^ 2 - (86347 / 15960) * p₂.1 * p₄.1 * p₄.2 * p₅.1 + (4159 / 3990) * p₂.1 * p₃.2 * p₅.1 ^ 2 - (4159 / 3990) * p₂.1 * p₃.2 * p₄.1 * p₅.1 - (115 / 1596) * p₂.1 * p₃.1 * p₄.2 * p₅.1 - (62051 / 15960) * p₂.1 * p₃.1 * p₃.2 * p₅.1 - (3163 / 3990) * p₂.1 * p₂.2 * p₅.1 ^ 2 + (4213 / 1995) * p₂.1 * p₂.2 * p₄.1 * p₅.1 - (2027 / 7980) * p₂.1 * p₂.2 * p₄.1 ^ 2 + (1649 / 3990) * p₂.1 * p₂.2 * p₃.2 * p₄.2 + (55093 / 15960) * p₂.1 * p₂.2 * p₃.2 ^ 2 + (9561 / 5320) * p₂.1 * p₂.2 * p₃.1 * p₅.1 - (956 / 285) * p₂.1 * p₂.2 * p₃.1 * p₄.1 - (401 / 168) * p₂.1 * p₂.2 * p₃.1 ^ 2 + (2833 / 2660) * p₂.1 * p₂.2 ^ 2 * p₃.2 + (3621 / 5320) * p₂.1 ^ 2 * p₄.2 * p₅.1 - (4159 / 3990) * p₂.1 ^ 2 * p₃.2 * p₅.1 + (11797 / 7980) * p₂.1 ^ 2 * p₃.2 * p₄.1 + (55093 / 15960) * p₂.1 ^ 2 * p₃.1 * p₃.2 + (2833 / 2660) * p₂.1 ^ 2 * p₂.2 * p₃.1)
      * Psi p₀ p₄ p₁ p₃
    + (-(2027 / 7980) * p₂.2 * p₄.1 * p₄.2 ^ 2 + (2027 / 7980) * p₂.2 * p₄.1 ^ 2 * p₅.1 - (2027 / 7980) * p₂.2 * p₄.1 ^ 3 + (811 / 665) * p₂.2 * p₃.2 * p₄.2 * p₅.1 + (2027 / 3990) * p₂.2 * p₃.2 * p₄.1 * p₄.2 + (73097 / 15960) * p₂.2 * p₃.2 ^ 2 * p₄.1 + (5493 / 1330) * p₂.2 * p₃.1 * p₅.1 ^ 2 + (36559 / 15960) * p₂.2 * p₃.1 * p₄.2 ^ 2 + (403 / 1330) * p₂.2 * p₃.1 * p₄.1 * p₅.1 + (2127 / 760) * p₂.2 * p₃.1 * p₄.1 ^ 2 - (36559 / 7980) * p₂.2 * p₃.1 * p₃.2 * p₄.2 - (5074 / 1995) * p₂.2 * p₃.1 * p₃.2 ^ 2 - (37403 / 7980) * p₂.2 * p₃.1 ^ 2 * p₅.1 - (1 / 760) * p₂.2 * p₃.1 ^ 2 * p₄.1 - (5074 / 1995) * p₂.2 * p₃.1 ^ 3 - (2027 / 7980) * p₂.2 ^ 2 * p₄.2 * p₅.1 + (2027 / 3990) * p₂.2 ^ 2 * p₄.1 * p₄.2 - (34921 / 7980) * p₂.2 ^ 2 * p₃.2 * p₅.1 - (85259 / 15960) * p₂.2 ^ 2 * p₃.2 * p₄.1 + (31667 / 3192) * p₂.2 ^ 2 * p₃.1 * p₄.2 + (321 / 76) * p₂.2 ^ 2 * p₃.1 * p₃.2 - (2027 / 7980) * p₂.1 * p₄.1 * p₄.2 * p₅.1 - (5493 / 1330) * p₂.1 * p₃.2 * p₅.1 ^ 2 - (14111 / 3192) * p₂.1 * p₃.2 * p₄.2 ^ 2 + (24533 / 7980) * p₂.1 * p₃.2 * p₄.1 * p₅.1 - (14111 / 3192) * p₂.1 * p₃.2 * p₄.1 ^ 2 + (46961 / 15960) * p₂.1 * p₃.2 ^ 2 * p₄.2 + (11797 / 7980) * p₂.1 * p₃.2 ^ 3 - (6019 / 7980) * p₂.1 * p₃.1 * p₄.2 * p₅.1 + (37403 / 7980) * p₂.1 * p₃.1 * p₃.2 * p₅.1 + (14111 / 1596) * p₂.1 * p₃.1 * p₃.2 * p₄.1 - (31383 / 5320) * p₂.1 * p₃.1 ^ 2 * p₄.2 + (11797 / 7980) * p₂.1 * p₃.1 ^ 2 * p₃.2 - (2027 / 3990) * p₂.1 * p₂.2 * p₄.1 * p₅.1 + (2027 / 3990) * p₂.1 * p₂.2 * p₄.1 ^ 2 + (1903 / 7980) * p₂.1 * p₂.2 * p₃.2 * p₄.2 - (9867 / 1330) * p₂.1 * p₂.2 * p₃.2 ^ 2 - (9697 / 1140) * p₂.1 * p₂.2 * p₃.1 * p₅.1 + (653 / 84) * p₂.1 * p₂.2 * p₃.1 * p₄.1 + (4201 / 1330) * p₂.1 * p₂.2 * p₃.1 ^ 2 - (2833 / 1330) * p₂.1 * p₂.2 ^ 2 * p₃.2 + (2027 / 7980) * p₂.1 ^ 2 * p₄.2 * p₅.1 + (5493 / 1330) * p₂.1 ^ 2 * p₃.2 * p₅.1 - (20191 / 2280) * p₂.1 ^ 2 * p₃.2 * p₄.1 + (31383 / 5320) * p₂.1 ^ 2 * p₃.1 * p₄.2 - (16901 / 2660) * p₂.1 ^ 2 * p₃.1 * p₃.2 - (2833 / 1330) * p₂.1 ^ 2 * p₂.2 * p₃.1)
      * Psi p₂ p₅ p₁ p₄
    + (-(2027 / 3990) * p₄.1 ^ 2 * p₄.2 * p₅.1 - (4771 / 5320) * p₃.2 * p₄.2 ^ 2 * p₅.1 + (7423 / 5320) * p₃.2 * p₄.1 * p₅.1 ^ 2 - (11377 / 1995) * p₃.2 * p₄.1 ^ 2 * p₅.1 + (35881 / 3990) * p₃.2 * p₄.1 ^ 3 + (55199 / 15960) * p₃.2 ^ 2 * p₄.2 * p₅.1 - (129889 / 15960) * p₃.2 ^ 2 * p₄.1 * p₄.2 + (62051 / 15960) * p₃.2 ^ 3 * p₄.1 - (597 / 760) * p₃.1 * p₄.2 * p₅.1 ^ 2 - (73457 / 15960) * p₃.1 * p₄.2 ^ 3 + (2887 / 2280) * p₃.1 * p₄.1 * p₄.2 * p₅.1 - (72327 / 5320) * p₃.1 * p₄.1 ^ 2 * p₄.2 + (14579 / 1140) * p₃.1 * p₃.2 * p₄.2 ^ 2 + (6809 / 1995) * p₃.1 * p₃.2 * p₄.1 * p₅.1 - (6229 / 665) * p₃.1 * p₃.2 * p₄.1 ^ 2 - (1817 / 760) * p₃.1 * p₃.2 ^ 2 * p₄.2 - (8291 / 15960) * p₃.1 ^ 2 * p₄.2 * p₅.1 + (10653 / 760) * p₃.1 ^ 2 * p₄.1 * p₄.2 + (84451 / 15960) * p₃.1 ^ 2 * p₃.2 * p₄.1 - (8651 / 2280) * p₃.1 ^ 3 * p₄.2 - (2027 / 7980) * p₂.2 * p₄.1 * p₅.1 ^ 2 + (2027 / 7980) * p₂.2 * p₄.1 * p₄.2 ^ 2 + (2027 / 3990) * p₂.2 * p₄.1 ^ 2 * p₅.1 - (2027 / 7980) * p₂.2 * p₄.1 ^ 3 - (8317 / 1330) * p₂.2 * p₃.2 * p₄.2 * p₅.1 + (67789 / 7980) * p₂.2 * p₃.2 * p₄.1 * p₄.2 + (5083 / 3990) * p₂.2 * p₃.2 ^ 2 * p₄.1 - (3541 / 7980) * p₂.2 * p₃.1 * p₅.1 ^ 2 - (1123 / 210) * p₂.2 * p₃.1 * p₄.2 ^ 2 - (2977 / 1330) * p₂.2 * p₃.1 * p₄.1 * p₅.1 + (29923 / 7980) * p₂.2 * p₃.1 * p₄.1 ^ 2 - (1643 / 7980) * p₂.2 * p₃.1 * p₃.2 * p₄.2 + (2547 / 1064) * p₂.2 * p₃.1 * p₃.2 ^ 2 - (31123 / 15960) * p₂.2 * p₃.1 ^ 2 * p₅.1 + (14173 / 2660) * p₂.2 * p₃.1 ^ 2 * p₄.1 + (2547 / 1064) * p₂.2 * p₃.1 ^ 3 + (2027 / 7980) * p₂.2 ^ 2 * p₄.2 * p₅.1 - (2027 / 7980) * p₂.2 ^ 2 * p₄.1 * p₄.2 + (3541 / 7980) * p₂.2 ^ 2 * p₃.2 * p₅.1 - (9173 / 2660) * p₂.2 ^ 2 * p₃.2 * p₄.1 - (9418 / 1995) * p₂.2 ^ 2 * p₃.1 * p₄.2 + (31123 / 15960) * p₂.2 ^ 2 * p₃.1 * p₃.2 + (2027 / 3990) * p₂.1 * p₄.1 * p₄.2 * p₅.1 + (2027 / 3990) * p₂.1 * p₄.1 ^ 2 * p₄.2 + (24593 / 7980) * p₂.1 * p₃.2 * p₅.1 ^ 2 + (7027 / 1330) * p₂.1 * p₃.2 * p₄.2 ^ 2 - (5173 / 1140) * p₂.1 * p₃.2 * p₄.1 * p₅.1 + (29909 / 7980) * p₂.1 * p₃.2 * p₄.1 ^ 2 - (5053 / 1995) * p₂.1 * p₃.2 ^ 2 * p₄.2 - (11797 / 7980) * p₂.1 * p₃.2 ^ 3 + (6663 / 2660) * p₂.1 * p₃.1 * p₄.2 * p₅.1 + (1489 / 1596) * p₂.1 * p₃.1 * p₄.1 * p₄.2 - (5267 / 2280) * p₂.1 * p₃.1 * p₃.2 * p₅.1 - (32353 / 7980) * p₂.1 * p₃.1 * p₃.2 * p₄.1 - (1457 / 532) * p₂.1 * p₃.1 ^ 2 * p₄.2 - (11797 / 7980) * p₂.1 * p₃.1 ^ 2 * p₃.2 + (9623 / 1596) * p₂.1 * p₂.2 * p₃.2 * p₄.2 + (53 / 285) * p₂.1 * p₂.2 * p₃.2 ^ 2 + (9197 / 3990) * p₂.1 * p₂.2 * p₃.1 * p₅.1 - (17693 / 2660) * p₂.1 * p₂.2 * p₃.1 * p₄.1 - (463 / 2660) * p₂.1 * p₂.2 * p₃.1 ^ 2 + (487 / 399) * p₂.1 * p₂.2 ^ 2 * p₃.2 - (2027 / 7980) * p₂.1 ^ 2 * p₄.2 * p₅.1 - (2027 / 7980) * p₂.1 ^ 2 * p₄.1 * p₄.2 - (857 / 140) * p₂.1 ^ 2 * p₃.2 * p₅.1 + (718 / 399) * p₂.1 ^ 2 * p₃.2 * p₄.1 + (21643 / 7980) * p₂.1 ^ 2 * p₃.1 * p₄.2 + (5267 / 2280) * p₂.1 ^ 2 * p₃.1 * p₃.2 - (191 / 105) * p₂.1 ^ 2 * p₂.2 * p₃.1 + (6064 / 1995) * p₂.1 ^ 3 * p₃.2)
      * Psi p₀ p₂ p₁ p₅
    + ((1619 / 1995) * p₄.2 * p₅.1 ^ 3 + (4993 / 7980) * p₄.2 ^ 3 * p₅.1 - (83173 / 7980) * p₄.1 ^ 2 * p₄.2 * p₅.1 - (2853 / 2660) * p₃.2 * p₅.1 ^ 3 + (11554 / 1995) * p₃.2 * p₄.2 ^ 2 * p₅.1 + (8389 / 1330) * p₃.2 * p₄.1 * p₅.1 ^ 2 - (1861 / 399) * p₃.2 * p₄.1 ^ 2 * p₅.1 - (10739 / 1995) * p₃.2 ^ 2 * p₄.2 * p₅.1 - (4159 / 3990) * p₃.2 ^ 3 * p₅.1 + (4629 / 2660) * p₃.1 * p₄.2 * p₅.1 ^ 2 + (85801 / 3990) * p₃.1 * p₄.1 * p₄.2 * p₅.1 - (1089 / 140) * p₃.1 * p₃.2 * p₅.1 ^ 2 + (4159 / 1995) * p₃.1 * p₃.2 * p₄.1 * p₅.1 - (4966 / 665) * p₃.1 ^ 2 * p₄.2 * p₅.1 - (4159 / 3990) * p₃.1 ^ 2 * p₃.2 * p₅.1 - (1619 / 1995) * p₂.2 * p₅.1 ^ 3 + (11009 / 3192) * p₂.2 * p₄.1 * p₅.1 ^ 2 - (2027 / 7980) * p₂.2 * p₄.1 * p₄.2 ^ 2 - (21041 / 15960) * p₂.2 * p₄.1 ^ 2 * p₅.1 - (2027 / 7980) * p₂.2 * p₄.1 ^ 3 - (157147 / 15960) * p₂.2 * p₃.2 * p₄.2 * p₅.1 + (16241 / 1596) * p₂.2 * p₃.2 * p₄.1 * p₄.2 - (16241 / 3192) * p₂.2 * p₃.2 ^ 2 * p₄.1 - (136811 / 7980) * p₂.2 * p₃.1 * p₅.1 ^ 2 - (6197 / 840) * p₂.2 * p₃.1 * p₄.2 ^ 2 - (4127 / 15960) * p₂.2 * p₃.1 * p₄.1 * p₅.1 + (2127 / 760) * p₂.2 * p₃.1 * p₄.1 ^ 2 + (10148 / 1995) * p₂.2 * p₃.1 * p₃.2 * p₄.2 - (5074 / 1995) * p₂.2 * p₃.1 * p₃.2 ^ 2 + (158297 / 15960) * p₂.2 * p₃.1 ^ 2 * p₅.1 - (1 / 760) * p₂.2 * p₃.1 ^ 2 * p₄.1 - (5074 / 1995) * p₂.2 * p₃.1 ^ 3 - (4993 / 7980) * p₂.2 ^ 2 * p₄.2 * p₅.1 + (2027 / 7980) * p₂.2 ^ 2 * p₄.1 * p₄.2 + (38749 / 2280) * p₂.2 ^ 2 * p₃.2 * p₅.1 - (16241 / 3192) * p₂.2 ^ 2 * p₃.2 * p₄.1 + (6197 / 840) * p₂.2 ^ 2 * p₃.1 * p₄.2 - (295199 / 15960) * p₂.2 ^ 2 * p₃.1 * p₃.2 - (40849 / 5320) * p₂.1 * p₄.2 * p₅.1 ^ 2 + (88191 / 5320) * p₂.1 * p₄.1 * p₄.2 * p₅.1 + (13607 / 1330) * p₂.1 * p₃.2 * p₅.1 ^ 2 - (14111 / 3192) * p₂.1 * p₃.2 * p₄.2 ^ 2 - (14793 / 2660) * p₂.1 * p₃.2 * p₄.1 * p₅.1 + (6197 / 840) * p₂.1 * p₃.2 * p₄.1 ^ 2 + (46961 / 15960) * p₂.1 * p₃.2 ^ 2 * p₄.2 + (11797 / 7980) * p₂.1 * p₃.2 ^ 3 - (125897 / 7980) * p₂.1 * p₃.1 * p₄.2 * p₅.1 - (31383 / 2660) * p₂.1 * p₃.1 * p₄.1 * p₄.2 - (147097 / 15960) * p₂.1 * p₃.1 * p₃.2 * p₅.1 - (11797 / 3990) * p₂.1 * p₃.1 * p₃.2 * p₄.1 + (31383 / 5320) * p₂.1 * p₃.1 ^ 2 * p₄.2 + (11797 / 7980) * p₂.1 * p₃.1 ^ 2 * p₃.2 + (33751 / 7980) * p₂.1 * p₂.2 * p₅.1 ^ 2 - (14759 / 2660) * p₂.1 * p₂.2 * p₄.1 * p₅.1 + (2027 / 7980) * p₂.1 * p₂.2 * p₄.1 ^ 2 + (743 / 1140) * p₂.1 * p₂.2 * p₃.2 * p₄.2 + (261203 / 15960) * p₂.1 * p₂.2 * p₃.2 ^ 2 + (52297 / 2280) * p₂.1 * p₂.2 * p₃.1 * p₅.1 + (35267 / 7980) * p₂.1 * p₂.2 * p₃.1 * p₄.1 - (312197 / 15960) * p₂.1 * p₂.2 * p₃.1 ^ 2 - (2833 / 2660) * p₂.1 * p₂.2 ^ 2 * p₃.2 + (203 / 285) * p₂.1 ^ 2 * p₄.2 * p₅.1 - (2987 / 570) * p₂.1 ^ 2 * p₃.2 * p₅.1 - (6197 / 840) * p₂.1 ^ 2 * p₃.2 * p₄.1 + (31383 / 5320) * p₂.1 ^ 2 * p₃.1 * p₄.2 + (39743 / 2280) * p₂.1 ^ 2 * p₃.1 * p₃.2 - (2833 / 2660) * p₂.1 ^ 2 * p₂.2 * p₃.1)
      * Psi p₀ p₃ p₂ p₄
    + (-(4771 / 5320) * p₃.2 * p₄.2 ^ 2 * p₅.1 - (7423 / 5320) * p₃.2 * p₄.1 * p₅.1 ^ 2 + (10139 / 2660) * p₃.2 * p₄.1 ^ 2 * p₅.1 + (32449 / 5320) * p₃.2 ^ 2 * p₄.2 * p₅.1 - (86159 / 15960) * p₃.2 ^ 2 * p₄.1 * p₄.2 - (1977 / 380) * p₃.2 ^ 3 * p₅.1 + (6003 / 5320) * p₃.2 ^ 3 * p₄.1 + (187 / 1064) * p₃.1 * p₄.2 * p₅.1 ^ 2 - (87497 / 15960) * p₃.1 * p₄.2 ^ 3 - (5099 / 1064) * p₃.1 * p₄.1 * p₄.2 * p₅.1 - (87497 / 15960) * p₃.1 * p₄.1 ^ 2 * p₄.2 + (5493 / 1330) * p₃.1 * p₃.2 * p₅.1 ^ 2 + (47885 / 3192) * p₃.1 * p₃.2 * p₄.2 ^ 2 + (22507 / 5320) * p₃.1 * p₃.2 * p₄.1 * p₅.1 + (101207 / 15960) * p₃.1 * p₃.2 * p₄.1 ^ 2 - (31651 / 3990) * p₃.1 * p₃.2 ^ 2 * p₄.2 + (8686 / 1995) * p₃.1 * p₃.2 ^ 3 - (3151 / 7980) * p₃.1 ^ 2 * p₄.2 * p₅.1 + (2479 / 760) * p₃.1 ^ 2 * p₄.1 * p₄.2 - (3901 / 532) * p₃.1 ^ 2 * p₃.2 * p₅.1 - (17281 / 2280) * p₃.1 ^ 2 * p₃.2 * p₄.1 + (1031 / 1330) * p₃.1 ^ 3 * p₄.2 + (8686 / 1995) * p₃.1 ^ 3 * p₃.2 + (2027 / 7980) * p₂.2 * p₄.1 * p₅.1 ^ 2 - (2027 / 7980) * p₂.2 * p₄.1 ^ 2 * p₅.1 + (4967 / 1596) * p₂.2 * p₃.2 * p₄.2 * p₅.1 - (60751 / 7980) * p₂.2 * p₃.2 * p₄.1 * p₄.2 + (25111 / 2660) * p₂.2 * p₃.1 * p₅.1 ^ 2 + (3989 / 665) * p₂.2 * p₃.1 * p₄.1 * p₅.1 - (60751 / 7980) * p₂.2 * p₃.1 * p₄.1 ^ 2 + (11931 / 665) * p₂.2 * p₃.1 * p₃.2 * p₄.2 - (16729 / 3192) * p₂.2 * p₃.1 * p₃.2 ^ 2 - (32419 / 3192) * p₂.2 * p₃.1 ^ 2 * p₅.1 + (1567 / 105) * p₂.2 * p₃.1 ^ 2 * p₄.1 - (16057 / 3192) * p₂.2 * p₃.1 ^ 3 + (2027 / 7980) * p₂.2 ^ 2 * p₄.1 * p₄.2 - (19277 / 1596) * p₂.2 ^ 2 * p₃.2 * p₅.1 + (5023 / 2660) * p₂.2 ^ 2 * p₃.2 * p₄.1 + (3641 / 1330) * p₂.2 ^ 2 * p₃.1 * p₄.2 + (98383 / 15960) * p₂.2 ^ 2 * p₃.1 * p₃.2 + (2027 / 7980) * p₂.1 * p₄.1 * p₄.2 * p₅.1 - (7337 / 798) * p₂.1 * p₃.2 * p₅.1 ^ 2 + (754 / 665) * p₂.1 * p₃.2 * p₄.2 ^ 2 + (1302 / 95) * p₂.1 * p₃.2 * p₄.1 * p₅.1 - (77179 / 7980) * p₂.1 * p₃.2 * p₄.1 ^ 2 - (3189 / 380) * p₂.1 * p₃.2 ^ 2 * p₄.2 + (1977 / 380) * p₂.1 * p₃.2 ^ 3 - (70237 / 7980) * p₂.1 * p₃.1 * p₄.2 * p₅.1 + (86227 / 7980) * p₂.1 * p₃.1 * p₄.1 * p₄.2 + (94471 / 15960) * p₂.1 * p₃.1 * p₃.2 * p₅.1 - (82 / 57) * p₂.1 * p₃.1 * p₃.2 * p₄.1 - (4487 / 1140) * p₂.1 * p₃.1 ^ 2 * p₄.2 + (1897 / 380) * p₂.1 * p₃.1 ^ 2 * p₃.2 - (2027 / 3990) * p₂.1 * p₂.2 * p₄.1 * p₅.1 + (2027 / 3990) * p₂.1 * p₂.2 * p₄.1 ^ 2 + (10331 / 2660) * p₂.1 * p₂.2 * p₃.2 * p₄.2 - (118733 / 7980) * p₂.1 * p₂.2 * p₃.2 ^ 2 - (5733 / 380) * p₂.1 * p₂.2 * p₃.1 * p₅.1 + (87071 / 7980) * p₂.1 * p₂.2 * p₃.1 * p₄.1 + (59 / 105) * p₂.1 * p₂.2 * p₃.1 ^ 2 - (191 / 210) * p₂.1 * p₂.2 ^ 2 * p₃.2 - (2027 / 7980) * p₂.1 ^ 2 * p₄.1 * p₄.2 + (24557 / 3990) * p₂.1 ^ 2 * p₃.2 * p₅.1 - (14351 / 1330) * p₂.1 ^ 2 * p₃.2 * p₄.1 + (66943 / 7980) * p₂.1 ^ 2 * p₃.1 * p₄.2 - (148051 / 15960) * p₂.1 ^ 2 * p₃.1 * p₃.2 - (2251 / 570) * p₂.1 ^ 2 * p₂.2 * p₃.1 + (6064 / 1995) * p₂.1 ^ 3 * p₃.2)
      * Psi p₀ p₄ p₂ p₅
    + ((223 / 2660) * p₂.2 * p₄.1 ^ 3 + (569 / 266) * p₂.2 * p₃.2 * p₄.1 * p₄.2 + (5527 / 3990) * p₂.2 * p₃.1 * p₄.1 ^ 2 - (15489 / 2660) * p₂.2 * p₃.1 * p₃.2 * p₄.2 + (45463 / 15960) * p₂.2 * p₃.1 * p₃.2 ^ 2 - (13331 / 15960) * p₂.2 * p₃.1 ^ 2 * p₅.1 - (9263 / 2660) * p₂.2 * p₃.1 ^ 2 * p₄.1 + (45463 / 15960) * p₂.2 * p₃.1 ^ 3 + (7325 / 1596) * p₂.2 ^ 2 * p₄.1 * p₄.2 - (30713 / 7980) * p₂.2 ^ 2 * p₃.2 * p₄.1 - (39551 / 7980) * p₂.2 ^ 2 * p₃.1 * p₄.2 + (90341 / 15960) * p₂.2 ^ 2 * p₃.1 * p₃.2 - (11491 / 3990) * p₂.2 ^ 3 * p₄.1 + (6001 / 1140) * p₂.2 ^ 3 * p₃.1 + (2209 / 3990) * p₂.1 * p₄.2 ^ 3 + (80 / 57) * p₂.1 * p₄.1 * p₄.2 * p₅.1 + (3749 / 7980) * p₂.1 * p₄.1 ^ 2 * p₄.2 + (841 / 3192) * p₂.1 * p₃.2 * p₄.2 ^ 2 - (17075 / 3192) * p₂.1 * p₃.2 * p₄.1 * p₅.1 + (31687 / 15960) * p₂.1 * p₃.2 * p₄.1 ^ 2 - (869 / 2280) * p₂.1 * p₃.2 ^ 2 * p₄.2 - (497 / 1140) * p₂.1 * p₃.2 ^ 3 + (12595 / 3192) * p₂.1 * p₃.1 * p₄.2 * p₅.1 - (515 / 532) * p₂.1 * p₃.1 * p₄.1 * p₄.2 + (13331 / 15960) * p₂.1 * p₃.1 * p₃.2 * p₅.1 - (47 / 35) * p₂.1 * p₃.1 * p₃.2 * p₄.1 - (22007 / 15960) * p₂.1 * p₃.1 ^ 2 * p₄.2 - (497 / 1140) * p₂.1 * p₃.1 ^ 2 * p₃.2 + (1846 / 399) * p₂.1 * p₂.2 * p₄.1 ^ 2 - (1039 / 570) * p₂.1 * p₂.2 * p₃.2 * p₄.2 + (1383 / 1330) * p₂.1 * p₂.2 * p₃.2 ^ 2 - (1562 / 1995) * p₂.1 * p₂.2 * p₃.1 * p₅.1 - (16027 / 1330) * p₂.1 * p₂.2 * p₃.1 * p₄.1 + (10364 / 1995) * p₂.1 * p₂.2 * p₃.1 ^ 2 + (241 / 1995) * p₂.1 * p₂.2 ^ 2 * p₄.2 + (11 / 210) * p₂.1 * p₂.2 ^ 2 * p₃.2 - (3805 / 1596) * p₂.1 * p₂.2 ^ 3 - (80 / 57) * p₂.1 ^ 2 * p₄.2 * p₅.1 - (59 / 1596) * p₂.1 ^ 2 * p₄.1 * p₄.2 + (1454 / 665) * p₂.1 ^ 2 * p₃.2 * p₅.1 + (28529 / 7980) * p₂.1 ^ 2 * p₃.2 * p₄.1 - (17177 / 7980) * p₂.1 ^ 2 * p₃.1 * p₄.2 + (4805 / 3192) * p₂.1 ^ 2 * p₃.1 * p₃.2 - (11491 / 3990) * p₂.1 ^ 2 * p₂.2 * p₄.1 + (66041 / 7980) * p₂.1 ^ 2 * p₂.2 * p₃.1 + (241 / 1995) * p₂.1 ^ 3 * p₄.2 - (1968 / 665) * p₂.1 ^ 3 * p₃.2 - (3805 / 1596) * p₂.1 ^ 3 * p₂.2)
      * Psi p₀ p₅ p₃ p₄
    + ((5493 / 1330) * p₂.2 * p₃.1 * p₅.1 ^ 2 - (17719 / 7980) * p₂.2 * p₃.1 * p₄.1 ^ 2 + (12881 / 1995) * p₂.2 * p₃.1 * p₃.2 * p₄.2 - (341 / 2280) * p₂.2 * p₃.1 * p₃.2 ^ 2 - (4217 / 2280) * p₂.2 * p₃.1 ^ 2 * p₅.1 + (17 / 190) * p₂.2 * p₃.1 ^ 2 * p₄.1 - (341 / 2280) * p₂.2 * p₃.1 ^ 3 - (64061 / 7980) * p₂.2 ^ 2 * p₄.2 * p₅.1 + (13519 / 1596) * p₂.2 ^ 2 * p₄.1 * p₄.2 - (523 / 133) * p₂.2 ^ 2 * p₃.2 * p₅.1 + (3821 / 3990) * p₂.2 ^ 2 * p₃.2 * p₄.1 - (19129 / 3990) * p₂.2 ^ 2 * p₃.1 * p₄.2 + (98533 / 15960) * p₂.2 ^ 2 * p₃.1 * p₃.2 - (811 / 1330) * p₂.1 * p₄.2 * p₅.1 ^ 2 + (115 / 1596) * p₂.1 * p₄.2 ^ 3 + (115 / 1596) * p₂.1 * p₄.1 ^ 2 * p₄.2 - (115 / 798) * p₂.1 * p₃.2 * p₄.1 * p₅.1 + (115 / 798) * p₂.1 * p₃.2 * p₄.1 ^ 2 - (1965 / 532) * p₂.1 * p₃.2 ^ 2 * p₄.2 + (471 / 190) * p₂.1 * p₃.1 * p₄.2 * p₅.1 + (789 / 380) * p₂.1 * p₃.1 * p₄.1 * p₄.2 - (4477 / 15960) * p₂.1 * p₃.1 * p₃.2 * p₅.1 + (18671 / 7980) * p₂.1 * p₃.1 * p₃.2 * p₄.1 + (222 / 665) * p₂.1 * p₃.1 ^ 2 * p₄.2 + (4603 / 1596) * p₂.1 * p₂.2 * p₅.1 ^ 2 - (191 / 105) * p₂.1 * p₂.2 * p₄.1 ^ 2 + (2479 / 1995) * p₂.1 * p₂.2 * p₃.2 * p₄.2 - (28859 / 3990) * p₂.1 * p₂.2 * p₃.2 ^ 2 - (607 / 76) * p₂.1 * p₂.2 * p₃.1 * p₅.1 + (382 / 105) * p₂.1 * p₂.2 * p₃.1 * p₄.1 + (6551 / 1995) * p₂.1 * p₂.2 * p₃.1 ^ 2 - (191 / 210) * p₂.1 * p₂.2 ^ 2 * p₃.2 - (24659 / 2660) * p₂.1 ^ 2 * p₄.2 * p₅.1 + (82111 / 7980) * p₂.1 ^ 2 * p₄.1 * p₄.2 + (16451 / 2660) * p₂.1 ^ 2 * p₃.2 * p₅.1 - (491 / 570) * p₂.1 ^ 2 * p₃.2 * p₄.1 - (7143 / 1330) * p₂.1 ^ 2 * p₃.1 * p₄.2 - (69311 / 15960) * p₂.1 ^ 2 * p₃.1 * p₃.2 - (2833 / 1330) * p₂.1 ^ 2 * p₂.2 * p₅.1 + (2833 / 1330) * p₂.1 ^ 2 * p₂.2 * p₃.1 - (6064 / 1995) * p₂.1 ^ 3 * p₃.2)
      * Psi p₀ p₁ p₃ p₅
      = cross p₀ p₁ p₂ * cross p₀ p₂ p₃ * cross p₀ p₂ p₅ * cross p₀ p₄ p₅ := by
  simp only [Psi, qq, cross, h0x, h0y, h5y, hr1x, hr1y]
  ring

/-- No six points in general position carry the witness set of class 14.
The hypotheses name the forced midpoint relation and the 8 witnesses used.
The identity is applied to the similarity image of the configuration and
pulled back with `psi_sim` and `cross_sim`. -/
theorem not_pattern_k14 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hr1x : (p 1).1 = (p 2).1 + (p 3).1 - (p 4).1)
    (hr1y : (p 1).2 = (p 2).2 + (p 3).2 - (p 4).2)
    (hw1 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw2 : Psi (p 0) (p 4) (p 1) (p 3) = 0)
    (hw3 : Psi (p 2) (p 5) (p 1) (p 4) = 0)
    (hw4 : Psi (p 0) (p 2) (p 1) (p 5) = 0)
    (hw5 : Psi (p 0) (p 3) (p 2) (p 4) = 0)
    (hw6 : Psi (p 0) (p 4) (p 2) (p 5) = 0)
    (hw7 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw8 : Psi (p 0) (p 1) (p 3) (p 5) = 0)
    : False := by
  obtain ⟨hne, hcol, hcyc⟩ := hgp
  have hnz : ((p 5).1 - (p 0).1) ^ 2 + ((p 5).2 - (p 0).2) ^ 2 ≠ 0 := by
    intro h
    exact hne 0 5 (by decide)
      (eq_of_sqdist_eq_zero (by simp only [sqdist]; linear_combination h))
  have key := psi_identity_k14
    (simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 0), simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 0))
    (simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 1), simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 1))
    (simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 2), simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 2))
    (simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 3), simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 3))
    (simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 4), simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 4))
    (simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 5), simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 5))
    (show simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 1) = simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 2) + simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 3) - simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 4) by
      simp only [simx, simy]
      linear_combination ((p 5).1 - (p 0).1) * hr1x + ((p 5).2 - (p 0).2) * hr1y)
    (show simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 1) = simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 2) + simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 3) - simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 4) by
      simp only [simx, simy]
      linear_combination ((p 5).1 - (p 0).1) * hr1y - ((p 5).2 - (p 0).2) * hr1x)
    (show simx (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 0) = 0 by simp only [simx]; ring)
    (show simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 0) = 0 by simp only [simy]; ring)
    (show simy (p 0) ((p 5).1 - (p 0).1, (p 5).2 - (p 0).2) (p 5) = 0 by simp only [simy]; ring)
  simp only [psi_sim, cross_sim, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, mul_zero, add_zero, zero_add] at key
  have hz : cross (p 0) (p 1) (p 2) * cross (p 0) (p 2) (p 3) * cross (p 0) (p 2) (p 5) * cross (p 0) (p 4) (p 5) = 0 := by
    have h4 : (((p 5).1 - (p 0).1) ^ 2 + ((p 5).2 - (p 0).2) ^ 2) ^ 4
        * (cross (p 0) (p 1) (p 2) * cross (p 0) (p 2) (p 3) * cross (p 0) (p 2) (p 5) * cross (p 0) (p 4) (p 5)) = 0 := by
      linear_combination -key
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h (pow_ne_zero 4 hnz)
    · exact h
  have hf1 : cross (p 0) (p 1) (p 2) ≠ 0 := fun h => hcol 0 1 2 (by decide) (by decide) h
  have hf2 : cross (p 0) (p 2) (p 3) ≠ 0 := fun h => hcol 0 2 3 (by decide) (by decide) h
  have hf3 : cross (p 0) (p 2) (p 5) ≠ 0 := fun h => hcol 0 2 5 (by decide) (by decide) h
  have hf4 : cross (p 0) (p 4) (p 5) ≠ 0 := fun h => hcol 0 4 5 (by decide) (by decide) h
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hf1 hf2) hf3) hf4) hz

/-- The mask of class 14. -/
def maskK14 : Mask := 321419383917544127594562

/-- **Class 14, sharp form.**  No six points in general position support the
mask of class 14 while the cell outside the mask listed here is not a
witness.  That cell is needed only to rule out the orthocentric branch of
the dichotomy `parallelogram_or_orthocentric`. -/
theorem not_supports_free_k14 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK14) (hf : cellPsi p 75 ≠ 0) : False := by
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hs 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have c46 : Psi (p 2) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 46 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 46 = ((1, 4), (2, 5)) from by decide)] at h
  have c48 : Psi (p 0) (p 2) (p 1) (p 5) = 0 := by
    have h := hs 48 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 48 = ((1, 5), (0, 2)) from by decide)] at h
  have c61 : Psi (p 0) (p 3) (p 2) (p 4) = 0 := by
    have h := hs 61 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 61 = ((2, 4), (0, 3)) from by decide)] at h
  have c68 : Psi (p 0) (p 4) (p 2) (p 5) = 0 := by
    have h := hs 68 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 68 = ((2, 5), (0, 4)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hs 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  have c45 : Psi (p 2) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 45 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 45 = ((1, 4), (2, 3)) from by decide)] at h
  have c57 : Psi (p 1) (p 4) (p 2) (p 3) = 0 := by
    have h := hs 57 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 57 = ((2, 3), (1, 4)) from by decide)] at h
  have hm := midpoint_of_two_complementary_witnesses (p 2) (p 3) (p 1) (p 4)
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ne_of_gp hgp (by decide)) (ne_of_gp hgp (by decide))
    (ncol_of_gp hgp (by decide) (by decide) (by decide))
    c45 c57
    (fun hh => hf (by
      rw [cellPsi_eq (show cellOf 75 = ((3, 4), (1, 2)) from by decide)]
      exact (psi_eq_zero_swap₁₂ (p 1) (p 2) (p 3) (p 4)).1 hh))
  exact not_pattern_k14 p hgp
    (by linarith [hm.1] : (p 1).1 = (p 2).1 + (p 3).1 - (p 4).1)
    (by linarith [hm.2] : (p 1).2 = (p 2).2 + (p 3).2 - (p 4).2)
    c27 c37 c46 c48 c61 c68 c74 c78

/-- **Class 14.**  No six points in general position carry the mask of class 14. -/
theorem not_carries_k14 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK14) : False :=
  not_supports_free_k14 p hgp (supports_of_carries hc)
    (fun hh => absurd ((hc 75 (by norm_num)).1 hh) (by decide))

theorem maskK14_mem : maskK14 ∈ censusRest := by decide












end QR3

end DistinctCircumradii

#print axioms DistinctCircumradii.QR3.cellPsi_eq
#print axioms DistinctCircumradii.QR3.psi_shift
#print axioms DistinctCircumradii.QR3.cross_shift
#print axioms DistinctCircumradii.QR3.sqdist_shift
#print axioms DistinctCircumradii.QR3.psi_sim
#print axioms DistinctCircumradii.QR3.cross_sim
#print axioms DistinctCircumradii.QR3.sqdist_sim
#print axioms DistinctCircumradii.QR3.psi_identity_k14
#print axioms DistinctCircumradii.QR3.not_pattern_k14
#print axioms DistinctCircumradii.QR3.not_supports_free_k14
#print axioms DistinctCircumradii.QR3.not_carries_k14
#print axioms DistinctCircumradii.QR3.maskK14_mem
