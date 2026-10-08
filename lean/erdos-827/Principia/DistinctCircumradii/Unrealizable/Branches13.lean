import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（枝分かれの議論）：名前空間 `QB13` の k24

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QB13

theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-- The mask of the class treated here. -/
def maskK31 : Mask := 20023166075136716235374660

theorem maskK31_mem : maskK31 ∈ censusRest := by decide

/-! ## Points as complex numbers -/

/-- Collinearity read off from the same kind of identity. -/
theorem collinear_of_cross_eq {a b c : Pt}
    (h : (toC c - toC a) * (barC b - barC a) = (barC c - barC a) * (toC b - toC a)) :
    Collinear3 a b c := by
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, toC_re, toC_im,
    barC_re, barC_im] at h2
  simp only [Collinear3, cross]
  linarith

/-! ## The normalised directions -/

/-- Division cancelled on the right. -/
theorem div_mul_cancel_ne {a b : ℂ} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hb, mul_one]

/-- The configuration moved by the similarity that sends `p 0` to `0` and
`p 1` to `1`. -/
noncomputable def normY (p : Fin 6 → Pt) (i : Fin 6) : ℂ :=
  (toC (p i) - toC (p 0)) / (toC (p 1) - toC (p 0))

/-- The conjugate picture of `normY`. -/
noncomputable def normC (p : Fin 6 → Pt) (i : Fin 6) : ℂ :=
  (barC (p i) - barC (p 0)) / (barC (p 1) - barC (p 0))

/-- The normalised direction of the segment `p i p j`. -/
noncomputable def normW (p : Fin 6 → Pt) (i j : Fin 6) : ℂ :=
  (normY p i - normY p j) / (normC p i - normC p j)

section Normalisation

variable {p : Fin 6 → Pt}

theorem normY_sub (hs : toC (p 1) - toC (p 0) ≠ 0) (i j : Fin 6) :
    toC (p i) - toC (p j) = (normY p i - normY p j) * (toC (p 1) - toC (p 0)) := by
  have e : normY p i - normY p j
      = (toC (p i) - toC (p j)) / (toC (p 1) - toC (p 0)) := by
    unfold normY
    rw [div_sub_div_same]
    congr 1
    ring
  rw [e, div_mul_cancel_ne hs]

theorem normC_sub (ht : barC (p 1) - barC (p 0) ≠ 0) (i j : Fin 6) :
    barC (p i) - barC (p j) = (normC p i - normC p j) * (barC (p 1) - barC (p 0)) := by
  have e : normC p i - normC p j
      = (barC (p i) - barC (p j)) / (barC (p 1) - barC (p 0)) := by
    unfold normC
    rw [div_sub_div_same]
    congr 1
    ring
  rw [e, div_mul_cancel_ne ht]

theorem normY_zero : normY p 0 = 0 := by unfold normY; rw [sub_self, zero_div]

theorem normC_zero : normC p 0 = 0 := by unfold normC; rw [sub_self, zero_div]

theorem normY_one (hs : toC (p 1) - toC (p 0) ≠ 0) : normY p 1 = 1 := by
  unfold normY; exact div_self hs

theorem normC_one (ht : barC (p 1) - barC (p 0) ≠ 0) : normC p 1 = 1 := by
  unfold normC; exact div_self ht

theorem normY_sub_ne (hs : toC (p 1) - toC (p 0) ≠ 0) {i j : Fin 6} (h : p i ≠ p j) :
    normY p i - normY p j ≠ 0 := by
  intro hz
  exact toC_sub_ne_zero h (by rw [normY_sub hs i j, hz, zero_mul])

theorem normC_sub_ne (ht : barC (p 1) - barC (p 0) ≠ 0) {i j : Fin 6} (h : p i ≠ p j) :
    normC p i - normC p j ≠ 0 := by
  intro hz
  exact barC_sub_ne_zero h (by rw [normC_sub ht i j, hz, zero_mul])

theorem normW_spec {i j : Fin 6} (h : normC p i - normC p j ≠ 0) :
    normY p i - normY p j = normW p i j * (normC p i - normC p j) := by
  unfold normW
  exact (div_mul_cancel_ne h).symm

theorem normW_spec' {i j : Fin 6} (h : normC p i - normC p j ≠ 0) :
    normY p j - normY p i = normW p i j * (normC p j - normC p i) := by
  linear_combination - normW_spec h

theorem normW_ne {i j : Fin 6} (hy : normY p i - normY p j ≠ 0)
    (hc : normC p i - normC p j ≠ 0) : normW p i j ≠ 0 := by
  unfold normW
  exact div_ne_zero hy hc

/-- The witness cell of a configuration, read in the normalised picture. -/
theorem cell_bridge (hs : toC (p 1) - toC (p 0) ≠ 0) (ht : barC (p 1) - barC (p 0) ≠ 0)
    (a b c d : Fin 6) (h : Psi (p a) (p b) (p c) (p d) = 0) :
    (normY p a - normY p c) * (normY p a - normY p d)
        * ((normC p b - normC p c) * (normC p b - normC p d))
      = (normC p a - normC p c) * (normC p a - normC p d)
        * ((normY p b - normY p c) * (normY p b - normY p d)) := by
  have W := witnessEq h
  rw [normY_sub hs a c, normY_sub hs a d, normC_sub ht b c, normC_sub ht b d,
      normC_sub ht a c, normC_sub ht a d, normY_sub hs b c, normY_sub hs b d] at W
  have hK : (toC (p 1) - toC (p 0)) ^ 2 * (barC (p 1) - barC (p 0)) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 2 ht)
  exact mul_right_cancel₀ hK (by linear_combination W)

end Normalisation

/-- A witness cell as a monomial identity between four normalised directions. -/
theorem witness_monomial {Ya Yb Yc Yd Ca Cb Cc Cd wac wad wbc wbd : ℂ}
    (hac : Ya - Yc = wac * (Ca - Cc)) (had : Ya - Yd = wad * (Ca - Cd))
    (hbc : Yb - Yc = wbc * (Cb - Cc)) (hbd : Yb - Yd = wbd * (Cb - Cd))
    (nac : Ca - Cc ≠ 0) (nad : Ca - Cd ≠ 0) (nbc : Cb - Cc ≠ 0) (nbd : Cb - Cd ≠ 0)
    (key : (Ya - Yc) * (Ya - Yd) * ((Cb - Cc) * (Cb - Cd))
      = (Ca - Cc) * (Ca - Cd) * ((Yb - Yc) * (Yb - Yd))) :
    wac * wad = wbc * wbd := by
  have h : (wac * wad - wbc * wbd) * ((Ca - Cc) * (Ca - Cd) * ((Cb - Cc) * (Cb - Cd))) = 0 := by
    linear_combination key - (Ya - Yd) * (Cb - Cc) * (Cb - Cd) * hac
      - wac * (Ca - Cc) * (Cb - Cc) * (Cb - Cd) * had
      + (Ca - Cc) * (Ca - Cd) * (Yb - Yd) * hbc
      + (Ca - Cc) * (Ca - Cd) * wbc * (Cb - Cc) * hbd
  rcases mul_eq_zero.mp h with h1 | h1
  · linear_combination h1
  · exact absurd h1 (mul_ne_zero (mul_ne_zero nac nad) (mul_ne_zero nbc nbd))

/-! ## The algebra of the branches -/

/-- A square root has two values. -/
theorem sq_split {u v : ℂ} (h : u ^ 2 = v ^ 2) : u = v ∨ u = -v := by
  have k : (u - v) * (u + v) = 0 := by linear_combination h
  rcases mul_eq_zero.mp k with h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (by linear_combination h1)

/-- A twenty-second root of unity lies on one of the four cyclotomic factors. -/
theorem pow22_split {x : ℂ} (h : x ^ 22 = 1) :
    x = 1 ∨ x = -1
      ∨ x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0
      ∨ x ^ 10 - x ^ 9 + x ^ 8 - x ^ 7 + x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0 := by
  have k : (x - 1) * ((x + 1)
      * ((x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1)
        * (x ^ 10 - x ^ 9 + x ^ 8 - x ^ 7 + x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1)))
      = 0 := by linear_combination h
  rcases mul_eq_zero.mp k with h1 | h1
  · exact Or.inl (by linear_combination h1)
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inr (Or.inl (by linear_combination h2))
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h3))

/-- A sixth root of unity lies on one of the four cyclotomic factors. -/
theorem pow6_split {x : ℂ} (h : x ^ 6 = 1) :
    x = 1 ∨ x = -1 ∨ x ^ 2 + x + 1 = 0 ∨ x ^ 2 - x + 1 = 0 := by
  have k : (x - 1) * ((x + 1) * ((x ^ 2 + x + 1) * (x ^ 2 - x + 1))) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp k with h1 | h1
  · exact Or.inl (by linear_combination h1)
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inr (Or.inl (by linear_combination h2))
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h3))

/-- The coordinates of two points, written through their directions to `p 0`
and `p 1`, satisfy one relation for each pair. -/
theorem pair_relation {Yi Ci Yj Cj Ui Vi Uj Vj wij : ℂ}
    (h1 : Yi = Ui * Ci) (h2 : 1 - Yi = Vi * (1 - Ci))
    (h3 : Yj = Uj * Cj) (h4 : 1 - Yj = Vj * (1 - Cj))
    (h5 : Yi - Yj = wij * (Ci - Cj)) :
    Ui * (1 - Vi) * (Uj - Vj) - Uj * (1 - Vj) * (Ui - Vi)
      = wij * ((1 - Vi) * (Uj - Vj) - (1 - Vj) * (Ui - Vi)) := by
  have ei : Ci * (Ui - Vi) = 1 - Vi := by linear_combination -h1 - h2
  have ej : Cj * (Uj - Vj) = 1 - Vj := by linear_combination -h3 - h4
  have fi : Yi * (Ui - Vi) = Ui * (1 - Vi) := by linear_combination (Ui - Vi) * h1 + Ui * ei
  have fj : Yj * (Uj - Vj) = Uj * (1 - Vj) := by linear_combination (Uj - Vj) * h3 + Uj * ej
  linear_combination (Ui - Vi) * (Uj - Vj) * h5 - (Uj - Vj) * fi + (Ui - Vi) * fj
    + wij * (Uj - Vj) * ei - wij * (Ui - Vi) * ej

/-- Two normalised directions out of one point agree exactly when the three
points are on a line. -/
theorem collinear_of_w {p : Fin 6 → Pt} (hs : toC (p 1) - toC (p 0) ≠ 0)
    (ht : barC (p 1) - barC (p 0) ≠ 0) {a b c : Fin 6} {wab wac : ℂ}
    (hb : normY p a - normY p b = wab * (normC p a - normC p b))
    (hc : normY p a - normY p c = wac * (normC p a - normC p c))
    (h : wab = wac) : Collinear3 (p a) (p b) (p c) := by
  apply collinear_of_cross_eq
  rw [normY_sub hs c a, normC_sub ht b a, normC_sub ht c a, normY_sub hs b a]
  linear_combination
    (-(toC (p 1) - toC (p 0)) * (barC (p 1) - barC (p 0)) * (normC p b - normC p a)) * hc
    + ((toC (p 1) - toC (p 0)) * (barC (p 1) - barC (p 0)) * (normC p c - normC p a)) * hb
    + (-(toC (p 1) - toC (p 0)) * (barC (p 1) - barC (p 0)) * (normC p c - normC p a)
        * (normC p b - normC p a)) * h

set_option maxHeartbeats 40000000 in
/-- **The last class, the one with a modulus, is not supported either.** -/
theorem core_class24
    (w02 w03 w04 w05 w12 w13 w14 w15 w23 w24 w25 w34 w35 w45 : ℂ)
    (Y2 C2 Y3 C3 Y4 C4 Y5 C5 : ℂ)
    (n02 : w02 ≠ 0) (n03 : w03 ≠ 0) (n04 : w04 ≠ 0) (n05 : w05 ≠ 0)
    (n12 : w12 ≠ 0) (n13 : w13 ≠ 0) (n14 : w14 ≠ 0) (n15 : w15 ≠ 0)
    (n23 : w23 ≠ 0) (n24 : w24 ≠ 0) (n25 : w25 ≠ 0) (n34 : w34 ≠ 0)
    (n35 : w35 ≠ 0) (n45 : w45 ≠ 0)
    (E2 : w02 * w12 = w05 * w15)
    (E6 : w12 = w03 * w23)
    (E11 : w04 * w24 = w05 * w25)
    (E15 : w02 * w23 = w04 * w34)
    (E23 : w03 * w34 = w05 * w45)
    (E26 : w15 = w04 * w45)
    (E34 : w13 * w23 = w15 * w25)
    (E37 : w03 = w14 * w34)
    (E42 : w04 = w12 * w24)
    (E53 : w13 * w35 = w14 * w45)
    (E57 : w12 * w13 = w24 * w34)
    (E64 : w12 * w14 = w25 * w45)
    (E67 : w02 * w05 = w23 * w35)
    (E77 : w23 * w24 = w35 * w45)
    (E78 : w03 * w05 = w13 * w15)
    (u2 : Y2 = w02 * C2) (v2 : 1 - Y2 = w12 * (1 - C2))
    (u3 : Y3 = w03 * C3) (v3 : 1 - Y3 = w13 * (1 - C3))
    (u4 : Y4 = w04 * C4) (v4 : 1 - Y4 = w14 * (1 - C4))
    (u5 : Y5 = w05 * C5) (v5 : 1 - Y5 = w15 * (1 - C5))
    (g23 : Y2 - Y3 = w23 * (C2 - C3)) (g24 : Y2 - Y4 = w24 * (C2 - C4))
    (g34 : Y3 - Y4 = w34 * (C3 - C4)) (g35 : Y3 - Y5 = w35 * (C3 - C5))
    (g45 : Y4 - Y5 = w45 * (C4 - C5))
    (nc1 : w04 ≠ w05) (nc2 : w04 ≠ w45) (nc3 : w05 ≠ w45) :
    False := by
  have t04 : w04 ^ 2 = w24 ^ 6 * w45 ^ 8 := by
    have hPQ_t04 : w02 * w03 ^ 3 * w04 ^ 6 * w05 ^ 3 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 3 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2 = w02 * w03 ^ 3 * w04 ^ 4 * w05 ^ 3 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 3 * w24 ^ 9 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2 * w45 ^ 8 := by
      linear_combination (w03 ^ 3 * w04 ^ 6 * w05 ^ 3 * w12 ^ 6 * w13 * w14 ^ 3 * w15 * w23 ^ 3 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2) * E2 + (w03 ^ 3 * w04 ^ 6 * w05 ^ 4 * w12 ^ 5 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 3 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2) * E6 + (w03 ^ 4 * w04 ^ 6 * w05 ^ 4 * w12 ^ 4 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 4 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2) * E6 + (w03 ^ 5 * w04 ^ 6 * w05 ^ 4 * w12 ^ 3 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 5 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2) * E6 + (-w03 ^ 6 * w04 ^ 6 * w05 ^ 3 * w12 ^ 3 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 6 * w24 ^ 3 * w25 ^ 2 * w34 ^ 2 * w35 ^ 2) * E11 + (-w03 ^ 6 * w04 ^ 7 * w05 ^ 2 * w12 ^ 3 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 6 * w24 ^ 4 * w25 * w34 ^ 2 * w35 ^ 2) * E11 + (-w03 ^ 6 * w04 ^ 8 * w05 * w12 ^ 3 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 6 * w24 ^ 5 * w34 ^ 2 * w35 ^ 2) * E11 + (w03 ^ 5 * w04 ^ 9 * w05 * w12 ^ 3 * w13 * w14 ^ 3 * w15 ^ 2 * w23 ^ 6 * w24 ^ 6 * w34 * w35 ^ 2) * E23 + (w03 ^ 5 * w04 ^ 9 * w05 ^ 2 * w12 ^ 3 * w13 * w14 ^ 3 * w15 * w23 ^ 6 * w24 ^ 6 * w34 * w35 ^ 2 * w45) * E26 + (w03 ^ 4 * w04 ^ 10 * w05 ^ 2 * w12 ^ 3 * w13 * w14 ^ 3 * w15 * w23 ^ 6 * w24 ^ 6 * w34 * w35 ^ 2 * w45 ^ 2) * E37 + (w03 ^ 3 * w04 ^ 10 * w05 ^ 2 * w12 ^ 3 * w13 * w14 ^ 4 * w15 * w23 ^ 6 * w24 ^ 6 * w34 ^ 2 * w35 ^ 2 * w45 ^ 2) * E37 + (w03 ^ 3 * w04 ^ 9 * w05 ^ 2 * w12 ^ 3 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 6 * w34 ^ 3 * w35 ^ 2 * w45 ^ 2) * E42 + (w03 ^ 3 * w04 ^ 8 * w05 ^ 2 * w12 ^ 4 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 7 * w34 ^ 3 * w35 ^ 2 * w45 ^ 2) * E42 + (w03 ^ 3 * w04 ^ 7 * w05 ^ 2 * w12 ^ 5 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 8 * w34 ^ 3 * w35 ^ 2 * w45 ^ 2) * E42 + (w03 ^ 3 * w04 ^ 6 * w05 ^ 2 * w12 ^ 6 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 9 * w34 ^ 3 * w35 ^ 2 * w45 ^ 2) * E42 + (w03 ^ 3 * w04 ^ 5 * w05 ^ 2 * w12 ^ 7 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 10 * w34 ^ 3 * w35 ^ 2 * w45 ^ 2) * E42 + (w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 8 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 11 * w34 ^ 3 * w35 ^ 2 * w45 ^ 2) * E42 + (w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 9 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 12 * w34 ^ 3 * w35 * w45 ^ 2) * E53 + (-w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 9 * w14 ^ 6 * w15 * w23 ^ 6 * w24 ^ 11 * w34 ^ 2 * w35 * w45 ^ 3) * E57 + (w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 9 * w13 * w14 ^ 5 * w15 * w23 ^ 6 * w24 ^ 11 * w34 ^ 2 * w35 * w45 ^ 3) * E64 + (w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 8 * w13 * w14 ^ 4 * w15 * w23 ^ 6 * w24 ^ 11 * w25 * w34 ^ 2 * w35 * w45 ^ 4) * E64 + (w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 6 * w24 ^ 11 * w25 ^ 2 * w34 ^ 2 * w35 * w45 ^ 5) * E64 + (-w03 ^ 3 * w04 ^ 4 * w05 ^ 2 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 5 * w24 ^ 11 * w25 ^ 3 * w34 ^ 2 * w45 ^ 6) * E67 + (w02 * w03 ^ 3 * w04 ^ 4 * w05 ^ 3 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 4 * w24 ^ 10 * w25 ^ 3 * w34 ^ 2 * w45 ^ 6) * E77 + (w02 * w03 ^ 3 * w04 ^ 4 * w05 ^ 3 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 3 * w24 ^ 9 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 7) * E77
    have hK_t04 : w02 * w03 ^ 3 * w04 ^ 4 * w05 ^ 3 * w12 ^ 7 * w13 * w14 ^ 3 * w15 * w23 ^ 3 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n02) (pow_ne_zero 3 n03)) (pow_ne_zero 4 n04)) (pow_ne_zero 3 n05)) (pow_ne_zero 7 n12)) (n13)) (pow_ne_zero 3 n14)) (n15)) (pow_ne_zero 3 n23)) (pow_ne_zero 3 n24)) (pow_ne_zero 3 n25)) (pow_ne_zero 2 n34)) (pow_ne_zero 2 n35)
    exact mul_right_cancel₀ hK_t04 (by linear_combination hPQ_t04)
  have t13 : w13 ^ 2 = w24 ^ 4 * w45 ^ 2 := by
    have hPQ_t13 : w03 * w04 ^ 2 * w05 * w12 ^ 2 * w13 ^ 2 * w15 * w23 * w25 * w34 = w03 * w04 ^ 2 * w05 * w12 ^ 2 * w15 * w23 * w24 ^ 4 * w25 * w34 * w45 ^ 2 := by
      linear_combination (w03 * w04 ^ 2 * w05 * w12 * w13 ^ 2 * w15 * w23 * w25 * w34) * E6 + (-w03 ^ 2 * w04 ^ 2 * w12 * w13 ^ 2 * w15 * w23 ^ 2 * w34) * E11 + (w03 * w04 ^ 3 * w12 * w13 ^ 2 * w15 * w23 ^ 2 * w24) * E23 + (w03 * w04 ^ 3 * w05 * w12 * w13 ^ 2 * w23 ^ 2 * w24 * w45) * E26 + (w03 * w04 ^ 4 * w05 * w12 * w13 * w23 * w24 * w45 ^ 2) * E34 + (w03 * w04 ^ 3 * w05 * w12 * w13 * w15 * w23 * w24 * w25 * w45 ^ 2) * E42 + (w03 * w04 ^ 2 * w05 * w12 ^ 2 * w13 * w15 * w23 * w24 ^ 2 * w25 * w45 ^ 2) * E42 + (w03 * w04 ^ 2 * w05 * w12 ^ 2 * w15 * w23 * w24 ^ 3 * w25 * w45 ^ 2) * E57
    have hK_t13 : w03 * w04 ^ 2 * w05 * w12 ^ 2 * w15 * w23 * w25 * w34 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n03) (pow_ne_zero 2 n04)) (n05)) (pow_ne_zero 2 n12)) (n15)) (n23)) (n25)) (n34)
    exact mul_right_cancel₀ hK_t13 (by linear_combination hPQ_t13)
  have t25 : w25 ^ 2 * w45 ^ 2 = (1 : ℂ) := by
    have hPQ_t25 : w03 * w04 * w12 ^ 2 * w13 * w14 * w15 * w23 * w24 * w25 ^ 2 * w34 * w45 ^ 2 = w03 * w04 * w12 ^ 2 * w13 * w14 * w15 * w23 * w24 * w34 := by
      linear_combination (-w04 * w12 ^ 2 * w13 * w14 * w15 * w24 * w25 ^ 2 * w34 * w45 ^ 2) * E6 + (-w12 ^ 3 * w13 * w14 * w15 * w24 * w25 ^ 2 * w34 * w45) * E26 + (-w12 ^ 3 * w13 * w14 * w15 * w24 * w25 * w34 * w45) * E34 + (-w12 ^ 3 * w13 ^ 2 * w15 * w23 * w24 * w25 * w45) * E37 + (-w03 * w12 ^ 2 * w13 ^ 2 * w15 * w23 * w25 * w45) * E42 + (w03 * w04 * w12 * w13 * w15 * w23 * w25 * w45) * E57 + (-w03 * w04 * w12 * w13 * w15 * w23 * w24 * w34) * E64
    have hK_t25 : w03 * w04 * w12 ^ 2 * w13 * w14 * w15 * w23 * w24 * w34 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n03) (n04)) (pow_ne_zero 2 n12)) (n13)) (n14)) (n15)) (n23)) (n24)) (n34)
    exact mul_right_cancel₀ hK_t25 (by linear_combination hPQ_t25)
  have qf : w24 ^ 6 * w45 ^ 6 = (1 : ℂ) := by
    have hPQ_tf : w02 * w03 ^ 3 * w04 ^ 5 * w05 ^ 3 * w12 ^ 6 * w13 * w14 ^ 2 * w15 ^ 2 * w23 ^ 3 * w24 ^ 8 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 6 = w02 * w03 ^ 3 * w04 ^ 5 * w05 ^ 3 * w12 ^ 6 * w13 * w14 ^ 2 * w15 ^ 2 * w23 ^ 3 * w24 ^ 2 * w25 ^ 3 * w34 ^ 2 * w35 := by
      linear_combination (-w02 * w03 ^ 3 * w04 ^ 5 * w05 ^ 2 * w12 ^ 6 * w13 * w14 ^ 2 * w15 * w23 ^ 3 * w24 ^ 8 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 6) * E2 + (-w02 ^ 2 * w03 ^ 2 * w04 ^ 5 * w05 ^ 2 * w12 ^ 7 * w13 * w14 ^ 2 * w15 * w23 ^ 2 * w24 ^ 8 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 6) * E6 + (-w02 ^ 2 * w03 * w04 ^ 5 * w05 ^ 2 * w12 ^ 8 * w13 * w14 ^ 2 * w15 * w23 * w24 ^ 8 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 6) * E6 + (-w02 ^ 2 * w04 ^ 5 * w05 ^ 2 * w12 ^ 9 * w13 * w14 ^ 2 * w15 * w24 ^ 8 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 6) * E6 + (w02 ^ 2 * w04 ^ 4 * w05 ^ 2 * w12 ^ 10 * w13 * w14 ^ 2 * w15 * w24 ^ 7 * w25 ^ 3 * w34 ^ 2 * w35 * w45 ^ 6) * E11 + (w02 ^ 2 * w04 ^ 3 * w05 ^ 3 * w12 ^ 10 * w13 * w14 ^ 2 * w15 * w24 ^ 6 * w25 ^ 4 * w34 ^ 2 * w35 * w45 ^ 6) * E11 + (w02 ^ 2 * w04 ^ 2 * w05 ^ 4 * w12 ^ 10 * w13 * w14 ^ 2 * w15 * w24 ^ 5 * w25 ^ 5 * w34 ^ 2 * w35 * w45 ^ 6) * E11 + (-w02 ^ 2 * w04 ^ 2 * w05 ^ 4 * w12 ^ 10 * w13 * w14 ^ 2 * w15 * w24 ^ 5 * w25 ^ 6 * w34 ^ 2 * w35 * w45 ^ 5) * E23 + (-w02 ^ 2 * w03 * w04 * w05 ^ 4 * w12 ^ 10 * w13 * w14 ^ 2 * w15 * w24 ^ 5 * w25 ^ 6 * w34 ^ 3 * w35 * w45 ^ 4) * E26 + (-w02 ^ 2 * w03 * w05 ^ 4 * w12 ^ 10 * w13 * w14 ^ 2 * w15 ^ 2 * w24 ^ 5 * w25 ^ 6 * w34 ^ 3 * w35 * w45 ^ 3) * E26 + (-w02 ^ 2 * w03 * w05 ^ 4 * w12 ^ 10 * w13 * w14 ^ 2 * w15 ^ 2 * w24 ^ 5 * w25 ^ 5 * w34 ^ 3 * w35 * w45 ^ 3) * E34 + (-w02 ^ 2 * w03 * w05 ^ 4 * w12 ^ 10 * w13 ^ 2 * w14 * w15 ^ 2 * w23 * w24 ^ 5 * w25 ^ 5 * w34 ^ 2 * w35 * w45 ^ 3) * E37 + (-w02 ^ 2 * w03 ^ 2 * w05 ^ 4 * w12 ^ 10 * w13 ^ 2 * w15 ^ 2 * w23 * w24 ^ 5 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E37 + (-w02 ^ 2 * w03 ^ 3 * w05 ^ 4 * w12 ^ 9 * w13 ^ 2 * w15 ^ 2 * w23 * w24 ^ 4 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E42 + (-w02 ^ 2 * w03 ^ 3 * w04 * w05 ^ 4 * w12 ^ 8 * w13 ^ 2 * w15 ^ 2 * w23 * w24 ^ 3 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E42 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 7 * w13 ^ 2 * w15 ^ 2 * w23 * w24 ^ 2 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E42 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 3 * w05 ^ 4 * w12 ^ 6 * w13 ^ 2 * w15 ^ 2 * w23 * w24 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E42 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 4 * w05 ^ 4 * w12 ^ 5 * w13 ^ 2 * w15 ^ 2 * w23 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E42 + (w02 ^ 2 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 4 * w13 * w15 ^ 2 * w23 * w25 ^ 5 * w34 * w35 * w45 ^ 3) * E57 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 4 * w13 * w15 ^ 2 * w23 * w24 * w25 ^ 4 * w34 ^ 2 * w35 * w45 ^ 2) * E64 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 5 * w13 * w14 * w15 ^ 2 * w23 * w24 * w25 ^ 3 * w34 ^ 2 * w35 * w45) * E64 + (w02 * w03 ^ 3 * w04 ^ 5 * w05 ^ 3 * w12 ^ 6 * w13 * w14 ^ 2 * w15 ^ 2 * w23 * w24 * w25 ^ 3 * w34 ^ 2 * w35 * w45) * E67 + (-w02 * w03 ^ 3 * w04 ^ 5 * w05 ^ 3 * w12 ^ 6 * w13 * w14 ^ 2 * w15 ^ 2 * w23 ^ 2 * w24 * w25 ^ 3 * w34 ^ 2 * w35) * E77
    have hK_tf : w02 * w03 ^ 3 * w04 ^ 5 * w05 ^ 3 * w12 ^ 6 * w13 * w14 ^ 2 * w15 ^ 2 * w23 ^ 3 * w24 ^ 2 * w25 ^ 3 * w34 ^ 2 * w35 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n02) (pow_ne_zero 3 n03)) (pow_ne_zero 5 n04)) (pow_ne_zero 3 n05)) (pow_ne_zero 6 n12)) (n13)) (pow_ne_zero 2 n14)) (pow_ne_zero 2 n15)) (pow_ne_zero 3 n23)) (pow_ne_zero 2 n24)) (pow_ne_zero 3 n25)) (pow_ne_zero 2 n34)) (n35)
    exact mul_right_cancel₀ hK_tf (by linear_combination hPQ_tf)
  have G23 := pair_relation u2 v2 u3 v3 g23
  have G24 := pair_relation u2 v2 u4 v4 g24
  have G34 := pair_relation u3 v3 u4 v4 g34
  have G35 := pair_relation u3 v3 u5 v5 g35
  have G45 := pair_relation u4 v4 u5 v5 g45
  rcases sq_split (show w13 ^ 2 = (w24 ^ 2 * w45) ^ 2 by linear_combination t13) with h13 | h13
  · rcases sq_split (show (w25 * w45) ^ 2 = (1 : ℂ) ^ 2 by linear_combination t25) with h25 | h25
    · rcases sq_split (show w04 ^ 2 = (w24 ^ 3 * w45 ^ 4) ^ 2 by linear_combination t04) with h04 | h04
      · have x15 : w15 = w24 ^ 3 * w45 ^ 5 := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = w24 ^ 2 * w45 ^ 4 := by
          have hx : w12 * w24 = (w24 ^ 2 * w45 ^ 4) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = w24 ^ 4 * w45 ^ 5 := by
          linear_combination (-1 : ℂ) * w45 * E11 + (-1 : ℂ) * w05 * h25 + (1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = w24 ^ 5 * w45 ^ 6 := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 5 * w45 ^ 6) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E2 + (-1 : ℂ) * w02 * x12 + (1 : ℂ) * w15 * x05 + (1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = w24 ^ 3 * w45 ^ 5 := by
          have hx : w34 * w24 = (w24 ^ 3 * w45 ^ 5) * w24 := by
            linear_combination -E57 + w13 * x12 + (1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = w24 ^ 4 * w45 ^ 2 := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 4 * w45 ^ 2) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E64 + (-1 : ℂ) * w14 * x12 + (1 : ℂ) * h25 + (-1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = w24 * w45 := by
          linear_combination E37 + w34 * x14 + (1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = w24 * w45 ^ 3 := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (w24 * w45 ^ 3) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (1 : ℂ) * E15 + (-1 : ℂ) * w23 * x02 + (1 : ℂ) * w34 * h04 + (1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = w24 ^ 2 * w45 ^ 2 := by
          have hx : w35 * w45 = (w24 ^ 2 * w45 ^ 2) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc1 (by rw [h04, x05]; linear_combination (-1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact nc3 (by rw [x05]; linear_combination (1 * w45 * ((w24 * w45) ^ 3 + (-1) * (w24 * w45) ^ 2 + (w24 * w45) + (-1))) * hf)
        · exact nc2 (by rw [h04]; linear_combination ((1 : ℂ) * w45 * ((w24 * w45) + (-1))) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((118/261*(w24 * w45) + 44/87)*w45^10 + (-155/261*(w24 * w45) - 292/261)*w45^9 + (-43/29*(w24 * w45) + 850/261)*w45^8 + (988/261*(w24 * w45) - 38/29)*w45^7 + (-779/261*(w24 * w45) - 37/261)*w45^6 + (55/261*(w24 * w45) + 307/87)*w45^5 + (586/261*(w24 * w45) + 11/87)*w45^4 + (604/261*(w24 * w45) - 745/261)*w45^3 + (-171/29*(w24 * w45) + 71/87)*w45^2 + (-436/261*(w24 * w45) + 2009/261)*w45 + (326/87*(w24 * w45) - 41/29)) * w45 ^ 3 * G23 + ((250/261*(w24 * w45) - 118/261)*w45^10 + (67/261*(w24 * w45) - 463/261)*w45^9 + (-554/261*(w24 * w45) + 1054/261)*w45^8 + (400/87*(w24 * w45) - 844/261)*w45^7 + (-359/87*(w24 * w45) - 628/261)*w45^6 + (26/261*(w24 * w45) + 1883/261)*w45^5 + (1702/261*(w24 * w45) - 1367/261)*w45^4 + (-8/3*(w24 * w45) - 65/87)*w45^3 + (-4/3*(w24 * w45) + 5/3)*w45^2 + w45 + (w24 * w45)) * w45 ^ 3 * G24 + ((1/3*(w24 * w45) - 2/3)) * w45 ^ 3 * G35 + ((250/261*(w24 * w45)^9 + 44/87*(w24 * w45)^8 - 118/261*(w24 * w45)^7 - 250/261*(w24 * w45)^6 - 44/87*(w24 * w45)^5 + 118/261*(w24 * w45)^4 + 44/87*(w24 * w45)^3)*w45^17 + (67/261*(w24 * w45)^9 - 44/29*(w24 * w45)^8 - 115/87*(w24 * w45)^7 + 61/87*(w24 * w45)^6 + 410/261*(w24 * w45)^5 - 155/261*(w24 * w45)^4 - 292/261*(w24 * w45)^3)*w45^16 + (-554/261*(w24 * w45)^9 + 382/261*(w24 * w45)^8 + 767/261*(w24 * w45)^7 + 25/29*(w24 * w45)^6 - 637/261*(w24 * w45)^5 - 173/87*(w24 * w45)^4 + 968/261*(w24 * w45)^3 + 44/87*(w24 * w45)^2)*w45^15 + (-250/261*(w24 * w45)^10 + 356/87*(w24 * w45)^9 + 293/87*(w24 * w45)^8 - 557/261*(w24 * w45)^7 - 878/261*(w24 * w45)^6 - 1/261*(w24 * w45)^5 + 1162/261*(w24 * w45)^4 - 83/29*(w24 * w45)^3 - 292/261*(w24 * w45)^2)*w45^14 + (-250/261*(w24 * w45)^11 - 199/261*(w24 * w45)^10 - 563/261*(w24 * w45)^9 - 538/261*(w24 * w45)^8 - 805/261*(w24 * w45)^7 + 227/261*(w24 * w45)^6 + 160/87*(w24 * w45)^5 - 1696/261*(w24 * w45)^4 - 595/261*(w24 * w45)^3 + 850/261*(w24 * w45)^2)*w45^13 + (-67/261*(w24 * w45)^11 + 950/261*(w24 * w45)^10 - 11/261*(w24 * w45)^9 - 370/261*(w24 * w45)^8 + 1283/261*(w24 * w45)^7 + 1411/261*(w24 * w45)^6 - 652/261*(w24 * w45)^5 - 1/9*(w24 * w45)^4 + 2113/261*(w24 * w45)^3 - 38/29*(w24 * w45)^2)*w45^12 + (554/261*(w24 * w45)^11 - 1700/261*(w24 * w45)^10 + 542/261*(w24 * w45)^9 + 2803/261*(w24 * w45)^8 + 218/87*(w24 * w45)^7 - 278/29*(w24 * w45)^6 - 730/261*(w24 * w45)^5 + 1387/261*(w24 * w45)^4 - 416/87*(w24 * w45)^3 - 37/261*(w24 * w45)^2)*w45^11 + (-400/87*(w24 * w45)^11 + 721/261*(w24 * w45)^10 + 640/87*(w24 * w45)^9 - 1145/261*(w24 * w45)^8 - 3907/261*(w24 * w45)^7 - 478/261*(w24 * w45)^6 + 425/87*(w24 * w45)^5 - 2050/261*(w24 * w45)^4 - 427/87*(w24 * w45)^3 + 307/87*(w24 * w45)^2)*w45^10 + (359/87*(w24 * w45)^11 + 1679/261*(w24 * w45)^10 - 2183/261*(w24 * w45)^9 - 1733/261*(w24 * w45)^8 + 3425/261*(w24 * w45)^7 + 3704/261*(w24 * w45)^6 - 329/87*(w24 * w45)^5 - 1267/261*(w24 * w45)^4 + 587/87*(w24 * w45)^3 + 11/87*(w24 * w45)^2)*w45^9 + (-26/261*(w24 * w45)^11 - 3611/261*(w24 * w45)^10 - 1018/261*(w24 * w45)^9 + 677/87*(w24 * w45)^8 + 809/261*(w24 * w45)^7 - 2620/261*(w24 * w45)^6 - 299/261*(w24 * w45)^5 + 212/29*(w24 * w45)^4 + 1213/261*(w24 * w45)^3 - 745/261*(w24 * w45)^2)*w45^8 + (-1702/261*(w24 * w45)^11 + 361/261*(w24 * w45)^10 + 1442/261*(w24 * w45)^9 + 1322/261*(w24 * w45)^8 - 134/29*(w24 * w45)^7 + 247/261*(w24 * w45)^6 + 568/261*(w24 * w45)^5 - 1352/261*(w24 * w45)^4 - 1358/261*(w24 * w45)^3 + 71/87*(w24 * w45)^2)*w45^7 + (8/3*(w24 * w45)^11 + 413/87*(w24 * w45)^10 + 134/261*(w24 * w45)^9 + 856/87*(w24 * w45)^8 - 656/261*(w24 * w45)^7 - 61/261*(w24 * w45)^6 - 48/29*(w24 * w45)^5 - 791/261*(w24 * w45)^4 - 214/261*(w24 * w45)^3 + 2009/261*(w24 * w45)^2)*w45^6 + (4/3*(w24 * w45)^11 - 1/3*(w24 * w45)^10 + 1006/261*(w24 * w45)^9 - 1861/261*(w24 * w45)^8 - 89/261*(w24 * w45)^7 - 349/261*(w24 * w45)^6 + 127/261*(w24 * w45)^5 - 682/261*(w24 * w45)^4 - 770/261*(w24 * w45)^3 - 41/29*(w24 * w45)^2)*w45^5 + (-2*(w24 * w45)^10 - 14/3*(w24 * w45)^9 - 326/87*(w24 * w45)^8 + 1111/261*(w24 * w45)^7 - 356/261*(w24 * w45)^6 + 542/261*(w24 * w45)^5 - 1/3*(w24 * w45)^4 + 41/29*(w24 * w45)^3)*w45^4 + (-(w24 * w45)^11 - (w24 * w45)^10 - 4/3*(w24 * w45)^9 + 4/3*(w24 * w45)^8 - 12/29*(w24 * w45)^7 + 128/29*(w24 * w45)^6 + 41/29*(w24 * w45)^5 + 1/3*(w24 * w45)^4 + 2/3*(w24 * w45)^3)*w45^3 + (2*(w24 * w45)^8 + 2*(w24 * w45)^7 - 2*(w24 * w45)^5 - 2/3*(w24 * w45)^4)*w45^2 + ((w24 * w45)^9 + (w24 * w45)^8 - (w24 * w45)^6 - (w24 * w45)^5)*w45 + (-(w24 * w45)^4 - (w24 * w45)^3 + (w24 * w45) + 1)) * hf) one_ne_zero
      · have x15 : w15 = -(w24 ^ 3 * w45 ^ 5) := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = -(w24 ^ 2 * w45 ^ 4) := by
          have hx : w12 * w24 = (-(w24 ^ 2 * w45 ^ 4)) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = -(w24 ^ 4 * w45 ^ 5) := by
          linear_combination (-1 : ℂ) * w45 * E11 + (-1 : ℂ) * w05 * h25 + (1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = -(w24 ^ 5 * w45 ^ 6) := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 5 * w45 ^ 6)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E2 + (1 : ℂ) * w02 * x12 + (-1 : ℂ) * w15 * x05 + (1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = -(w24 ^ 3 * w45 ^ 5) := by
          have hx : w34 * w24 = (-(w24 ^ 3 * w45 ^ 5)) * w24 := by
            linear_combination -E57 + w13 * x12 + (-1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = -(w24 ^ 4 * w45 ^ 2) := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 4 * w45 ^ 2)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E64 + (1 : ℂ) * w14 * x12 + (-1 : ℂ) * h25 + (1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = w24 * w45 := by
          linear_combination E37 + w34 * x14 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = -(w24 * w45 ^ 3) := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (-(w24 * w45 ^ 3)) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (-1 : ℂ) * E15 + (1 : ℂ) * w23 * x02 + (-1 : ℂ) * w34 * h04 + (1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = -(w24 ^ 2 * w45 ^ 2) := by
          have hx : w35 * w45 = (-(w24 ^ 2 * w45 ^ 2)) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc1 (by rw [h04, x05]; linear_combination (1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact nc2 (by rw [h04]; linear_combination (-1 * w45 * ((w24 * w45) ^ 2 + (-1) * (w24 * w45) + 1)) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((125/333*(w24 * w45) + 5/18)*w45^6 + (11/111*(w24 * w45) - 149/222)*w45^5 + (-133/333*(w24 * w45) - 134/333)*w45^4 + (-161/222*(w24 * w45) + 21/37)*w45^3 + (718/333*(w24 * w45) + 569/333)*w45^2 + (83/74*(w24 * w45) + 101/222)*w45 + (-205/666*(w24 * w45) - 1031/666)) * w45 ^ 3 * G23 + ((-145/222*(w24 * w45) - 20/111)*w45^6 + (31/111*(w24 * w45) + 35/111)*w45^5 + (-95/111*(w24 * w45) + 32/111)*w45^4 + (-127/111*(w24 * w45) - 47/222)*w45^3 + w45 - (w24 * w45)) * w45 ^ 3 * G24 + ((145/222*(w24 * w45)^9 - 35/74*(w24 * w45)^8 - 20/111*(w24 * w45)^7 + 145/222*(w24 * w45)^6 - 35/74*(w24 * w45)^5 - 20/111*(w24 * w45)^4 + 5/18*(w24 * w45)^3)*w45^13 + (-31/111*(w24 * w45)^9 - 4/111*(w24 * w45)^8 + 230/333*(w24 * w45)^7 - 251/666*(w24 * w45)^6 - 51/74*(w24 * w45)^5 + 160/111*(w24 * w45)^4 - 149/222*(w24 * w45)^3)*w45^12 + (95/111*(w24 * w45)^9 - 506/333*(w24 * w45)^8 + 191/222*(w24 * w45)^7 + 59/222*(w24 * w45)^6 - 127/222*(w24 * w45)^5 + 65/74*(w24 * w45)^4 - 2/9*(w24 * w45)^3 - 5/18*(w24 * w45)^2)*w45^11 + (-145/222*(w24 * w45)^10 + 359/222*(w24 * w45)^9 - 22/111*(w24 * w45)^8 - 289/333*(w24 * w45)^7 - 5/666*(w24 * w45)^6 + 221/222*(w24 * w45)^5 - 140/333*(w24 * w45)^4 - 277/666*(w24 * w45)^3 + 149/222*(w24 * w45)^2)*w45^10 + (-145/222*(w24 * w45)^11 + 167/222*(w24 * w45)^10 + 8/37*(w24 * w45)^9 - 565/666*(w24 * w45)^8 - 10/333*(w24 * w45)^7 + 35/37*(w24 * w45)^6 - 59/222*(w24 * w45)^5 - 149/222*(w24 * w45)^4 + 211/666*(w24 * w45)^3 + 134/333*(w24 * w45)^2)*w45^9 + (31/111*(w24 * w45)^11 - 91/111*(w24 * w45)^10 + 92/111*(w24 * w45)^9 - 3/37*(w24 * w45)^8 - 169/666*(w24 * w45)^7 + 613/333*(w24 * w45)^6 - 61/37*(w24 * w45)^5 - 649/666*(w24 * w45)^4 + 541/333*(w24 * w45)^3 - 21/37*(w24 * w45)^2)*w45^8 + (-95/111*(w24 * w45)^11 + 110/111*(w24 * w45)^9 - 634/333*(w24 * w45)^8 + 869/333*(w24 * w45)^7 + 323/222*(w24 * w45)^6 - 626/111*(w24 * w45)^5 + 351/74*(w24 * w45)^4 + 164/333*(w24 * w45)^3 - 569/333*(w24 * w45)^2)*w45^7 + (-127/111*(w24 * w45)^11 + 69/74*(w24 * w45)^10 + 109/222*(w24 * w45)^9 - 685/222*(w24 * w45)^8 + 838/333*(w24 * w45)^7 + 256/333*(w24 * w45)^6 - 347/74*(w24 * w45)^5 + 815/333*(w24 * w45)^4 + 997/666*(w24 * w45)^3 - 101/222*(w24 * w45)^2)*w45^6 + (16/111*(w24 * w45)^9 - 461/666*(w24 * w45)^8 + 910/333*(w24 * w45)^7 - 448/111*(w24 * w45)^6 + 22/37*(w24 * w45)^5 + 577/222*(w24 * w45)^4 - 10/3*(w24 * w45)^3 + 1031/666*(w24 * w45)^2)*w45^5 + (-127/111*(w24 * w45)^9 + 143/74*(w24 * w45)^8 + 1/3*(w24 * w45)^7 - 217/74*(w24 * w45)^6 + 238/111*(w24 * w45)^5 + 413/333*(w24 * w45)^4 - 1031/666*(w24 * w45)^3)*w45^4 + (-(w24 * w45)^11 + (w24 * w45)^10 - (w24 * w45)^8 + 1127/666*(w24 * w45)^7 - 143/74*(w24 * w45)^6 + 175/222*(w24 * w45)^5)*w45^3 + (-(w24 * w45)^9 + (w24 * w45)^8 - (w24 * w45)^6 + (w24 * w45)^5)*w45 + (-(w24 * w45)^4 + (w24 * w45)^3 - (w24 * w45) + 1)) * hf) one_ne_zero
        · exact nc2 (by rw [h04]; linear_combination ((-1 : ℂ) * w45 * ((w24 * w45) + (1))) * hf)
    · rcases sq_split (show w04 ^ 2 = (w24 ^ 3 * w45 ^ 4) ^ 2 by linear_combination t04) with h04 | h04
      · have x15 : w15 = w24 ^ 3 * w45 ^ 5 := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = w24 ^ 2 * w45 ^ 4 := by
          have hx : w12 * w24 = (w24 ^ 2 * w45 ^ 4) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = -(w24 ^ 4 * w45 ^ 5) := by
          linear_combination (1 : ℂ) * w45 * E11 + (1 : ℂ) * w05 * h25 + (-1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = -(w24 ^ 5 * w45 ^ 6) := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 5 * w45 ^ 6)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E2 + (-1 : ℂ) * w02 * x12 + (1 : ℂ) * w15 * x05 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = w24 ^ 3 * w45 ^ 5 := by
          have hx : w34 * w24 = (w24 ^ 3 * w45 ^ 5) * w24 := by
            linear_combination -E57 + w13 * x12 + (1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = -(w24 ^ 4 * w45 ^ 2) := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 4 * w45 ^ 2)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E64 + (-1 : ℂ) * w14 * x12 + (1 : ℂ) * h25 + (1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = -(w24 * w45) := by
          linear_combination E37 + w34 * x14 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (-1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = -(w24 * w45 ^ 3) := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (-(w24 * w45 ^ 3)) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (-1 : ℂ) * E15 + (1 : ℂ) * w23 * x02 + (-1 : ℂ) * w34 * h04 + (-1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = -(w24 ^ 2 * w45 ^ 2) := by
          have hx : w35 * w45 = (-(w24 ^ 2 * w45 ^ 2)) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc2 (by rw [h04]; linear_combination (1 * w45 * ((w24 * w45) ^ 2 + (1) * (w24 * w45) + 1)) * hf)
        · exact nc1 (by rw [h04, x05]; linear_combination (1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact nc2 (by rw [h04]; linear_combination ((1 : ℂ) * w45 * ((w24 * w45) + (-1))) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((2/27*(w24 * w45) - 2/27)*w45^10 + (1/54*(w24 * w45) - 1/6)*w45^9 + (4/27*(w24 * w45) + 5/54)*w45^8 + (1/6*(w24 * w45) - 41/54)*w45^7 + (-16/9*(w24 * w45) + 65/54)*w45^6 + (133/54*(w24 * w45) + 14/27)*w45^5 + (5/6*(w24 * w45) - 112/27)*w45^4 + (-35/9*(w24 * w45) + 91/27)*w45^3 + (209/54*(w24 * w45) - 23/27)*w45^2 + (-31/27*(w24 * w45) - 68/27)*w45 + (-65/54*(w24 * w45) + 37/18)) * w45 ^ 3 * G23 + ((-4/27*(w24 * w45) + 2/27)*w45^10 + (-1/27*(w24 * w45) + 13/54)*w45^9 + (7/54*(w24 * w45) - 23/54)*w45^8 + (-23/54*(w24 * w45) + 47/27)*w45^7 + (76/27*(w24 * w45) - 67/54)*w45^6 + (-187/54*(w24 * w45) - 56/27)*w45^5 + (-151/54*(w24 * w45) + 142/27)*w45^4 + (124/27*(w24 * w45) - 38/27)*w45^3 + 1/6*w45^2 + (-1/2*(w24 * w45) + 4/3)*w45 + (-(w24 * w45) - 1/6)) * w45 ^ 3 * G24 + (1/6*(w24 * w45)) * w45 ^ 3 * G34 + ((4/27*(w24 * w45)^9 + 2/27*(w24 * w45)^8 - 2/27*(w24 * w45)^7 - 4/27*(w24 * w45)^6 - 2/27*(w24 * w45)^5 + 2/27*(w24 * w45)^4 + 2/27*(w24 * w45)^3)*w45^17 + (1/27*(w24 * w45)^9 - 11/54*(w24 * w45)^8 - 1/6*(w24 * w45)^7 - 1/27*(w24 * w45)^6 + 1/18*(w24 * w45)^5 + 17/54*(w24 * w45)^4 + 1/6*(w24 * w45)^3)*w45^16 + (-7/54*(w24 * w45)^9 + 10/27*(w24 * w45)^8 + 14/27*(w24 * w45)^7 - 5/54*(w24 * w45)^6 - 13/27*(w24 * w45)^5 - 7/27*(w24 * w45)^4 - 1/6*(w24 * w45)^3 - 2/27*(w24 * w45)^2)*w45^15 + (4/27*(w24 * w45)^10 + 1/2*(w24 * w45)^9 - 11/9*(w24 * w45)^8 - 97/54*(w24 * w45)^7 - 35/54*(w24 * w45)^6 + 28/27*(w24 * w45)^5 + 31/27*(w24 * w45)^4 + 4/9*(w24 * w45)^3 - 1/6*(w24 * w45)^2)*w45^14 + (4/27*(w24 * w45)^11 + 1/9*(w24 * w45)^10 - 167/54*(w24 * w45)^9 - 16/9*(w24 * w45)^8 + 38/27*(w24 * w45)^7 + 68/27*(w24 * w45)^6 + 20/27*(w24 * w45)^5 - 1/9*(w24 * w45)^4 - 43/54*(w24 * w45)^3 + 5/54*(w24 * w45)^2)*w45^13 + (1/27*(w24 * w45)^11 - 1/3*(w24 * w45)^10 + 95/27*(w24 * w45)^9 + 157/27*(w24 * w45)^8 + 11/27*(w24 * w45)^7 - 130/27*(w24 * w45)^6 - 26/9*(w24 * w45)^5 - 101/27*(w24 * w45)^4 - 119/54*(w24 * w45)^3 - 41/54*(w24 * w45)^2)*w45^12 + (-7/54*(w24 * w45)^11 + 13/18*(w24 * w45)^10 + 95/54*(w24 * w45)^9 - 299/54*(w24 * w45)^8 - 127/18*(w24 * w45)^7 - 1/27*(w24 * w45)^6 + 16/9*(w24 * w45)^5 + 146/27*(w24 * w45)^4 + 311/54*(w24 * w45)^3 + 65/54*(w24 * w45)^2)*w45^11 + (23/54*(w24 * w45)^11 - 223/54*(w24 * w45)^10 - 143/18*(w24 * w45)^9 - 43/18*(w24 * w45)^8 + 541/54*(w24 * w45)^7 + 253/27*(w24 * w45)^6 + 125/54*(w24 * w45)^5 + 16/3*(w24 * w45)^4 + 5/54*(w24 * w45)^3 + 14/27*(w24 * w45)^2)*w45^10 + (-76/27*(w24 * w45)^11 + 17/9*(w24 * w45)^10 + 373/54*(w24 * w45)^9 + 224/27*(w24 * w45)^8 - 2/9*(w24 * w45)^7 - 157/18*(w24 * w45)^6 - 11/54*(w24 * w45)^5 - 76/9*(w24 * w45)^4 - 49/6*(w24 * w45)^3 - 112/27*(w24 * w45)^2)*w45^9 + (187/54*(w24 * w45)^11 + 25/3*(w24 * w45)^10 - 17/54*(w24 * w45)^9 - 176/27*(w24 * w45)^8 - 319/27*(w24 * w45)^7 - 311/54*(w24 * w45)^6 - 115/18*(w24 * w45)^5 - 31/27*(w24 * w45)^4 + 175/27*(w24 * w45)^3 + 91/27*(w24 * w45)^2)*w45^8 + (151/54*(w24 * w45)^11 - 127/18*(w24 * w45)^10 - 125/27*(w24 * w45)^9 - 17/6*(w24 * w45)^8 + 13/6*(w24 * w45)^7 + 89/18*(w24 * w45)^6 + 95/18*(w24 * w45)^5 + 643/54*(w24 * w45)^4 + 56/27*(w24 * w45)^3 - 23/27*(w24 * w45)^2)*w45^7 + (-124/27*(w24 * w45)^11 - 86/27*(w24 * w45)^10 - 20/9*(w24 * w45)^9 - 91/18*(w24 * w45)^8 + 23/18*(w24 * w45)^7 + 115/18*(w24 * w45)^6 + 443/54*(w24 * w45)^5 - 82/27*(w24 * w45)^4 - 371/54*(w24 * w45)^3 - 68/27*(w24 * w45)^2)*w45^6 + (1/3*(w24 * w45)^10 - 205/54*(w24 * w45)^9 + 271/54*(w24 * w45)^8 + 26/9*(w24 * w45)^7 - 167/54*(w24 * w45)^6 - 223/54*(w24 * w45)^5 - 163/54*(w24 * w45)^4 + 31/18*(w24 * w45)^3 + 37/18*(w24 * w45)^2)*w45^5 + (1/2*(w24 * w45)^11 + 1/6*(w24 * w45)^10 + 239/54*(w24 * w45)^9 + 104/27*(w24 * w45)^8 + 49/54*(w24 * w45)^7 + 13/18*(w24 * w45)^6 + 11/6*(w24 * w45)^5 + 55/54*(w24 * w45)^4 + 17/9*(w24 * w45)^3)*w45^4 + ((w24 * w45)^11 + 7/6*(w24 * w45)^10 + 1/6*(w24 * w45)^9 - 4/3*(w24 * w45)^8 + 65/54*(w24 * w45)^7 + 50/27*(w24 * w45)^6 - 139/54*(w24 * w45)^5 - 1/6*(w24 * w45)^4)*w45^3 + (-1/2*(w24 * w45)^9 - 1/6*(w24 * w45)^8 + 1/6*(w24 * w45)^6 + 1/6*(w24 * w45)^5)*w45^2 + (-(w24 * w45)^9 - 4/3*(w24 * w45)^8 - 1/3*(w24 * w45)^7 + (w24 * w45)^6 + 4/3*(w24 * w45)^5)*w45 + (-1/6*(w24 * w45)^6 - 1/6*(w24 * w45)^5 - (w24 * w45)^4 - (w24 * w45)^3 + (w24 * w45) + 1)) * hf) one_ne_zero
      · have x15 : w15 = -(w24 ^ 3 * w45 ^ 5) := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = -(w24 ^ 2 * w45 ^ 4) := by
          have hx : w12 * w24 = (-(w24 ^ 2 * w45 ^ 4)) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = w24 ^ 4 * w45 ^ 5 := by
          linear_combination (1 : ℂ) * w45 * E11 + (1 : ℂ) * w05 * h25 + (-1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = w24 ^ 5 * w45 ^ 6 := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 5 * w45 ^ 6) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E2 + (1 : ℂ) * w02 * x12 + (-1 : ℂ) * w15 * x05 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = -(w24 ^ 3 * w45 ^ 5) := by
          have hx : w34 * w24 = (-(w24 ^ 3 * w45 ^ 5)) * w24 := by
            linear_combination -E57 + w13 * x12 + (-1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = w24 ^ 4 * w45 ^ 2 := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 4 * w45 ^ 2) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E64 + (1 : ℂ) * w14 * x12 + (-1 : ℂ) * h25 + (-1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = -(w24 * w45) := by
          linear_combination E37 + w34 * x14 + (1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (-1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = w24 * w45 ^ 3 := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (w24 * w45 ^ 3) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (1 : ℂ) * E15 + (-1 : ℂ) * w23 * x02 + (1 : ℂ) * w34 * h04 + (-1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = w24 ^ 2 * w45 ^ 2 := by
          have hx : w35 * w45 = (w24 ^ 2 * w45 ^ 2) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc3 (by rw [x05]; linear_combination (1 * w45 * ((w24 * w45) ^ 3 + (1) * (w24 * w45) ^ 2 + (w24 * w45) + (1))) * hf)
        · exact nc1 (by rw [h04, x05]; linear_combination (-1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((-32/15*(w24 * w45) + 3/10)*w45^6 + (-19/15*(w24 * w45) - 23/30)*w45^5 + (4/15*(w24 * w45) + 14/5)*w45^4 + (127/30*(w24 * w45) + 34/15)*w45^3 + (23/15*(w24 * w45) - 13/5)*w45^2 + (-29/10*(w24 * w45) - 107/30)*w45 + (-89/30*(w24 * w45) + 13/10)) * w45 ^ 3 * G23 + ((-73/30*(w24 * w45) - 32/15)*w45^6 + (-44/15*(w24 * w45) - 17/5)*w45^5 + (-3/5*(w24 * w45) + 17/15)*w45^4 + (-19/15*(w24 * w45) - 119/30)*w45^3 + (-2*(w24 * w45) - 2)*w45^2 + w45 + (w24 * w45)) * w45 ^ 3 * G24 + ((-73/30*(w24 * w45)^9 + 3/10*(w24 * w45)^8 + 32/15*(w24 * w45)^7 - 73/30*(w24 * w45)^6 + 3/10*(w24 * w45)^5 + 32/15*(w24 * w45)^4 - 3/10*(w24 * w45)^3)*w45^13 + (-44/15*(w24 * w45)^9 - 7/15*(w24 * w45)^8 + 19/15*(w24 * w45)^7 - 1/2*(w24 * w45)^6 + 41/30*(w24 * w45)^5 + 19/15*(w24 * w45)^4 + 23/30*(w24 * w45)^3)*w45^12 + (-3/5*(w24 * w45)^9 - 2/5*(w24 * w45)^8 - 21/10*(w24 * w45)^7 + 61/30*(w24 * w45)^6 + 113/30*(w24 * w45)^5 + 1/30*(w24 * w45)^4 - 2/3*(w24 * w45)^3 - 3/10*(w24 * w45)^2)*w45^11 + (-73/30*(w24 * w45)^10 - 29/30*(w24 * w45)^9 - 64/15*(w24 * w45)^8 + 4/3*(w24 * w45)^7 + 149/30*(w24 * w45)^6 - 109/30*(w24 * w45)^5 - 34/15*(w24 * w45)^4 + 5/6*(w24 * w45)^3 + 23/30*(w24 * w45)^2)*w45^10 + (-73/30*(w24 * w45)^11 - 79/30*(w24 * w45)^10 - 1/3*(w24 * w45)^9 - 17/10*(w24 * w45)^8 + 19/5*(w24 * w45)^7 + 17/15*(w24 * w45)^6 - 35/6*(w24 * w45)^5 + 103/30*(w24 * w45)^4 + 13/2*(w24 * w45)^3 - 14/5*(w24 * w45)^2)*w45^9 + (-44/15*(w24 * w45)^11 - 16/15*(w24 * w45)^10 + 77/15*(w24 * w45)^9 - 28/15*(w24 * w45)^8 + 5/2*(w24 * w45)^7 - 3*(w24 * w45)^6 + 12/5*(w24 * w45)^5 + 77/6*(w24 * w45)^4 - 23/5*(w24 * w45)^3 - 34/15*(w24 * w45)^2)*w45^8 + (-3/5*(w24 * w45)^11 + 7/15*(w24 * w45)^10 - 79/15*(w24 * w45)^9 - 29/5*(w24 * w45)^7 + 27/10*(w24 * w45)^6 + 57/5*(w24 * w45)^5 - 163/30*(w24 * w45)^4 - 17/15*(w24 * w45)^3 + 13/5*(w24 * w45)^2)*w45^7 + (-19/15*(w24 * w45)^11 - 47/10*(w24 * w45)^10 + 31/30*(w24 * w45)^9 - 157/30*(w24 * w45)^8 - 28/15*(w24 * w45)^7 + 34/3*(w24 * w45)^6 - 89/30*(w24 * w45)^5 - 56/15*(w24 * w45)^4 + 15/2*(w24 * w45)^3 + 107/30*(w24 * w45)^2)*w45^6 + (-2*(w24 * w45)^11 + 12/5*(w24 * w45)^9 - 11/2*(w24 * w45)^8 + 86/15*(w24 * w45)^6 - 22/3*(w24 * w45)^5 + 109/30*(w24 * w45)^4 + 83/15*(w24 * w45)^3 - 13/10*(w24 * w45)^2)*w45^5 + (2*(w24 * w45)^10 - 49/15*(w24 * w45)^9 - 37/10*(w24 * w45)^8 + 31/15*(w24 * w45)^7 - 29/6*(w24 * w45)^6 - 4/5*(w24 * w45)^5 + 34/15*(w24 * w45)^4 - 13/10*(w24 * w45)^3)*w45^4 + ((w24 * w45)^11 - (w24 * w45)^10 - 2*(w24 * w45)^9 + (w24 * w45)^8 - 29/30*(w24 * w45)^7 - 17/10*(w24 * w45)^6 + 89/30*(w24 * w45)^5)*w45^3 + (2*(w24 * w45)^8 - 2*(w24 * w45)^7 + 2*(w24 * w45)^5)*w45^2 + ((w24 * w45)^9 - (w24 * w45)^8 + (w24 * w45)^6 - (w24 * w45)^5)*w45 + (-(w24 * w45)^4 + (w24 * w45)^3 - (w24 * w45) + 1)) * hf) one_ne_zero
        · exact nc2 (by rw [h04]; linear_combination ((-1 : ℂ) * w45 * ((w24 * w45) + (1))) * hf)
  · rcases sq_split (show (w25 * w45) ^ 2 = (1 : ℂ) ^ 2 by linear_combination t25) with h25 | h25
    · rcases sq_split (show w04 ^ 2 = (w24 ^ 3 * w45 ^ 4) ^ 2 by linear_combination t04) with h04 | h04
      · have x15 : w15 = w24 ^ 3 * w45 ^ 5 := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = w24 ^ 2 * w45 ^ 4 := by
          have hx : w12 * w24 = (w24 ^ 2 * w45 ^ 4) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = w24 ^ 4 * w45 ^ 5 := by
          linear_combination (-1 : ℂ) * w45 * E11 + (-1 : ℂ) * w05 * h25 + (1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = w24 ^ 5 * w45 ^ 6 := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 5 * w45 ^ 6) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E2 + (-1 : ℂ) * w02 * x12 + (1 : ℂ) * w15 * x05 + (1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = -(w24 ^ 3 * w45 ^ 5) := by
          have hx : w34 * w24 = (-(w24 ^ 3 * w45 ^ 5)) * w24 := by
            linear_combination -E57 + w13 * x12 + (1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = w24 ^ 4 * w45 ^ 2 := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 4 * w45 ^ 2) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E64 + (-1 : ℂ) * w14 * x12 + (1 : ℂ) * h25 + (-1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = -(w24 * w45) := by
          linear_combination E37 + w34 * x14 + (1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (-1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = -(w24 * w45 ^ 3) := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (-(w24 * w45 ^ 3)) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (1 : ℂ) * E15 + (-1 : ℂ) * w23 * x02 + (1 : ℂ) * w34 * h04 + (1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = -(w24 ^ 2 * w45 ^ 2) := by
          have hx : w35 * w45 = (-(w24 ^ 2 * w45 ^ 2)) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc1 (by rw [h04, x05]; linear_combination (-1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact nc3 (by rw [x05]; linear_combination (1 * w45 * ((w24 * w45) ^ 3 + (-1) * (w24 * w45) ^ 2 + (w24 * w45) + (-1))) * hf)
        · exact nc2 (by rw [h04]; linear_combination ((1 : ℂ) * w45 * ((w24 * w45) + (-1))) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((160/513*(w24 * w45) - 170/513)*w45^10 + (505/513*(w24 * w45) + 496/513)*w45^9 + (-463/171*(w24 * w45) + 644/171)*w45^8 + (-2422/513*(w24 * w45) + 1412/513)*w45^7 + (-3863/513*(w24 * w45) + 769/513)*w45^6 + (-2647/513*(w24 * w45) - 2209/513)*w45^5 + (-82/57*(w24 * w45) - 1351/171)*w45^4 + (2644/513*(w24 * w45) - 5363/513)*w45^3 + (3589/513*(w24 * w45) - 3797/513)*w45^2 + (1214/171*(w24 * w45) - 925/171)*w45 + (650/171*(w24 * w45) - 13/9)) * w45 ^ 3 * G23 + ((110/171*(w24 * w45) - 20/57)*w45^10 + (113/171*(w24 * w45) + 439/171)*w45^9 + (-1234/171*(w24 * w45) + 56/9)*w45^8 + (-94/19*(w24 * w45) - 70/19)*w45^7 + (211/171*(w24 * w45) - 328/57)*w45^6 + (830/171*(w24 * w45) - 473/57)*w45^5 + (160/19*(w24 * w45) - 179/57)*w45^4 + (52/57*(w24 * w45) + 185/57)*w45^3 + (-2*(w24 * w45) + 7/3)*w45^2 + w45 + (w24 * w45)) * w45 ^ 3 * G24 + (1/3*(w24 * w45)) * w45 ^ 3 * G35 + ((110/171*(w24 * w45)^9 + 50/171*(w24 * w45)^8 - 20/57*(w24 * w45)^7 - 110/171*(w24 * w45)^6 - 50/171*(w24 * w45)^5 + 20/57*(w24 * w45)^4 + 170/513*(w24 * w45)^3)*w45^17 + (113/171*(w24 * w45)^9 + 184/57*(w24 * w45)^8 + 1157/513*(w24 * w45)^7 - 329/513*(w24 * w45)^6 - 442/171*(w24 * w45)^5 - 499/171*(w24 * w45)^4 - 496/513*(w24 * w45)^3)*w45^16 + (-1234/171*(w24 * w45)^9 - 350/513*(w24 * w45)^8 + 2837/513*(w24 * w45)^7 + 2521/513*(w24 * w45)^6 - 47/171*(w24 * w45)^5 - 775/171*(w24 * w45)^4 - 704/171*(w24 * w45)^3 - 170/513*(w24 * w45)^2)*w45^15 + (-110/171*(w24 * w45)^10 - 896/171*(w24 * w45)^9 - 3413/513*(w24 * w45)^8 + 55/19*(w24 * w45)^7 + 1154/171*(w24 * w45)^6 + 83/171*(w24 * w45)^5 + 1264/513*(w24 * w45)^4 + 25/171*(w24 * w45)^3 + 496/513*(w24 * w45)^2)*w45^14 + (-110/171*(w24 * w45)^11 - 163/171*(w24 * w45)^10 - 281/171*(w24 * w45)^9 - 484/57*(w24 * w45)^8 + 203/171*(w24 * w45)^7 + 5495/513*(w24 * w45)^6 + 2002/171*(w24 * w45)^5 + 1954/513*(w24 * w45)^4 + 133/27*(w24 * w45)^3 + 644/171*(w24 * w45)^2)*w45^13 + (-113/171*(w24 * w45)^11 + 682/171*(w24 * w45)^10 + 187/57*(w24 * w45)^9 - 10414/513*(w24 * w45)^8 - 6737/513*(w24 * w45)^7 + 3319/513*(w24 * w45)^6 + 2632/171*(w24 * w45)^5 + 433/57*(w24 * w45)^4 + 3871/513*(w24 * w45)^3 + 1412/513*(w24 * w45)^2)*w45^12 + (1234/171*(w24 * w45)^11 + 1016/171*(w24 * w45)^10 + 218/19*(w24 * w45)^9 - 5015/513*(w24 * w45)^8 - 10532/513*(w24 * w45)^7 - 3082/513*(w24 * w45)^6 + 220/19*(w24 * w45)^5 + 1661/513*(w24 * w45)^4 - 1574/513*(w24 * w45)^3 + 769/513*(w24 * w45)^2)*w45^11 + (94/19*(w24 * w45)^11 + 1265/171*(w24 * w45)^10 + 88/9*(w24 * w45)^9 - 1513/513*(w24 * w45)^8 - 7985/513*(w24 * w45)^7 - 134/19*(w24 * w45)^6 + 755/171*(w24 * w45)^5 - 536/513*(w24 * w45)^4 - 5423/513*(w24 * w45)^3 - 2209/513*(w24 * w45)^2)*w45^10 + (-211/171*(w24 * w45)^11 - 1/3*(w24 * w45)^10 - 1/57*(w24 * w45)^9 + 1255/171*(w24 * w45)^8 - 5945/513*(w24 * w45)^7 - 5306/513*(w24 * w45)^6 - 271/57*(w24 * w45)^5 - 73/27*(w24 * w45)^4 - 2365/171*(w24 * w45)^3 - 1351/171*(w24 * w45)^2)*w45^9 + (-830/171*(w24 * w45)^11 - 851/171*(w24 * w45)^10 - 110/57*(w24 * w45)^9 + 7783/513*(w24 * w45)^8 + 61/57*(w24 * w45)^7 - 3944/513*(w24 * w45)^6 - 29/9*(w24 * w45)^5 + 188/19*(w24 * w45)^4 - 955/171*(w24 * w45)^3 - 5363/513*(w24 * w45)^2)*w45^8 + (-160/19*(w24 * w45)^11 - 353/57*(w24 * w45)^10 + 208/171*(w24 * w45)^9 + 7396/513*(w24 * w45)^8 + 356/171*(w24 * w45)^7 - 853/171*(w24 * w45)^6 + 86/57*(w24 * w45)^5 + 6154/513*(w24 * w45)^4 + 3764/513*(w24 * w45)^3 - 3797/513*(w24 * w45)^2)*w45^7 + (-52/57*(w24 * w45)^11 - 41/19*(w24 * w45)^10 + 218/171*(w24 * w45)^9 + 1480/171*(w24 * w45)^8 - 184/513*(w24 * w45)^7 - 1313/171*(w24 * w45)^6 + 1030/171*(w24 * w45)^5 + 6553/513*(w24 * w45)^4 + 3086/513*(w24 * w45)^3 - 925/171*(w24 * w45)^2)*w45^6 + (2*(w24 * w45)^11 - 1/3*(w24 * w45)^10 + 290/57*(w24 * w45)^9 + 1139/171*(w24 * w45)^8 + 605/513*(w24 * w45)^7 - 1115/171*(w24 * w45)^6 + 59/57*(w24 * w45)^5 + 1334/171*(w24 * w45)^4 + 1252/171*(w24 * w45)^3 - 13/9*(w24 * w45)^2)*w45^5 + (-2*(w24 * w45)^10 - 62/57*(w24 * w45)^9 + 60/19*(w24 * w45)^8 - 89/171*(w24 * w45)^7 - 102/19*(w24 * w45)^6 - 2/19*(w24 * w45)^5 - 61/171*(w24 * w45)^4 + 13/9*(w24 * w45)^3)*w45^4 + (-(w24 * w45)^11 - (w24 * w45)^10 - 2*(w24 * w45)^9 + 4/3*(w24 * w45)^8 + 34/171*(w24 * w45)^7 - 60/19*(w24 * w45)^6 - 49/19*(w24 * w45)^5 - 1/3*(w24 * w45)^4)*w45^3 + (2*(w24 * w45)^8 + 2*(w24 * w45)^7 - 2*(w24 * w45)^5)*w45^2 + ((w24 * w45)^9 + (w24 * w45)^8 - (w24 * w45)^6 - (w24 * w45)^5)*w45 + (-(w24 * w45)^4 - (w24 * w45)^3 + (w24 * w45) + 1)) * hf) one_ne_zero
      · have x15 : w15 = -(w24 ^ 3 * w45 ^ 5) := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = -(w24 ^ 2 * w45 ^ 4) := by
          have hx : w12 * w24 = (-(w24 ^ 2 * w45 ^ 4)) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = -(w24 ^ 4 * w45 ^ 5) := by
          linear_combination (-1 : ℂ) * w45 * E11 + (-1 : ℂ) * w05 * h25 + (1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = -(w24 ^ 5 * w45 ^ 6) := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 5 * w45 ^ 6)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E2 + (1 : ℂ) * w02 * x12 + (-1 : ℂ) * w15 * x05 + (1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = w24 ^ 3 * w45 ^ 5 := by
          have hx : w34 * w24 = (w24 ^ 3 * w45 ^ 5) * w24 := by
            linear_combination -E57 + w13 * x12 + (-1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = -(w24 ^ 4 * w45 ^ 2) := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 4 * w45 ^ 2)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E64 + (1 : ℂ) * w14 * x12 + (-1 : ℂ) * h25 + (1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = -(w24 * w45) := by
          linear_combination E37 + w34 * x14 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (-1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = w24 * w45 ^ 3 := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (w24 * w45 ^ 3) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (-1 : ℂ) * E15 + (1 : ℂ) * w23 * x02 + (-1 : ℂ) * w34 * h04 + (1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = w24 ^ 2 * w45 ^ 2 := by
          have hx : w35 * w45 = (w24 ^ 2 * w45 ^ 2) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc1 (by rw [h04, x05]; linear_combination (1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact nc2 (by rw [h04]; linear_combination (-1 * w45 * ((w24 * w45) ^ 2 + (-1) * (w24 * w45) + 1)) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((11/69*(w24 * w45) + 197/138)*w45^6 + (12/23*(w24 * w45) - 5/138)*w45^5 + (-11/23*(w24 * w45) - 15/23)*w45^4 + (-545/138*(w24 * w45) - 188/69)*w45^3 + (151/69*(w24 * w45) + 104/69)*w45^2 + (47/46*(w24 * w45) + 491/138)*w45 + (-77/46*(w24 * w45) - 43/46)) * w45 ^ 3 * G23 + ((175/138*(w24 * w45) - 11/69)*w45^6 + (-42/23*(w24 * w45) - 25/69)*w45^5 + (-83/69*(w24 * w45) - 39/23)*w45^4 + (-52/23*(w24 * w45) - 61/46)*w45^3 + w45 - (w24 * w45)) * w45 ^ 3 * G24 + ((-175/138*(w24 * w45)^9 + 197/138*(w24 * w45)^8 - 11/69*(w24 * w45)^7 - 175/138*(w24 * w45)^6 + 197/138*(w24 * w45)^5 - 11/69*(w24 * w45)^4 - 197/138*(w24 * w45)^3)*w45^13 + (42/23*(w24 * w45)^9 - 101/69*(w24 * w45)^8 - 12/23*(w24 * w45)^7 + 77/138*(w24 * w45)^6 + 17/138*(w24 * w45)^5 - 12/23*(w24 * w45)^4 + 5/138*(w24 * w45)^3)*w45^12 + (83/69*(w24 * w45)^9 + 15/23*(w24 * w45)^8 - 109/138*(w24 * w45)^7 + 221/138*(w24 * w45)^6 - 215/138*(w24 * w45)^5 + 263/138*(w24 * w45)^4 + 34/69*(w24 * w45)^3 - 197/138*(w24 * w45)^2)*w45^11 + (175/138*(w24 * w45)^10 + 5/6*(w24 * w45)^9 - 35/23*(w24 * w45)^8 + 125/69*(w24 * w45)^7 + 15/46*(w24 * w45)^6 - 109/138*(w24 * w45)^5 + 28/23*(w24 * w45)^4 + 523/138*(w24 * w45)^3 + 5/138*(w24 * w45)^2)*w45^10 + (175/138*(w24 * w45)^11 - 449/138*(w24 * w45)^10 + 112/69*(w24 * w45)^9 + 137/46*(w24 * w45)^8 - 29/23*(w24 * w45)^7 + 134/69*(w24 * w45)^6 - 101/138*(w24 * w45)^5 - 91/138*(w24 * w45)^4 - 97/138*(w24 * w45)^3 + 15/23*(w24 * w45)^2)*w45^9 + (-42/23*(w24 * w45)^11 + 6/23*(w24 * w45)^10 - 3/23*(w24 * w45)^9 - 60/23*(w24 * w45)^8 - 187/46*(w24 * w45)^7 + 202/69*(w24 * w45)^6 + 257/69*(w24 * w45)^5 - 511/138*(w24 * w45)^4 + 33/23*(w24 * w45)^3 + 188/69*(w24 * w45)^2)*w45^8 + (-83/69*(w24 * w45)^11 - 190/69*(w24 * w45)^10 + 338/69*(w24 * w45)^9 + 22/69*(w24 * w45)^8 - 142/69*(w24 * w45)^7 - 199/138*(w24 * w45)^6 + 8/3*(w24 * w45)^5 + 211/46*(w24 * w45)^4 - 61/23*(w24 * w45)^3 - 104/69*(w24 * w45)^2)*w45^7 + (-52/23*(w24 * w45)^11 + 43/46*(w24 * w45)^10 - 1/2*(w24 * w45)^9 - 45/46*(w24 * w45)^8 + 48/23*(w24 * w45)^7 - 227/69*(w24 * w45)^6 - 251/46*(w24 * w45)^5 + 128/23*(w24 * w45)^4 + 67/138*(w24 * w45)^3 - 491/138*(w24 * w45)^2)*w45^6 + (-14/69*(w24 * w45)^9 - 749/138*(w24 * w45)^8 + 199/69*(w24 * w45)^7 + 122/23*(w24 * w45)^6 - 392/69*(w24 * w45)^5 - 341/138*(w24 * w45)^4 + 292/69*(w24 * w45)^3 + 43/46*(w24 * w45)^2)*w45^5 + (-52/23*(w24 * w45)^9 + 89/46*(w24 * w45)^8 + 31/23*(w24 * w45)^7 + 179/138*(w24 * w45)^6 + 21/23*(w24 * w45)^5 - 17/23*(w24 * w45)^4 - 43/46*(w24 * w45)^3)*w45^4 + (-(w24 * w45)^11 + (w24 * w45)^10 - (w24 * w45)^8 + 15/46*(w24 * w45)^7 - 89/46*(w24 * w45)^6 - 15/46*(w24 * w45)^5)*w45^3 + (-(w24 * w45)^9 + (w24 * w45)^8 - (w24 * w45)^6 + (w24 * w45)^5)*w45 + (-(w24 * w45)^4 + (w24 * w45)^3 - (w24 * w45) + 1)) * hf) one_ne_zero
        · exact nc2 (by rw [h04]; linear_combination ((-1 : ℂ) * w45 * ((w24 * w45) + (1))) * hf)
    · rcases sq_split (show w04 ^ 2 = (w24 ^ 3 * w45 ^ 4) ^ 2 by linear_combination t04) with h04 | h04
      · have x15 : w15 = w24 ^ 3 * w45 ^ 5 := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = w24 ^ 2 * w45 ^ 4 := by
          have hx : w12 * w24 = (w24 ^ 2 * w45 ^ 4) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = -(w24 ^ 4 * w45 ^ 5) := by
          linear_combination (1 : ℂ) * w45 * E11 + (1 : ℂ) * w05 * h25 + (-1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = -(w24 ^ 5 * w45 ^ 6) := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 5 * w45 ^ 6)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E2 + (-1 : ℂ) * w02 * x12 + (1 : ℂ) * w15 * x05 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = -(w24 ^ 3 * w45 ^ 5) := by
          have hx : w34 * w24 = (-(w24 ^ 3 * w45 ^ 5)) * w24 := by
            linear_combination -E57 + w13 * x12 + (1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = -(w24 ^ 4 * w45 ^ 2) := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (-(w24 ^ 4 * w45 ^ 2)) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (1 : ℂ) * E64 + (-1 : ℂ) * w14 * x12 + (1 : ℂ) * h25 + (1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = w24 * w45 := by
          linear_combination E37 + w34 * x14 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = w24 * w45 ^ 3 := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (w24 * w45 ^ 3) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (-1 : ℂ) * E15 + (1 : ℂ) * w23 * x02 + (-1 : ℂ) * w34 * h04 + (-1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = w24 ^ 2 * w45 ^ 2 := by
          have hx : w35 * w45 = (w24 ^ 2 * w45 ^ 2) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc2 (by rw [h04]; linear_combination (1 * w45 * ((w24 * w45) ^ 2 + (1) * (w24 * w45) + 1)) * hf)
        · exact nc1 (by rw [h04, x05]; linear_combination (1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact nc2 (by rw [h04]; linear_combination ((1 : ℂ) * w45 * ((w24 * w45) + (-1))) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((-10/43*(w24 * w45) + 149/387)*w45^10 + (-5/774*(w24 * w45) + 293/774)*w45^9 + (26/129*(w24 * w45) + 275/774)*w45^8 + (-41/258*(w24 * w45) + 1081/774)*w45^7 + (-545/387*(w24 * w45) + 233/258)*w45^6 + (-1003/774*(w24 * w45) - 53/387)*w45^5 + (415/774*(w24 * w45) - 2/9)*w45^4 + (-365/387*(w24 * w45) + 139/129)*w45^3 + (53/774*(w24 * w45) - 139/387)*w45^2 + (814/387*(w24 * w45) - 32/129)*w45 + (-39/86*(w24 * w45) + 1723/774)) * w45 ^ 3 * G23 + ((-59/387*(w24 * w45) - 10/43)*w45^10 + (71/129*(w24 * w45) - 61/774)*w45^9 + (325/774*(w24 * w45) - 595/774)*w45^8 + (-29/774*(w24 * w45) - 131/129)*w45^7 + (1381/387*(w24 * w45) - 2363/774)*w45^6 + (2513/774*(w24 * w45) + 88/129)*w45^5 + (-637/774*(w24 * w45) + 2003/387)*w45^4 + (-428/387*(w24 * w45) + 92/129)*w45^3 + (-1/3*(w24 * w45) + 1/6)*w45^2 + (1/6*(w24 * w45) + 2/3)*w45 + (-4/3*(w24 * w45) + 1/6)) * w45 ^ 3 * G24 + ((1/6*(w24 * w45) - 1/3)) * w45 ^ 3 * G34 + ((59/387*(w24 * w45)^9 + 149/387*(w24 * w45)^8 + 10/43*(w24 * w45)^7 - 59/387*(w24 * w45)^6 - 149/387*(w24 * w45)^5 - 10/43*(w24 * w45)^4 + 149/387*(w24 * w45)^3)*w45^17 + (-71/129*(w24 * w45)^9 - 365/774*(w24 * w45)^8 + 241/774*(w24 * w45)^7 + 154/387*(w24 * w45)^6 - 113/774*(w24 * w45)^5 - 5/774*(w24 * w45)^4 + 293/774*(w24 * w45)^3)*w45^16 + (-325/774*(w24 * w45)^9 + 25/43*(w24 * w45)^8 + 151/387*(w24 * w45)^7 - 143/774*(w24 * w45)^6 - 166/387*(w24 * w45)^5 - 71/387*(w24 * w45)^4 + 95/774*(w24 * w45)^3 + 149/387*(w24 * w45)^2)*w45^15 + (59/387*(w24 * w45)^10 + 109/258*(w24 * w45)^9 + 13/9*(w24 * w45)^8 + 517/774*(w24 * w45)^7 - 583/774*(w24 * w45)^6 - 685/387*(w24 * w45)^5 - 298/387*(w24 * w45)^4 + 199/129*(w24 * w45)^3 + 293/774*(w24 * w45)^2)*w45^14 + (59/387*(w24 * w45)^11 - 64/387*(w24 * w45)^10 - 2947/774*(w24 * w45)^9 - 173/129*(w24 * w45)^8 + 359/129*(w24 * w45)^7 + 106/43*(w24 * w45)^6 - 257/387*(w24 * w45)^5 - 446/387*(w24 * w45)^4 + 1087/774*(w24 * w45)^3 + 275/774*(w24 * w45)^2)*w45^13 + (-71/129*(w24 * w45)^11 - 115/129*(w24 * w45)^10 - 1091/387*(w24 * w45)^9 - 130/43*(w24 * w45)^8 + 74/387*(w24 * w45)^7 + 1286/387*(w24 * w45)^6 + 347/129*(w24 * w45)^5 - 992/387*(w24 * w45)^4 - 61/86*(w24 * w45)^3 + 1081/774*(w24 * w45)^2)*w45^12 + (-325/774*(w24 * w45)^11 + 299/774*(w24 * w45)^10 + 643/258*(w24 * w45)^9 - 337/258*(w24 * w45)^8 - 3157/774*(w24 * w45)^7 - 730/387*(w24 * w45)^6 - 734/387*(w24 * w45)^5 - 368/387*(w24 * w45)^4 - 967/774*(w24 * w45)^3 + 233/258*(w24 * w45)^2)*w45^11 + (29/774*(w24 * w45)^11 - 649/258*(w24 * w45)^10 + 1669/774*(w24 * w45)^9 + 523/258*(w24 * w45)^8 + 479/774*(w24 * w45)^7 - 1114/387*(w24 * w45)^6 - 417/86*(w24 * w45)^5 - 701/387*(w24 * w45)^4 - 611/258*(w24 * w45)^3 - 53/387*(w24 * w45)^2)*w45^10 + (-1381/387*(w24 * w45)^11 - 1456/387*(w24 * w45)^10 - 95/774*(w24 * w45)^9 - 48/43*(w24 * w45)^8 + 18/43*(w24 * w45)^7 - 1607/774*(w24 * w45)^6 + 479/258*(w24 * w45)^5 - 103/387*(w24 * w45)^4 + 13/18*(w24 * w45)^3 - 2/9*(w24 * w45)^2)*w45^9 + (-2513/774*(w24 * w45)^11 - 1202/387*(w24 * w45)^10 - 4055/774*(w24 * w45)^9 + 196/129*(w24 * w45)^8 - 292/129*(w24 * w45)^7 - 2713/774*(w24 * w45)^6 + 785/258*(w24 * w45)^5 + 2467/387*(w24 * w45)^4 + 1456/387*(w24 * w45)^3 + 139/129*(w24 * w45)^2)*w45^8 + (637/774*(w24 * w45)^11 - 2513/774*(w24 * w45)^10 + 46/387*(w24 * w45)^9 + 381/86*(w24 * w45)^8 + 1601/774*(w24 * w45)^7 - 1327/774*(w24 * w45)^6 - 617/258*(w24 * w45)^5 + 3733/774*(w24 * w45)^4 + 527/129*(w24 * w45)^3 - 139/387*(w24 * w45)^2)*w45^7 + (428/387*(w24 * w45)^11 + 281/387*(w24 * w45)^10 + 1045/387*(w24 * w45)^9 + 49/774*(w24 * w45)^8 + 1579/258*(w24 * w45)^7 + 403/258*(w24 * w45)^6 - 4159/774*(w24 * w45)^5 + 65/129*(w24 * w45)^4 + 493/258*(w24 * w45)^3 - 32/129*(w24 * w45)^2)*w45^6 + (1/3*(w24 * w45)^11 - 1411/774*(w24 * w45)^9 + 1961/774*(w24 * w45)^8 + 64/43*(w24 * w45)^7 + 167/86*(w24 * w45)^6 + 847/774*(w24 * w45)^5 + 229/774*(w24 * w45)^4 - 3/86*(w24 * w45)^3 + 1723/774*(w24 * w45)^2)*w45^5 + (-1/6*(w24 * w45)^11 + 1/2*(w24 * w45)^10 - 469/774*(w24 * w45)^9 + 235/387*(w24 * w45)^8 - 689/774*(w24 * w45)^7 + 661/774*(w24 * w45)^6 + 143/86*(w24 * w45)^5 + 985/774*(w24 * w45)^4 + 926/387*(w24 * w45)^3)*w45^4 + (4/3*(w24 * w45)^11 + 7/6*(w24 * w45)^10 - 1/2*(w24 * w45)^9 - 4/3*(w24 * w45)^8 + 39/86*(w24 * w45)^7 - 539/387*(w24 * w45)^6 - 203/258*(w24 * w45)^5 + 1/6*(w24 * w45)^4)*w45^3 + (1/6*(w24 * w45)^9 - 1/2*(w24 * w45)^8 - 1/3*(w24 * w45)^7 - 1/6*(w24 * w45)^6 + 1/6*(w24 * w45)^5)*w45^2 + (-4/3*(w24 * w45)^9 - (w24 * w45)^8 + (w24 * w45)^6 + (w24 * w45)^5)*w45 + (-1/6*(w24 * w45)^6 + 1/6*(w24 * w45)^5 - (w24 * w45)^4 - (w24 * w45)^3 + (w24 * w45) + 1)) * hf) one_ne_zero
      · have x15 : w15 = -(w24 ^ 3 * w45 ^ 5) := by
          linear_combination E26 + w45 * h04
        have x12 : w12 = -(w24 ^ 2 * w45 ^ 4) := by
          have hx : w12 * w24 = (-(w24 ^ 2 * w45 ^ 4)) * w24 := by
            linear_combination -E42 + h04
          exact mul_right_cancel₀ n24 hx
        have x05 : w05 = w24 ^ 4 * w45 ^ 5 := by
          linear_combination (1 : ℂ) * w45 * E11 + (1 : ℂ) * w05 * h25 + (-1 : ℂ) * w24 * w45 * h04
        have x02 : w02 = w24 ^ 5 * w45 ^ 6 := by
          have hx : w02 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 5 * w45 ^ 6) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E2 + (1 : ℂ) * w02 * x12 + (-1 : ℂ) * w15 * x05 + (-1 : ℂ) * w24 ^ 4 * w45 ^ 5 * x15
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x34 : w34 = w24 ^ 3 * w45 ^ 5 := by
          have hx : w34 * w24 = (w24 ^ 3 * w45 ^ 5) * w24 := by
            linear_combination -E57 + w13 * x12 + (-1 : ℂ) * w24 ^ 2 * w45 ^ 4 * h13
          exact mul_right_cancel₀ n24 hx
        have x14 : w14 = w24 ^ 4 * w45 ^ 2 := by
          have hx : w14 * (w24 ^ 2 * w45 ^ 4) = (w24 ^ 4 * w45 ^ 2) * (w24 ^ 2 * w45 ^ 4) := by
            linear_combination (-1 : ℂ) * E64 + (1 : ℂ) * w14 * x12 + (-1 : ℂ) * h25 + (-1 : ℂ) * qf
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 n24) (pow_ne_zero 4 n45)) hx
        have x03 : w03 = w24 * w45 := by
          linear_combination E37 + w34 * x14 + (1 : ℂ) * w24 ^ 4 * w45 ^ 2 * x34 + (1 : ℂ) * w24 * w45 * qf
        have x23 : w23 = -(w24 * w45 ^ 3) := by
          have hx : w23 * (w24 ^ 5 * w45 ^ 6) = (-(w24 * w45 ^ 3)) * (w24 ^ 5 * w45 ^ 6) := by
            linear_combination (1 : ℂ) * E15 + (-1 : ℂ) * w23 * x02 + (1 : ℂ) * w34 * h04 + (-1 : ℂ) * w24 ^ 3 * w45 ^ 4 * x34
          exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 5 n24) (pow_ne_zero 6 n45)) hx
        have x35 : w35 = -(w24 ^ 2 * w45 ^ 2) := by
          have hx : w35 * w45 = (-(w24 ^ 2 * w45 ^ 2)) * w45 := by
            linear_combination -E77 + w24 * x23
          exact mul_right_cancel₀ n45 hx
        simp only [x02, x12, x03, h13, h04, x14, x05, x15, x23, x34, x35] at G23 G24 G34 G35 G45
        rcases pow6_split (show (w24 * w45) ^ 6 = 1 by linear_combination qf) with hf | hf | hf | hf
        · exact nc3 (by rw [x05]; linear_combination (1 * w45 * ((w24 * w45) ^ 3 + (1) * (w24 * w45) ^ 2 + (w24 * w45) + (1))) * hf)
        · exact nc1 (by rw [h04, x05]; linear_combination (-1 * w24 ^ 3 * w45 ^ 4) * hf)
        · exact absurd (show ((1 : ℂ)) = 0 by
            linear_combination ((-2/3*(w24 * w45) - 1/2)*w45^6 - 1/6*w45^5 + (-2/3*(w24 * w45) + 1/3)*w45^4 + (5/6*(w24 * w45) + 1)*w45^3 + 4/3*(w24 * w45)*w45^2 + (1/2*(w24 * w45) - 1/2)*w45 + (-11/6*(w24 * w45) - 7/6)) * w45 ^ 3 * G23 + ((-7/6*(w24 * w45) - 1/3)*w45^6 + (1/3*(w24 * w45) + 5/3)*w45^5 + (w24 * w45)*w45^4 - 3/2*w45^3 + (-2*(w24 * w45) - 2)*w45^2 + w45 + (w24 * w45)) * w45 ^ 3 * G24 + ((-7/6*(w24 * w45)^9 + 5/6*(w24 * w45)^8 + 1/3*(w24 * w45)^7 - 7/6*(w24 * w45)^6 + 5/6*(w24 * w45)^5 + 1/3*(w24 * w45)^4 - 1/2*(w24 * w45)^3)*w45^13 + (1/3*(w24 * w45)^9 + 4/3*(w24 * w45)^8 - (w24 * w45)^7 + 1/6*(w24 * w45)^6 + 1/6*(w24 * w45)^5 + 1/3*(w24 * w45)^4 - 1/6*(w24 * w45)^3)*w45^12 + ((w24 * w45)^9 - 1/3*(w24 * w45)^8 - 5/6*(w24 * w45)^7 + 5/6*(w24 * w45)^6 + 7/6*(w24 * w45)^5 - 13/6*(w24 * w45)^4 + 1/2*(w24 * w45)^2)*w45^11 + (-7/6*(w24 * w45)^10 + 5/6*(w24 * w45)^9 - 7/3*(w24 * w45)^8 + 2*(w24 * w45)^7 - 1/6*(w24 * w45)^6 - 17/6*(w24 * w45)^5 + 3/2*(w24 * w45)^3 + 1/6*(w24 * w45)^2)*w45^10 + (-7/6*(w24 * w45)^11 + 7/6*(w24 * w45)^10 - 1/3*(w24 * w45)^9 - 11/6*(w24 * w45)^8 + 4/3*(w24 * w45)^7 + 1/6*(w24 * w45)^5 + 7/6*(w24 * w45)^4 - 1/6*(w24 * w45)^3 - 1/3*(w24 * w45)^2)*w45^9 + (1/3*(w24 * w45)^11 + 7/3*(w24 * w45)^10 - 8/3*(w24 * w45)^9 + 1/3*(w24 * w45)^8 + 1/2*(w24 * w45)^7 + 2/3*(w24 * w45)^5 + 1/2*(w24 * w45)^4 + 1/3*(w24 * w45)^3 - (w24 * w45)^2)*w45^8 + ((w24 * w45)^11 - (w24 * w45)^10 - 5/3*(w24 * w45)^9 + 4/3*(w24 * w45)^8 + 2/3*(w24 * w45)^7 - 1/2*(w24 * w45)^6 + (w24 * w45)^5 + 11/6*(w24 * w45)^4 - 2*(w24 * w45)^3)*w45^7 + (-7/2*(w24 * w45)^10 + 11/6*(w24 * w45)^9 + 11/6*(w24 * w45)^8 - 2*(w24 * w45)^7 + (w24 * w45)^6 - 11/6*(w24 * w45)^5 + 5/3*(w24 * w45)^4 + 1/2*(w24 * w45)^3 + 1/2*(w24 * w45)^2)*w45^6 + (-2*(w24 * w45)^11 + 4*(w24 * w45)^9 - 13/6*(w24 * w45)^8 - 5/3*(w24 * w45)^7 + 4/3*(w24 * w45)^6 + 4/3*(w24 * w45)^5 - 1/2*(w24 * w45)^4 - (w24 * w45)^3 + 7/6*(w24 * w45)^2)*w45^5 + (2*(w24 * w45)^10 - 2*(w24 * w45)^9 - 5/2*(w24 * w45)^8 + 3*(w24 * w45)^7 - 3/2*(w24 * w45)^6 - (w24 * w45)^5 - 4/3*(w24 * w45)^4 + 7/6*(w24 * w45)^3)*w45^4 + ((w24 * w45)^11 - (w24 * w45)^10 - 2*(w24 * w45)^9 + (w24 * w45)^8 + 1/6*(w24 * w45)^7 - 1/2*(w24 * w45)^6 + 1/2*(w24 * w45)^5)*w45^3 + (2*(w24 * w45)^8 - 2*(w24 * w45)^7 + 2*(w24 * w45)^5)*w45^2 + ((w24 * w45)^9 - (w24 * w45)^8 + (w24 * w45)^6 - (w24 * w45)^5)*w45 + (-(w24 * w45)^4 + (w24 * w45)^3 - (w24 * w45) + 1)) * hf) one_ne_zero
        · exact nc2 (by rw [h04]; linear_combination ((-1 : ℂ) * w45 * ((w24 * w45) + (1))) * hf)

/-- The mask of the last class. -/
def maskK24 : Mask := 453513356179089397942340

theorem maskK24_mem : maskK24 ∈ censusRest := by decide

theorem not_supports_k24 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hsup : Supports p maskK24) : False := by
  have hsne : toC (p 1) - toC (p 0) ≠ 0 := toC_sub_ne_zero (ne_of_gp hgp (by decide))
  have htne : barC (p 1) - barC (p 0) ≠ 0 := barC_sub_ne_zero (ne_of_gp hgp (by decide))
  have hC : ∀ i j : Fin 6, i ≠ j → normC p i - normC p j ≠ 0 := fun i j h =>
    normC_sub_ne htne (ne_of_gp hgp h)
  have hY : ∀ i j : Fin 6, i ≠ j → normY p i - normY p j ≠ 0 := fun i j h =>
    normY_sub_ne hsne (ne_of_gp hgp h)
  have hY0 : normY p 0 = 0 := normY_zero
  have hC0 : normC p 0 = 0 := normC_zero
  have hY1 : normY p 1 = 1 := normY_one hsne
  have hC1 : normC p 1 = 1 := normC_one htne
  have S01 : normY p 0 - normY p 1 = normW p 0 1 * (normC p 0 - normC p 1) :=
    normW_spec (hC 0 1 (by decide))
  have S02 : normY p 0 - normY p 2 = normW p 0 2 * (normC p 0 - normC p 2) :=
    normW_spec (hC 0 2 (by decide))
  have S03 : normY p 0 - normY p 3 = normW p 0 3 * (normC p 0 - normC p 3) :=
    normW_spec (hC 0 3 (by decide))
  have S04 : normY p 0 - normY p 4 = normW p 0 4 * (normC p 0 - normC p 4) :=
    normW_spec (hC 0 4 (by decide))
  have S05 : normY p 0 - normY p 5 = normW p 0 5 * (normC p 0 - normC p 5) :=
    normW_spec (hC 0 5 (by decide))
  have S10 : normY p 1 - normY p 0 = normW p 0 1 * (normC p 1 - normC p 0) :=
    normW_spec' (hC 0 1 (by decide))
  have S12 : normY p 1 - normY p 2 = normW p 1 2 * (normC p 1 - normC p 2) :=
    normW_spec (hC 1 2 (by decide))
  have S13 : normY p 1 - normY p 3 = normW p 1 3 * (normC p 1 - normC p 3) :=
    normW_spec (hC 1 3 (by decide))
  have S14 : normY p 1 - normY p 4 = normW p 1 4 * (normC p 1 - normC p 4) :=
    normW_spec (hC 1 4 (by decide))
  have S15 : normY p 1 - normY p 5 = normW p 1 5 * (normC p 1 - normC p 5) :=
    normW_spec (hC 1 5 (by decide))
  have S20 : normY p 2 - normY p 0 = normW p 0 2 * (normC p 2 - normC p 0) :=
    normW_spec' (hC 0 2 (by decide))
  have S21 : normY p 2 - normY p 1 = normW p 1 2 * (normC p 2 - normC p 1) :=
    normW_spec' (hC 1 2 (by decide))
  have S23 : normY p 2 - normY p 3 = normW p 2 3 * (normC p 2 - normC p 3) :=
    normW_spec (hC 2 3 (by decide))
  have S24 : normY p 2 - normY p 4 = normW p 2 4 * (normC p 2 - normC p 4) :=
    normW_spec (hC 2 4 (by decide))
  have S25 : normY p 2 - normY p 5 = normW p 2 5 * (normC p 2 - normC p 5) :=
    normW_spec (hC 2 5 (by decide))
  have S30 : normY p 3 - normY p 0 = normW p 0 3 * (normC p 3 - normC p 0) :=
    normW_spec' (hC 0 3 (by decide))
  have S31 : normY p 3 - normY p 1 = normW p 1 3 * (normC p 3 - normC p 1) :=
    normW_spec' (hC 1 3 (by decide))
  have S32 : normY p 3 - normY p 2 = normW p 2 3 * (normC p 3 - normC p 2) :=
    normW_spec' (hC 2 3 (by decide))
  have S34 : normY p 3 - normY p 4 = normW p 3 4 * (normC p 3 - normC p 4) :=
    normW_spec (hC 3 4 (by decide))
  have S35 : normY p 3 - normY p 5 = normW p 3 5 * (normC p 3 - normC p 5) :=
    normW_spec (hC 3 5 (by decide))
  have S40 : normY p 4 - normY p 0 = normW p 0 4 * (normC p 4 - normC p 0) :=
    normW_spec' (hC 0 4 (by decide))
  have S41 : normY p 4 - normY p 1 = normW p 1 4 * (normC p 4 - normC p 1) :=
    normW_spec' (hC 1 4 (by decide))
  have S42 : normY p 4 - normY p 2 = normW p 2 4 * (normC p 4 - normC p 2) :=
    normW_spec' (hC 2 4 (by decide))
  have S43 : normY p 4 - normY p 3 = normW p 3 4 * (normC p 4 - normC p 3) :=
    normW_spec' (hC 3 4 (by decide))
  have S45 : normY p 4 - normY p 5 = normW p 4 5 * (normC p 4 - normC p 5) :=
    normW_spec (hC 4 5 (by decide))
  have S50 : normY p 5 - normY p 0 = normW p 0 5 * (normC p 5 - normC p 0) :=
    normW_spec' (hC 0 5 (by decide))
  have S51 : normY p 5 - normY p 1 = normW p 1 5 * (normC p 5 - normC p 1) :=
    normW_spec' (hC 1 5 (by decide))
  have S52 : normY p 5 - normY p 2 = normW p 2 5 * (normC p 5 - normC p 2) :=
    normW_spec' (hC 2 5 (by decide))
  have S53 : normY p 5 - normY p 3 = normW p 3 5 * (normC p 5 - normC p 3) :=
    normW_spec' (hC 3 5 (by decide))
  have S54 : normY p 5 - normY p 4 = normW p 4 5 * (normC p 5 - normC p 4) :=
    normW_spec' (hC 4 5 (by decide))
  have hw01 : normW p 0 1 = 1 := by
    have k := S01
    rw [hY0, hY1, hC0, hC1] at k
    linear_combination k
  have N02 : normW p 0 2 ≠ 0 := normW_ne (hY 0 2 (by decide)) (hC 0 2 (by decide))
  have N03 : normW p 0 3 ≠ 0 := normW_ne (hY 0 3 (by decide)) (hC 0 3 (by decide))
  have N04 : normW p 0 4 ≠ 0 := normW_ne (hY 0 4 (by decide)) (hC 0 4 (by decide))
  have N05 : normW p 0 5 ≠ 0 := normW_ne (hY 0 5 (by decide)) (hC 0 5 (by decide))
  have N12 : normW p 1 2 ≠ 0 := normW_ne (hY 1 2 (by decide)) (hC 1 2 (by decide))
  have N13 : normW p 1 3 ≠ 0 := normW_ne (hY 1 3 (by decide)) (hC 1 3 (by decide))
  have N14 : normW p 1 4 ≠ 0 := normW_ne (hY 1 4 (by decide)) (hC 1 4 (by decide))
  have N15 : normW p 1 5 ≠ 0 := normW_ne (hY 1 5 (by decide)) (hC 1 5 (by decide))
  have N23 : normW p 2 3 ≠ 0 := normW_ne (hY 2 3 (by decide)) (hC 2 3 (by decide))
  have N24 : normW p 2 4 ≠ 0 := normW_ne (hY 2 4 (by decide)) (hC 2 4 (by decide))
  have N25 : normW p 2 5 ≠ 0 := normW_ne (hY 2 5 (by decide)) (hC 2 5 (by decide))
  have N34 : normW p 3 4 ≠ 0 := normW_ne (hY 3 4 (by decide)) (hC 3 4 (by decide))
  have N35 : normW p 3 5 ≠ 0 := normW_ne (hY 3 5 (by decide)) (hC 3 5 (by decide))
  have N45 : normW p 4 5 ≠ 0 := normW_ne (hY 4 5 (by decide)) (hC 4 5 (by decide))
  have P2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hsup 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have EQ2 : normW p 0 2 * normW p 1 2 = normW p 0 5 * normW p 1 5 :=
    witness_monomial S20 S21 S50 S51 (hC 2 0 (by decide)) (hC 2 1 (by decide)) (hC 5 0 (by decide)) (hC 5 1 (by decide)) (cell_bridge hsne htne 2 5 0 1 P2)
  have P6 : Psi (p 1) (p 3) (p 0) (p 2) = 0 := by
    have h := hsup 6 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 6 = ((0, 2), (1, 3)) from by decide)] at h
  have EQ6 : normW p 1 2 = normW p 0 3 * normW p 2 3 := by
    have k := witness_monomial S10 S12 S30 S32 (hC 1 0 (by decide)) (hC 1 2 (by decide)) (hC 3 0 (by decide)) (hC 3 2 (by decide)) (cell_bridge hsne htne 1 3 0 2 P6)
    rwa [hw01, one_mul] at k
  have P11 : Psi (p 4) (p 5) (p 0) (p 2) = 0 := by
    have h := hsup 11 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 11 = ((0, 2), (4, 5)) from by decide)] at h
  have EQ11 : normW p 0 4 * normW p 2 4 = normW p 0 5 * normW p 2 5 :=
    witness_monomial S40 S42 S50 S52 (hC 4 0 (by decide)) (hC 4 2 (by decide)) (hC 5 0 (by decide)) (hC 5 2 (by decide)) (cell_bridge hsne htne 4 5 0 2 P11)
  have P15 : Psi (p 2) (p 4) (p 0) (p 3) = 0 := by
    have h := hsup 15 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 15 = ((0, 3), (2, 4)) from by decide)] at h
  have EQ15 : normW p 0 2 * normW p 2 3 = normW p 0 4 * normW p 3 4 :=
    witness_monomial S20 S23 S40 S43 (hC 2 0 (by decide)) (hC 2 3 (by decide)) (hC 4 0 (by decide)) (hC 4 3 (by decide)) (cell_bridge hsne htne 2 4 0 3 P15)
  have P23 : Psi (p 3) (p 5) (p 0) (p 4) = 0 := by
    have h := hsup 23 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 23 = ((0, 4), (3, 5)) from by decide)] at h
  have EQ23 : normW p 0 3 * normW p 3 4 = normW p 0 5 * normW p 4 5 :=
    witness_monomial S30 S34 S50 S54 (hC 3 0 (by decide)) (hC 3 4 (by decide)) (hC 5 0 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 3 5 0 4 P23)
  have P26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hsup 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have EQ26 : normW p 1 5 = normW p 0 4 * normW p 4 5 := by
    have k := witness_monomial S10 S15 S40 S45 (hC 1 0 (by decide)) (hC 1 5 (by decide)) (hC 4 0 (by decide)) (hC 4 5 (by decide)) (cell_bridge hsne htne 1 4 0 5 P26)
    rwa [hw01, one_mul] at k
  have P34 : Psi (p 3) (p 5) (p 1) (p 2) = 0 := by
    have h := hsup 34 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 34 = ((1, 2), (3, 5)) from by decide)] at h
  have EQ34 : normW p 1 3 * normW p 2 3 = normW p 1 5 * normW p 2 5 :=
    witness_monomial S31 S32 S51 S52 (hC 3 1 (by decide)) (hC 3 2 (by decide)) (hC 5 1 (by decide)) (hC 5 2 (by decide)) (cell_bridge hsne htne 3 5 1 2 P34)
  have P37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hsup 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have EQ37 : normW p 0 3 = normW p 1 4 * normW p 3 4 := by
    have k := witness_monomial S01 S03 S41 S43 (hC 0 1 (by decide)) (hC 0 3 (by decide)) (hC 4 1 (by decide)) (hC 4 3 (by decide)) (cell_bridge hsne htne 0 4 1 3 P37)
    rwa [hw01, one_mul] at k
  have P42 : Psi (p 0) (p 2) (p 1) (p 4) = 0 := by
    have h := hsup 42 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 42 = ((1, 4), (0, 2)) from by decide)] at h
  have EQ42 : normW p 0 4 = normW p 1 2 * normW p 2 4 := by
    have k := witness_monomial S01 S04 S21 S24 (hC 0 1 (by decide)) (hC 0 4 (by decide)) (hC 2 1 (by decide)) (hC 2 4 (by decide)) (cell_bridge hsne htne 0 2 1 4 P42)
    rwa [hw01, one_mul] at k
  have P53 : Psi (p 3) (p 4) (p 1) (p 5) = 0 := by
    have h := hsup 53 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 53 = ((1, 5), (3, 4)) from by decide)] at h
  have EQ53 : normW p 1 3 * normW p 3 5 = normW p 1 4 * normW p 4 5 :=
    witness_monomial S31 S35 S41 S45 (hC 3 1 (by decide)) (hC 3 5 (by decide)) (hC 4 1 (by decide)) (hC 4 5 (by decide)) (cell_bridge hsne htne 3 4 1 5 P53)
  have P57 : Psi (p 1) (p 4) (p 2) (p 3) = 0 := by
    have h := hsup 57 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 57 = ((2, 3), (1, 4)) from by decide)] at h
  have EQ57 : normW p 1 2 * normW p 1 3 = normW p 2 4 * normW p 3 4 :=
    witness_monomial S12 S13 S42 S43 (hC 1 2 (by decide)) (hC 1 3 (by decide)) (hC 4 2 (by decide)) (hC 4 3 (by decide)) (cell_bridge hsne htne 1 4 2 3 P57)
  have P64 : Psi (p 1) (p 5) (p 2) (p 4) = 0 := by
    have h := hsup 64 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 64 = ((2, 4), (1, 5)) from by decide)] at h
  have EQ64 : normW p 1 2 * normW p 1 4 = normW p 2 5 * normW p 4 5 :=
    witness_monomial S12 S14 S52 S54 (hC 1 2 (by decide)) (hC 1 4 (by decide)) (hC 5 2 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 1 5 2 4 P64)
  have P67 : Psi (p 0) (p 3) (p 2) (p 5) = 0 := by
    have h := hsup 67 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 67 = ((2, 5), (0, 3)) from by decide)] at h
  have EQ67 : normW p 0 2 * normW p 0 5 = normW p 2 3 * normW p 3 5 :=
    witness_monomial S02 S05 S32 S35 (hC 0 2 (by decide)) (hC 0 5 (by decide)) (hC 3 2 (by decide)) (hC 3 5 (by decide)) (cell_bridge hsne htne 0 3 2 5 P67)
  have P77 : Psi (p 2) (p 5) (p 3) (p 4) = 0 := by
    have h := hsup 77 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 77 = ((3, 4), (2, 5)) from by decide)] at h
  have EQ77 : normW p 2 3 * normW p 2 4 = normW p 3 5 * normW p 4 5 :=
    witness_monomial S23 S24 S53 S54 (hC 2 3 (by decide)) (hC 2 4 (by decide)) (hC 5 3 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 2 5 3 4 P77)
  have P78 : Psi (p 0) (p 1) (p 3) (p 5) = 0 := by
    have h := hsup 78 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 78 = ((3, 5), (0, 1)) from by decide)] at h
  have EQ78 : normW p 0 3 * normW p 0 5 = normW p 1 3 * normW p 1 5 :=
    witness_monomial S03 S05 S13 S15 (hC 0 3 (by decide)) (hC 0 5 (by decide)) (hC 1 3 (by decide)) (hC 1 5 (by decide)) (cell_bridge hsne htne 0 1 3 5 P78)
  have nc1 : normW p 0 4 ≠ normW p 0 5 := fun h =>
    ncol_of_gp hgp (show (0 : Fin 6) ≠ 4 by decide) (show (0 : Fin 6) ≠ 5 by decide)
      (show (4 : Fin 6) ≠ 5 by decide) (collinear_of_w hsne htne S04 S05 h)
  have nc2 : normW p 0 4 ≠ normW p 4 5 := fun h =>
    ncol_of_gp hgp (show (4 : Fin 6) ≠ 0 by decide) (show (4 : Fin 6) ≠ 5 by decide)
      (show (0 : Fin 6) ≠ 5 by decide) (collinear_of_w hsne htne S40 S45 h)
  have nc3 : normW p 0 5 ≠ normW p 4 5 := fun h =>
    ncol_of_gp hgp (show (5 : Fin 6) ≠ 0 by decide) (show (5 : Fin 6) ≠ 4 by decide)
      (show (0 : Fin 6) ≠ 4 by decide) (collinear_of_w hsne htne S50 S54 h)
  have u2 : normY p 2 = normW p 0 2 * normC p 2 := by
    have k := S02
    rw [hY0, hC0] at k
    linear_combination -k
  have v2 : 1 - normY p 2 = normW p 1 2 * (1 - normC p 2) := by
    have k := S12
    rwa [hY1, hC1] at k
  have u3 : normY p 3 = normW p 0 3 * normC p 3 := by
    have k := S03
    rw [hY0, hC0] at k
    linear_combination -k
  have v3 : 1 - normY p 3 = normW p 1 3 * (1 - normC p 3) := by
    have k := S13
    rwa [hY1, hC1] at k
  have u4 : normY p 4 = normW p 0 4 * normC p 4 := by
    have k := S04
    rw [hY0, hC0] at k
    linear_combination -k
  have v4 : 1 - normY p 4 = normW p 1 4 * (1 - normC p 4) := by
    have k := S14
    rwa [hY1, hC1] at k
  have u5 : normY p 5 = normW p 0 5 * normC p 5 := by
    have k := S05
    rw [hY0, hC0] at k
    linear_combination -k
  have v5 : 1 - normY p 5 = normW p 1 5 * (1 - normC p 5) := by
    have k := S15
    rwa [hY1, hC1] at k
  have g23 : normY p 2 - normY p 3 = normW p 2 3 * (normC p 2 - normC p 3) := S23
  have g24 : normY p 2 - normY p 4 = normW p 2 4 * (normC p 2 - normC p 4) := S24
  have g34 : normY p 3 - normY p 4 = normW p 3 4 * (normC p 3 - normC p 4) := S34
  have g35 : normY p 3 - normY p 5 = normW p 3 5 * (normC p 3 - normC p 5) := S35
  have g45 : normY p 4 - normY p 5 = normW p 4 5 * (normC p 4 - normC p 5) := S45
  exact core_class24 (normW p 0 2) (normW p 0 3) (normW p 0 4) (normW p 0 5) (normW p 1 2) (normW p 1 3) (normW p 1 4) (normW p 1 5) (normW p 2 3) (normW p 2 4) (normW p 2 5) (normW p 3 4) (normW p 3 5) (normW p 4 5)
    (normY p 2) (normC p 2) (normY p 3) (normC p 3) (normY p 4) (normC p 4) (normY p 5) (normC p 5)
    N02 N03 N04 N05 N12 N13 N14 N15 N23 N24 N25 N34 N35 N45
    EQ2 EQ6 EQ11 EQ15 EQ23 EQ26 EQ34 EQ37 EQ42 EQ53 EQ57 EQ64 EQ67 EQ77 EQ78
    u2 v2 u3 v3 u4 v4 u5 v5 g23 g24 g34 g35 g45 nc1 nc2 nc3

theorem not_carries_k24 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK24) : False :=
  not_supports_k24 p hgp (supports_of_carries hc)



end QB13

end DistinctCircumradii

#print axioms DistinctCircumradii.QB13.cellPsi_eq
#print axioms DistinctCircumradii.QB13.maskK31_mem
#print axioms DistinctCircumradii.QB13.collinear_of_cross_eq
#print axioms DistinctCircumradii.QB13.div_mul_cancel_ne
#print axioms DistinctCircumradii.QB13.normY_sub
#print axioms DistinctCircumradii.QB13.normC_sub
#print axioms DistinctCircumradii.QB13.normY_zero
#print axioms DistinctCircumradii.QB13.normC_zero
#print axioms DistinctCircumradii.QB13.normY_one
#print axioms DistinctCircumradii.QB13.normC_one
#print axioms DistinctCircumradii.QB13.normY_sub_ne
#print axioms DistinctCircumradii.QB13.normC_sub_ne
#print axioms DistinctCircumradii.QB13.normW_spec
#print axioms DistinctCircumradii.QB13.normW_spec'
#print axioms DistinctCircumradii.QB13.normW_ne
#print axioms DistinctCircumradii.QB13.cell_bridge
#print axioms DistinctCircumradii.QB13.witness_monomial
#print axioms DistinctCircumradii.QB13.sq_split
#print axioms DistinctCircumradii.QB13.pow22_split
#print axioms DistinctCircumradii.QB13.pow6_split
#print axioms DistinctCircumradii.QB13.pair_relation
#print axioms DistinctCircumradii.QB13.collinear_of_w
#print axioms DistinctCircumradii.QB13.core_class24
#print axioms DistinctCircumradii.QB13.maskK24_mem
#print axioms DistinctCircumradii.QB13.not_supports_k24
#print axioms DistinctCircumradii.QB13.not_carries_k24
