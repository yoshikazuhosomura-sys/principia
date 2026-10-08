import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（枝分かれの議論）：名前空間 `QB12` の k27

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QB12

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

/-- A twenty-sixth root of unity lies on one of the four cyclotomic factors. -/
theorem pow26_split {x : ℂ} (h : x ^ 26 = 1) :
    x = 1 ∨ x = -1
      ∨ x ^ 12 + x ^ 11 + x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0
      ∨ x ^ 12 - x ^ 11 + x ^ 10 - x ^ 9 + x ^ 8 - x ^ 7 + x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0 := by
  have k : (x - 1) * ((x + 1)
      * ((x ^ 12 + x ^ 11 + x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1)
        * (x ^ 12 - x ^ 11 + x ^ 10 - x ^ 9 + x ^ 8 - x ^ 7 + x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1))) = 0 := by linear_combination h
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

set_option maxHeartbeats 40000000 in
/-- **The third class of this shape is not supported either.** -/
theorem core_class27
    (w02 w03 w04 w05 w12 w13 w14 w15 w23 w24 w25 w34 w35 w45 : ℂ)
    (Y2 C2 Y3 C3 : ℂ)
    (n02 : w02 ≠ 0) (n03 : w03 ≠ 0) (n04 : w04 ≠ 0) (n05 : w05 ≠ 0)
    (n12 : w12 ≠ 0) (n13 : w13 ≠ 0) (n14 : w14 ≠ 0) (n15 : w15 ≠ 0)
    (n23 : w23 ≠ 0) (n24 : w24 ≠ 0) (n25 : w25 ≠ 0) (n34 : w34 ≠ 0)
    (n35 : w35 ≠ 0) (n45 : w45 ≠ 0)
    (E1 : w02 * w12 = w04 * w14)
    (E11 : w04 * w24 = w05 * w25)
    (E14 : w13 = w05 * w35)
    (E21 : w02 * w24 = w03 * w34)
    (E24 : w15 = w02 * w25)
    (E30 : w02 = w13 * w23)
    (E37 : w03 = w14 * w34)
    (E46 : w12 * w24 = w15 * w45)
    (E53 : w13 * w35 = w14 * w45)
    (E57 : w12 * w13 = w24 * w34)
    (E65 : w23 * w34 = w25 * w45)
    (E69 : w12 * w15 = w23 * w35)
    (E74 : w03 * w04 = w35 * w45)
    (E79 : w03 * w05 = w23 * w25)
    (E84 : w04 * w05 = w14 * w15)
    (u2 : Y2 = w02 * C2) (v2 : 1 - Y2 = w12 * (1 - C2))
    (u3 : Y3 = w03 * C3) (v3 : 1 - Y3 = w13 * (1 - C3))
    (g23 : Y2 - Y3 = w23 * (C2 - C3))
    (nc1 : w03 ≠ 1) (nc2 : w13 ≠ 1) (nc3 : w03 ≠ w13) :
    False := by
  have t02 : w02 ^ 2 = w05 ^ 24 := by
    have hPQ_t02 : w02 ^ 10 * w03 ^ 10 * w04 ^ 7 * w12 ^ 4 * w13 ^ 10 * w14 ^ 5 * w15 ^ 5 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3 = w02 ^ 8 * w03 ^ 10 * w04 ^ 7 * w05 ^ 24 * w12 ^ 4 * w13 ^ 10 * w14 ^ 5 * w15 ^ 5 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3 := by
      linear_combination (-w02 ^ 10 * w03 ^ 10 * w04 ^ 6 * w12 ^ 4 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E1 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 5 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 7 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 4 * w05 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 6 * w25 ^ 8 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 3 * w05 ^ 2 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 5 * w25 ^ 9 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 2 * w05 ^ 3 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 4 * w25 ^ 10 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 * w05 ^ 4 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 3 * w25 ^ 11 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 5 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 12 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 6 * w12 ^ 5 * w13 ^ 9 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 7 * w12 ^ 5 * w13 ^ 8 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 8 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 8 * w12 ^ 5 * w13 ^ 7 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 9 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 9 * w12 ^ 5 * w13 ^ 6 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 10 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 10 * w12 ^ 5 * w13 ^ 5 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 11 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 11 * w12 ^ 5 * w13 ^ 4 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 12 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 12 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 13 * w45 ^ 3) * E14 + (-w02 ^ 11 * w03 ^ 9 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 2 * w25 ^ 13 * w34 ^ 5 * w35 ^ 14 * w45 ^ 3) * E21 + (-w02 ^ 12 * w03 ^ 8 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 3 * w25 ^ 13 * w34 ^ 4 * w35 ^ 14 * w45 ^ 3) * E21 + (-w02 ^ 13 * w03 ^ 7 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 4 * w25 ^ 13 * w34 ^ 3 * w35 ^ 14 * w45 ^ 3) * E21 + (-w02 ^ 14 * w03 ^ 6 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 5 * w25 ^ 13 * w34 ^ 2 * w35 ^ 14 * w45 ^ 3) * E21 + (-w02 ^ 15 * w03 ^ 5 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 6 * w25 ^ 13 * w34 * w35 ^ 14 * w45 ^ 3) * E21 + (-w02 ^ 16 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 5 * w23 ^ 10 * w24 ^ 7 * w25 ^ 13 * w35 ^ 14 * w45 ^ 3) * E21 + (w02 ^ 17 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 4 * w23 ^ 10 * w24 ^ 8 * w25 ^ 13 * w35 ^ 14 * w45 ^ 3) * E24 + (w02 ^ 17 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 3 * w14 ^ 4 * w15 ^ 4 * w23 ^ 10 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 16 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 4 * w14 ^ 4 * w15 ^ 4 * w23 ^ 11 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 15 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 5 * w14 ^ 4 * w15 ^ 4 * w23 ^ 12 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 14 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 6 * w14 ^ 4 * w15 ^ 4 * w23 ^ 13 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 13 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 7 * w14 ^ 4 * w15 ^ 4 * w23 ^ 14 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 12 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 8 * w14 ^ 4 * w15 ^ 4 * w23 ^ 15 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 11 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 9 * w14 ^ 4 * w15 ^ 4 * w23 ^ 16 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 10 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 4 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 9 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 4 * w23 ^ 18 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 8 * w03 ^ 4 * w05 ^ 13 * w12 ^ 5 * w13 ^ 12 * w14 ^ 4 * w15 ^ 4 * w23 ^ 19 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E30 + (w02 ^ 8 * w03 ^ 3 * w05 ^ 13 * w12 ^ 5 * w13 ^ 13 * w14 ^ 4 * w15 ^ 4 * w23 ^ 20 * w24 ^ 8 * w25 ^ 14 * w35 ^ 14 * w45 ^ 3) * E37 + (w02 ^ 8 * w03 ^ 2 * w05 ^ 13 * w12 ^ 5 * w13 ^ 13 * w14 ^ 5 * w15 ^ 4 * w23 ^ 20 * w24 ^ 8 * w25 ^ 14 * w34 * w35 ^ 14 * w45 ^ 3) * E37 + (w02 ^ 8 * w03 * w05 ^ 13 * w12 ^ 5 * w13 ^ 13 * w14 ^ 6 * w15 ^ 4 * w23 ^ 20 * w24 ^ 8 * w25 ^ 14 * w34 ^ 2 * w35 ^ 14 * w45 ^ 3) * E37 + (w02 ^ 8 * w05 ^ 13 * w12 ^ 5 * w13 ^ 13 * w14 ^ 7 * w15 ^ 4 * w23 ^ 20 * w24 ^ 8 * w25 ^ 14 * w34 ^ 3 * w35 ^ 14 * w45 ^ 3) * E37 + (w02 ^ 8 * w05 ^ 13 * w12 ^ 4 * w13 ^ 13 * w14 ^ 8 * w15 ^ 4 * w23 ^ 20 * w24 ^ 7 * w25 ^ 14 * w34 ^ 4 * w35 ^ 14 * w45 ^ 3) * E46 + (w02 ^ 8 * w05 ^ 13 * w12 ^ 3 * w13 ^ 13 * w14 ^ 8 * w15 ^ 5 * w23 ^ 20 * w24 ^ 6 * w25 ^ 14 * w34 ^ 4 * w35 ^ 14 * w45 ^ 4) * E46 + (w02 ^ 8 * w05 ^ 13 * w12 ^ 3 * w13 ^ 12 * w14 ^ 8 * w15 ^ 6 * w23 ^ 20 * w24 ^ 6 * w25 ^ 14 * w34 ^ 4 * w35 ^ 13 * w45 ^ 5) * E53 + (w02 ^ 8 * w05 ^ 13 * w12 ^ 2 * w13 ^ 11 * w14 ^ 9 * w15 ^ 6 * w23 ^ 20 * w24 ^ 6 * w25 ^ 14 * w34 ^ 4 * w35 ^ 13 * w45 ^ 6) * E57 + (w02 ^ 8 * w05 ^ 13 * w12 * w13 ^ 10 * w14 ^ 9 * w15 ^ 6 * w23 ^ 20 * w24 ^ 7 * w25 ^ 14 * w34 ^ 5 * w35 ^ 13 * w45 ^ 6) * E57 + (-w02 ^ 8 * w05 ^ 13 * w12 * w13 ^ 10 * w14 ^ 9 * w15 ^ 6 * w23 ^ 19 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 12 * w45 ^ 6) * E69 + (-w02 ^ 8 * w05 ^ 13 * w12 ^ 2 * w13 ^ 10 * w14 ^ 9 * w15 ^ 7 * w23 ^ 18 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 11 * w45 ^ 6) * E69 + (-w02 ^ 8 * w05 ^ 13 * w12 ^ 3 * w13 ^ 10 * w14 ^ 9 * w15 ^ 8 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 10 * w45 ^ 6) * E69 + (-w02 ^ 8 * w05 ^ 13 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 9 * w45 ^ 5) * E74 + (-w02 ^ 8 * w03 * w04 * w05 ^ 13 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 8 * w45 ^ 4) * E74 + (-w02 ^ 8 * w03 ^ 2 * w04 ^ 2 * w05 ^ 13 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E74 + (-w02 ^ 8 * w03 ^ 3 * w04 ^ 3 * w05 ^ 13 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 16 * w24 ^ 8 * w25 ^ 13 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 4 * w04 ^ 3 * w05 ^ 14 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 15 * w24 ^ 8 * w25 ^ 12 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 5 * w04 ^ 3 * w05 ^ 15 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 14 * w24 ^ 8 * w25 ^ 11 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 6 * w04 ^ 3 * w05 ^ 16 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 13 * w24 ^ 8 * w25 ^ 10 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 7 * w04 ^ 3 * w05 ^ 17 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 12 * w24 ^ 8 * w25 ^ 9 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 8 * w04 ^ 3 * w05 ^ 18 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 11 * w24 ^ 8 * w25 ^ 8 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 9 * w04 ^ 3 * w05 ^ 19 * w12 ^ 4 * w13 ^ 10 * w14 ^ 9 * w15 ^ 9 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E79 + (-w02 ^ 8 * w03 ^ 10 * w04 ^ 3 * w05 ^ 20 * w12 ^ 4 * w13 ^ 10 * w14 ^ 8 * w15 ^ 8 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E84 + (-w02 ^ 8 * w03 ^ 10 * w04 ^ 4 * w05 ^ 21 * w12 ^ 4 * w13 ^ 10 * w14 ^ 7 * w15 ^ 7 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E84 + (-w02 ^ 8 * w03 ^ 10 * w04 ^ 5 * w05 ^ 22 * w12 ^ 4 * w13 ^ 10 * w14 ^ 6 * w15 ^ 6 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E84 + (-w02 ^ 8 * w03 ^ 10 * w04 ^ 6 * w05 ^ 23 * w12 ^ 4 * w13 ^ 10 * w14 ^ 5 * w15 ^ 5 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E84
    have hK_t02 : w02 ^ 8 * w03 ^ 10 * w04 ^ 7 * w12 ^ 4 * w13 ^ 10 * w14 ^ 5 * w15 ^ 5 * w23 ^ 10 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 8 n02) (pow_ne_zero 10 n03)) (pow_ne_zero 7 n04)) (pow_ne_zero 4 n12)) (pow_ne_zero 10 n13)) (pow_ne_zero 5 n14)) (pow_ne_zero 5 n15)) (pow_ne_zero 10 n23)) (pow_ne_zero 8 n24)) (pow_ne_zero 7 n25)) (pow_ne_zero 6 n34)) (pow_ne_zero 7 n35)) (pow_ne_zero 3 n45)
    exact mul_right_cancel₀ hK_t02 (by linear_combination hPQ_t02)
  have t03 : w03 ^ 2 = w05 ^ 2 := by
    have hPQ_t03 : w02 * w03 ^ 2 * w04 * w14 * w15 * w24 * w25 * w34 = w02 * w04 * w05 ^ 2 * w14 * w15 * w24 * w25 * w34 := by
      linear_combination (w02 * w03 ^ 2 * w14 * w15 * w25 * w34) * E11 + (-w02 * w03 * w05 * w14 * w15 * w25 ^ 2) * E21 + (-w02 * w03 * w05 * w14 * w15 * w24 * w25) * E24 + (w02 * w05 * w14 * w15 ^ 2 * w24 * w25) * E37 + (-w02 * w05 * w14 * w15 * w24 * w25 * w34) * E84
    have hK_t03 : w02 * w04 * w14 * w15 * w24 * w25 * w34 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n02) (n04)) (n14)) (n15)) (n24)) (n25)) (n34)
    exact mul_right_cancel₀ hK_t03 (by linear_combination hPQ_t03)
  have t04 : w04 ^ 2 = w05 ^ 22 := by
    have hPQ_t04 : w02 ^ 9 * w03 ^ 10 * w04 ^ 8 * w12 ^ 4 * w13 ^ 9 * w14 ^ 5 * w15 ^ 4 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3 = w02 ^ 9 * w03 ^ 10 * w04 ^ 6 * w05 ^ 22 * w12 ^ 4 * w13 ^ 9 * w14 ^ 5 * w15 ^ 4 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3 := by
      linear_combination (-w02 ^ 9 * w03 ^ 10 * w04 ^ 7 * w12 ^ 4 * w13 ^ 9 * w14 ^ 4 * w15 ^ 4 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E1 + (-w02 ^ 10 * w03 ^ 10 * w04 ^ 6 * w12 ^ 5 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E1 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 5 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 7 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 4 * w05 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 6 * w25 ^ 8 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 3 * w05 ^ 2 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 5 * w25 ^ 9 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 2 * w05 ^ 3 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 4 * w25 ^ 10 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w04 * w05 ^ 4 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 3 * w25 ^ 11 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 5 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 12 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E11 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 6 * w12 ^ 6 * w13 ^ 8 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 7 * w12 ^ 6 * w13 ^ 7 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 7 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 8 * w12 ^ 6 * w13 ^ 6 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 8 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 9 * w12 ^ 6 * w13 ^ 5 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 9 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 10 * w12 ^ 6 * w13 ^ 4 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 10 * w45 ^ 3) * E14 + (w02 ^ 11 * w03 ^ 10 * w05 ^ 11 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 6 * w35 ^ 11 * w45 ^ 3) * E14 + (-w02 ^ 11 * w03 ^ 9 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 2 * w25 ^ 13 * w34 ^ 5 * w35 ^ 12 * w45 ^ 3) * E21 + (-w02 ^ 12 * w03 ^ 8 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 3 * w25 ^ 13 * w34 ^ 4 * w35 ^ 12 * w45 ^ 3) * E21 + (-w02 ^ 13 * w03 ^ 7 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 4 * w25 ^ 13 * w34 ^ 3 * w35 ^ 12 * w45 ^ 3) * E21 + (-w02 ^ 14 * w03 ^ 6 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 5 * w25 ^ 13 * w34 ^ 2 * w35 ^ 12 * w45 ^ 3) * E21 + (-w02 ^ 15 * w03 ^ 5 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 6 * w25 ^ 13 * w34 * w35 ^ 12 * w45 ^ 3) * E21 + (-w02 ^ 16 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 4 * w23 ^ 9 * w24 ^ 7 * w25 ^ 13 * w35 ^ 12 * w45 ^ 3) * E21 + (w02 ^ 17 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 3 * w23 ^ 9 * w24 ^ 8 * w25 ^ 13 * w35 ^ 12 * w45 ^ 3) * E24 + (w02 ^ 17 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 3 * w14 ^ 3 * w15 ^ 3 * w23 ^ 9 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 16 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 4 * w14 ^ 3 * w15 ^ 3 * w23 ^ 10 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 15 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 5 * w14 ^ 3 * w15 ^ 3 * w23 ^ 11 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 14 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 6 * w14 ^ 3 * w15 ^ 3 * w23 ^ 12 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 13 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 7 * w14 ^ 3 * w15 ^ 3 * w23 ^ 13 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 12 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 8 * w14 ^ 3 * w15 ^ 3 * w23 ^ 14 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 11 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 9 * w14 ^ 3 * w15 ^ 3 * w23 ^ 15 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 10 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 10 * w14 ^ 3 * w15 ^ 3 * w23 ^ 16 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 9 * w03 ^ 4 * w05 ^ 12 * w12 ^ 6 * w13 ^ 11 * w14 ^ 3 * w15 ^ 3 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E30 + (w02 ^ 9 * w03 ^ 3 * w05 ^ 12 * w12 ^ 6 * w13 ^ 12 * w14 ^ 3 * w15 ^ 3 * w23 ^ 18 * w24 ^ 8 * w25 ^ 14 * w35 ^ 12 * w45 ^ 3) * E37 + (w02 ^ 9 * w03 ^ 2 * w05 ^ 12 * w12 ^ 6 * w13 ^ 12 * w14 ^ 4 * w15 ^ 3 * w23 ^ 18 * w24 ^ 8 * w25 ^ 14 * w34 * w35 ^ 12 * w45 ^ 3) * E37 + (w02 ^ 9 * w03 * w05 ^ 12 * w12 ^ 6 * w13 ^ 12 * w14 ^ 5 * w15 ^ 3 * w23 ^ 18 * w24 ^ 8 * w25 ^ 14 * w34 ^ 2 * w35 ^ 12 * w45 ^ 3) * E37 + (w02 ^ 9 * w05 ^ 12 * w12 ^ 6 * w13 ^ 12 * w14 ^ 6 * w15 ^ 3 * w23 ^ 18 * w24 ^ 8 * w25 ^ 14 * w34 ^ 3 * w35 ^ 12 * w45 ^ 3) * E37 + (w02 ^ 9 * w05 ^ 12 * w12 ^ 5 * w13 ^ 12 * w14 ^ 7 * w15 ^ 3 * w23 ^ 18 * w24 ^ 7 * w25 ^ 14 * w34 ^ 4 * w35 ^ 12 * w45 ^ 3) * E46 + (w02 ^ 9 * w05 ^ 12 * w12 ^ 4 * w13 ^ 12 * w14 ^ 7 * w15 ^ 4 * w23 ^ 18 * w24 ^ 6 * w25 ^ 14 * w34 ^ 4 * w35 ^ 12 * w45 ^ 4) * E46 + (w02 ^ 9 * w05 ^ 12 * w12 ^ 4 * w13 ^ 11 * w14 ^ 7 * w15 ^ 5 * w23 ^ 18 * w24 ^ 6 * w25 ^ 14 * w34 ^ 4 * w35 ^ 11 * w45 ^ 5) * E53 + (w02 ^ 9 * w05 ^ 12 * w12 ^ 3 * w13 ^ 10 * w14 ^ 8 * w15 ^ 5 * w23 ^ 18 * w24 ^ 6 * w25 ^ 14 * w34 ^ 4 * w35 ^ 11 * w45 ^ 6) * E57 + (w02 ^ 9 * w05 ^ 12 * w12 ^ 2 * w13 ^ 9 * w14 ^ 8 * w15 ^ 5 * w23 ^ 18 * w24 ^ 7 * w25 ^ 14 * w34 ^ 5 * w35 ^ 11 * w45 ^ 6) * E57 + (-w02 ^ 9 * w05 ^ 12 * w12 ^ 2 * w13 ^ 9 * w14 ^ 8 * w15 ^ 5 * w23 ^ 17 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 10 * w45 ^ 6) * E69 + (-w02 ^ 9 * w05 ^ 12 * w12 ^ 3 * w13 ^ 9 * w14 ^ 8 * w15 ^ 6 * w23 ^ 16 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 9 * w45 ^ 6) * E69 + (-w02 ^ 9 * w05 ^ 12 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 16 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 8 * w45 ^ 5) * E74 + (-w02 ^ 9 * w03 * w04 * w05 ^ 12 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 16 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 7 * w45 ^ 4) * E74 + (-w02 ^ 9 * w03 ^ 2 * w04 ^ 2 * w05 ^ 12 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 16 * w24 ^ 8 * w25 ^ 14 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E74 + (-w02 ^ 9 * w03 ^ 3 * w04 ^ 3 * w05 ^ 12 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 15 * w24 ^ 8 * w25 ^ 13 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 4 * w04 ^ 3 * w05 ^ 13 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 14 * w24 ^ 8 * w25 ^ 12 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 5 * w04 ^ 3 * w05 ^ 14 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 13 * w24 ^ 8 * w25 ^ 11 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 6 * w04 ^ 3 * w05 ^ 15 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 12 * w24 ^ 8 * w25 ^ 10 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 7 * w04 ^ 3 * w05 ^ 16 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 11 * w24 ^ 8 * w25 ^ 9 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 8 * w04 ^ 3 * w05 ^ 17 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 10 * w24 ^ 8 * w25 ^ 8 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 9 * w04 ^ 3 * w05 ^ 18 * w12 ^ 4 * w13 ^ 9 * w14 ^ 8 * w15 ^ 7 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E79 + (-w02 ^ 9 * w03 ^ 10 * w04 ^ 3 * w05 ^ 19 * w12 ^ 4 * w13 ^ 9 * w14 ^ 7 * w15 ^ 6 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E84 + (-w02 ^ 9 * w03 ^ 10 * w04 ^ 4 * w05 ^ 20 * w12 ^ 4 * w13 ^ 9 * w14 ^ 6 * w15 ^ 5 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E84 + (-w02 ^ 9 * w03 ^ 10 * w04 ^ 5 * w05 ^ 21 * w12 ^ 4 * w13 ^ 9 * w14 ^ 5 * w15 ^ 4 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E84
    have hK_t04 : w02 ^ 9 * w03 ^ 10 * w04 ^ 6 * w12 ^ 4 * w13 ^ 9 * w14 ^ 5 * w15 ^ 4 * w23 ^ 9 * w24 ^ 8 * w25 ^ 7 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 9 n02) (pow_ne_zero 10 n03)) (pow_ne_zero 6 n04)) (pow_ne_zero 4 n12)) (pow_ne_zero 9 n13)) (pow_ne_zero 5 n14)) (pow_ne_zero 4 n15)) (pow_ne_zero 9 n23)) (pow_ne_zero 8 n24)) (pow_ne_zero 7 n25)) (pow_ne_zero 6 n34)) (pow_ne_zero 6 n35)) (pow_ne_zero 3 n45)
    exact mul_right_cancel₀ hK_t04 (by linear_combination hPQ_t04)
  have t12 : w12 ^ 2 = w05 ^ 6 := by
    have hPQ_t12 : w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w12 ^ 2 * w13 ^ 2 * w14 * w15 * w23 ^ 2 * w24 ^ 3 * w25 ^ 2 * w34 ^ 2 * w35 * w45 = w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 6 * w13 ^ 2 * w14 * w15 * w23 ^ 2 * w24 ^ 3 * w25 ^ 2 * w34 ^ 2 * w35 * w45 := by
      linear_combination (w02 ^ 2 * w03 ^ 3 * w04 * w12 ^ 2 * w13 ^ 2 * w14 * w15 * w23 ^ 2 * w24 ^ 2 * w25 ^ 2 * w34 ^ 2 * w35 * w45) * E11 + (w02 ^ 2 * w03 ^ 3 * w05 * w12 ^ 2 * w13 ^ 2 * w14 * w15 * w23 ^ 2 * w24 * w25 ^ 3 * w34 ^ 2 * w35 * w45) * E11 + (w02 ^ 2 * w03 ^ 3 * w05 ^ 2 * w12 ^ 2 * w13 * w14 * w15 * w23 ^ 2 * w24 * w25 ^ 4 * w34 ^ 2 * w35 * w45) * E14 + (-w02 ^ 2 * w03 ^ 2 * w05 ^ 3 * w12 ^ 2 * w13 * w14 * w15 * w23 ^ 2 * w24 * w25 ^ 4 * w34 * w35 ^ 2 * w45) * E21 + (-w02 ^ 3 * w03 * w05 ^ 3 * w12 ^ 2 * w13 * w14 * w15 * w23 ^ 2 * w24 ^ 2 * w25 ^ 4 * w35 ^ 2 * w45) * E21 + (w02 ^ 3 * w03 * w05 ^ 3 * w12 ^ 2 * w13 * w14 * w15 * w23 ^ 2 * w24 ^ 3 * w25 ^ 4 * w35 ^ 2 * w45) * E30 + (w02 ^ 2 * w03 * w05 ^ 3 * w12 ^ 2 * w13 ^ 2 * w14 * w15 * w23 ^ 3 * w24 ^ 3 * w25 ^ 4 * w35 ^ 2 * w45) * E30 + (w02 ^ 2 * w05 ^ 3 * w12 ^ 2 * w13 ^ 3 * w14 * w15 * w23 ^ 4 * w24 ^ 3 * w25 ^ 4 * w35 ^ 2 * w45) * E37 + (w02 ^ 2 * w05 ^ 3 * w12 * w13 ^ 3 * w14 ^ 2 * w15 * w23 ^ 4 * w24 ^ 2 * w25 ^ 4 * w34 * w35 ^ 2 * w45) * E46 + (w02 ^ 2 * w05 ^ 3 * w13 ^ 2 * w14 ^ 2 * w15 ^ 2 * w23 ^ 4 * w24 ^ 2 * w25 ^ 4 * w34 * w35 ^ 2 * w45 ^ 2) * E57 + (-w02 ^ 2 * w05 ^ 3 * w13 ^ 2 * w14 ^ 2 * w15 ^ 2 * w23 ^ 4 * w24 ^ 3 * w25 ^ 4 * w34 ^ 2 * w35 * w45) * E74 + (-w02 ^ 2 * w03 * w04 * w05 ^ 3 * w13 ^ 2 * w14 ^ 2 * w15 ^ 2 * w23 ^ 3 * w24 ^ 3 * w25 ^ 3 * w34 ^ 2 * w35 * w45) * E79 + (-w02 ^ 2 * w03 ^ 2 * w04 * w05 ^ 4 * w13 ^ 2 * w14 ^ 2 * w15 ^ 2 * w23 ^ 2 * w24 ^ 3 * w25 ^ 2 * w34 ^ 2 * w35 * w45) * E79 + (-w02 ^ 2 * w03 ^ 3 * w04 * w05 ^ 5 * w13 ^ 2 * w14 * w15 * w23 ^ 2 * w24 ^ 3 * w25 ^ 2 * w34 ^ 2 * w35 * w45) * E84
    have hK_t12 : w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w13 ^ 2 * w14 * w15 * w23 ^ 2 * w24 ^ 3 * w25 ^ 2 * w34 ^ 2 * w35 * w45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 n02) (pow_ne_zero 3 n03)) (pow_ne_zero 2 n04)) (pow_ne_zero 2 n13)) (n14)) (n15)) (pow_ne_zero 2 n23)) (pow_ne_zero 3 n24)) (pow_ne_zero 2 n25)) (pow_ne_zero 2 n34)) (n35)) (n45)
    exact mul_right_cancel₀ hK_t12 (by linear_combination hPQ_t12)
  have qf : w05 ^ 26 = (1 : ℂ) := by
    have hPQ_t05 : w02 ^ 11 * w03 ^ 10 * w04 ^ 6 * w05 ^ 26 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4 = w02 ^ 11 * w03 ^ 10 * w04 ^ 6 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4 := by
      linear_combination (-w02 ^ 11 * w03 ^ 10 * w04 ^ 6 * w05 ^ 25 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 9 * w25 ^ 9 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E11 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 7 * w05 ^ 24 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 10 * w25 ^ 8 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E11 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 8 * w05 ^ 23 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 11 * w25 ^ 7 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E11 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 9 * w05 ^ 22 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 12 * w25 ^ 6 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E11 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 10 * w05 ^ 21 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 13 * w25 ^ 5 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E11 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 11 * w05 ^ 20 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 14 * w25 ^ 4 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E11 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 19 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 ^ 7 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 18 * w12 ^ 5 * w13 ^ 12 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 ^ 6 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 17 * w12 ^ 5 * w13 ^ 13 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 ^ 5 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 16 * w12 ^ 5 * w13 ^ 14 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 ^ 4 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 15 * w12 ^ 5 * w13 ^ 15 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 ^ 3 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 14 * w12 ^ 5 * w13 ^ 16 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 ^ 2 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 13 * w12 ^ 5 * w13 ^ 17 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w35 * w45 ^ 4) * E14 + (-w02 ^ 11 * w03 ^ 10 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 18 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 15 * w25 ^ 4 * w34 ^ 7 * w45 ^ 4) * E14 + (w02 ^ 10 * w03 ^ 10 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 14 * w25 ^ 4 * w34 ^ 7 * w45 ^ 4) * E21 + (w02 ^ 9 * w03 ^ 11 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 13 * w25 ^ 4 * w34 ^ 8 * w45 ^ 4) * E21 + (w02 ^ 8 * w03 ^ 12 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 12 * w25 ^ 4 * w34 ^ 9 * w45 ^ 4) * E21 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 11 * w25 ^ 4 * w34 ^ 10 * w45 ^ 4) * E21 + (w02 ^ 6 * w03 ^ 14 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 10 * w25 ^ 4 * w34 ^ 11 * w45 ^ 4) * E21 + (w02 ^ 5 * w03 ^ 15 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 9 * w25 ^ 4 * w34 ^ 12 * w45 ^ 4) * E21 + (w02 ^ 4 * w03 ^ 16 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 8 * w25 ^ 4 * w34 ^ 13 * w45 ^ 4) * E21 + (-w02 ^ 3 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 8 * w25 ^ 3 * w34 ^ 14 * w45 ^ 4) * E24 + (-w02 ^ 2 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 9 * w23 ^ 13 * w24 ^ 8 * w25 ^ 2 * w34 ^ 14 * w45 ^ 4) * E24 + (-w02 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 10 * w23 ^ 13 * w24 ^ 8 * w25 * w34 ^ 14 * w45 ^ 4) * E24 + (-w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 19 * w14 ^ 4 * w15 ^ 11 * w23 ^ 13 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E24 + (-w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 18 * w14 ^ 4 * w15 ^ 12 * w23 ^ 12 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 17 * w14 ^ 4 * w15 ^ 12 * w23 ^ 11 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 2 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 16 * w14 ^ 4 * w15 ^ 12 * w23 ^ 10 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 3 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 15 * w14 ^ 4 * w15 ^ 12 * w23 ^ 9 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 4 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 14 * w14 ^ 4 * w15 ^ 12 * w23 ^ 8 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 5 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 13 * w14 ^ 4 * w15 ^ 12 * w23 ^ 7 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 6 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 12 * w14 ^ 4 * w15 ^ 12 * w23 ^ 6 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 7 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 12 * w23 ^ 5 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 8 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 10 * w14 ^ 4 * w15 ^ 12 * w23 ^ 4 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 9 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 9 * w14 ^ 4 * w15 ^ 12 * w23 ^ 3 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 10 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 8 * w14 ^ 4 * w15 ^ 12 * w23 ^ 2 * w24 ^ 8 * w34 ^ 14 * w45 ^ 4) * E30 + (-w02 ^ 11 * w03 ^ 17 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 8 * w14 ^ 3 * w15 ^ 12 * w23 ^ 2 * w24 ^ 8 * w34 ^ 13 * w45 ^ 4) * E37 + (-w02 ^ 11 * w03 ^ 18 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 8 * w14 ^ 2 * w15 ^ 12 * w23 ^ 2 * w24 ^ 8 * w34 ^ 12 * w45 ^ 4) * E37 + (-w02 ^ 11 * w03 ^ 19 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 8 * w14 * w15 ^ 12 * w23 ^ 2 * w24 ^ 8 * w34 ^ 11 * w45 ^ 4) * E37 + (-w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 8 * w14 * w15 ^ 11 * w23 ^ 2 * w24 ^ 8 * w34 ^ 11 * w45 ^ 3) * E46 + (-w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 6 * w13 ^ 8 * w14 * w15 ^ 10 * w23 ^ 2 * w24 ^ 9 * w34 ^ 11 * w45 ^ 2) * E46 + (-w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 7 * w13 ^ 8 * w14 * w15 ^ 9 * w23 ^ 2 * w24 ^ 10 * w34 ^ 11 * w45) * E46 + (-w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 8 * w13 ^ 8 * w15 ^ 9 * w23 ^ 2 * w24 ^ 11 * w34 ^ 11) * E53 + (-w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 8 * w13 ^ 9 * w15 ^ 9 * w23 ^ 2 * w24 ^ 10 * w34 ^ 10 * w35) * E57 + (-w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 9 * w13 ^ 10 * w15 ^ 9 * w23 ^ 2 * w24 ^ 9 * w34 ^ 9 * w35) * E57 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 10 * w13 ^ 11 * w15 ^ 9 * w23 * w24 ^ 9 * w34 ^ 8 * w35) * E65 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 10 * w13 ^ 11 * w15 ^ 9 * w24 ^ 9 * w25 * w34 ^ 7 * w35 * w45) * E65 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 9 * w13 ^ 11 * w15 ^ 8 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 * w45 ^ 2) * E69 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 8 * w13 ^ 11 * w15 ^ 7 * w23 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 2 * w45 ^ 2) * E69 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 7 * w13 ^ 11 * w15 ^ 6 * w23 ^ 2 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 3 * w45 ^ 2) * E69 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 6 * w13 ^ 11 * w15 ^ 5 * w23 ^ 3 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 4 * w45 ^ 2) * E69 + (w02 ^ 11 * w03 ^ 20 * w04 ^ 12 * w05 ^ 12 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 4 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 5 * w45 ^ 2) * E69 + (w02 ^ 11 * w03 ^ 19 * w04 ^ 11 * w05 ^ 12 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 5 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 6 * w45 ^ 2) * E74 + (w02 ^ 11 * w03 ^ 18 * w04 ^ 10 * w05 ^ 12 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 5 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 7 * w45 ^ 3) * E74 + (w02 ^ 11 * w03 ^ 17 * w04 ^ 10 * w05 ^ 11 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 5 * w24 ^ 9 * w25 ^ 2 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 16 * w04 ^ 10 * w05 ^ 10 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 6 * w24 ^ 9 * w25 ^ 3 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 15 * w04 ^ 10 * w05 ^ 9 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 7 * w24 ^ 9 * w25 ^ 4 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 14 * w04 ^ 10 * w05 ^ 8 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 8 * w24 ^ 9 * w25 ^ 5 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 13 * w04 ^ 10 * w05 ^ 7 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 9 * w24 ^ 9 * w25 ^ 6 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 12 * w04 ^ 10 * w05 ^ 6 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 10 * w24 ^ 9 * w25 ^ 7 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 11 * w04 ^ 10 * w05 ^ 5 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 11 * w24 ^ 9 * w25 ^ 8 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 10 * w05 ^ 4 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 12 * w24 ^ 9 * w25 ^ 9 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E79 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 9 * w05 ^ 3 * w12 ^ 5 * w13 ^ 11 * w15 ^ 4 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E84 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 8 * w05 ^ 2 * w12 ^ 5 * w13 ^ 11 * w14 * w15 ^ 5 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E84 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 7 * w05 * w12 ^ 5 * w13 ^ 11 * w14 ^ 2 * w15 ^ 6 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E84 + (w02 ^ 11 * w03 ^ 10 * w04 ^ 6 * w12 ^ 5 * w13 ^ 11 * w14 ^ 3 * w15 ^ 7 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4) * E84
    have hK_t05 : w02 ^ 11 * w03 ^ 10 * w04 ^ 6 * w12 ^ 5 * w13 ^ 11 * w14 ^ 4 * w15 ^ 8 * w23 ^ 13 * w24 ^ 9 * w25 ^ 10 * w34 ^ 7 * w35 ^ 8 * w45 ^ 4 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 11 n02) (pow_ne_zero 10 n03)) (pow_ne_zero 6 n04)) (pow_ne_zero 5 n12)) (pow_ne_zero 11 n13)) (pow_ne_zero 4 n14)) (pow_ne_zero 8 n15)) (pow_ne_zero 13 n23)) (pow_ne_zero 9 n24)) (pow_ne_zero 10 n25)) (pow_ne_zero 7 n34)) (pow_ne_zero 8 n35)) (pow_ne_zero 4 n45)
    exact mul_right_cancel₀ hK_t05 (by linear_combination hPQ_t05)
  have G23 := pair_relation u2 v2 u3 v3 g23
  rcases sq_split (show w02 ^ 2 = (w05 ^ 12) ^ 2 by linear_combination t02) with h02 | h02
  · rcases sq_split (show w03 ^ 2 = (w05 ^ 1) ^ 2 by linear_combination t03) with h03 | h03
    · rcases sq_split (show w04 ^ 2 = (w05 ^ 11) ^ 2 by linear_combination t04) with h04 | h04
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (2/13*w05^11 - 3/13*w05^10 + 4/13*w05^9 + 3/13*w05^8 + 1/13*w05^6 - 1/13*w05^5 - 3/13*w05^3 - 4/13*w05^2 + 3/13*w05 - 2/13) * G23 + (2/13*w05^23 - 5/13*w05^22 + 7/13*w05^21 - 3/13*w05^20 + 2/13*w05^19 - 8/13*w05^18 + 4/13*w05^17 - 3/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 - 3/13*w05^11 + 4/13*w05^10 - 8/13*w05^9 + 2/13*w05^8 - 3/13*w05^7 + 7/13*w05^6 - 5/13*w05^5 + 2/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (10/13*w05^11 - 7/13*w05^10 + 4/13*w05^9 - 1/13*w05^8 - 2/13*w05^7 + 5/13*w05^6 + 5/13*w05^5 - 2/13*w05^4 - 1/13*w05^3 + 4/13*w05^2 - 7/13*w05 + 10/13) * G23 + (10/13*w05^23 + 3/13*w05^22 - 3/13*w05^21 - 7/13*w05^20 - 6/13*w05^19 - 4/13*w05^18 + 4/13*w05^17 + 9/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 - 9/13*w05^11 - 4/13*w05^10 + 4/13*w05^9 + 6/13*w05^8 + 7/13*w05^7 + 3/13*w05^6 - 3/13*w05^5 - 10/13*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (14/13*w05^11 + 17/13*w05^10 - 4/13*w05^9 + 3/13*w05^8 + 12/13*w05^7 - 3/13*w05^6 - 3/13*w05^5 + 12/13*w05^4 + 3/13*w05^3 - 4/13*w05^2 + 17/13*w05 + 14/13) * G23 + (14/13*w05^23 + 3/13*w05^22 - 21/13*w05^21 - 7/13*w05^20 + 6/13*w05^19 + 20/13*w05^18 - 4/13*w05^17 - 15/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 - 15/13*w05^11 - 4/13*w05^10 + 20/13*w05^9 + 6/13*w05^8 - 7/13*w05^7 - 21/13*w05^6 + 3/13*w05^5 + 14/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (2/13*w05^11 + 5/13*w05^10 - 8/13*w05^9 + 7/13*w05^8 - 2/13*w05^7 - 7/13*w05^6 + 7/13*w05^5 + 2/13*w05^4 - 7/13*w05^3 + 8/13*w05^2 - 5/13*w05 - 2/13) * G23 + (2/13*w05^23 + 7/13*w05^22 - 3/13*w05^21 - 3/13*w05^20 - 2/13*w05^19 - 4/13*w05^18 + 8/13*w05^17 + 1/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 - 1/13*w05^11 - 8/13*w05^10 + 4/13*w05^9 + 2/13*w05^8 + 3/13*w05^7 + 3/13*w05^6 - 7/13*w05^5 - 2/13*w05^4 + w05 + 1) * hf) (by norm_num)
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (2/13*w05^11 - 3/13*w05^10 + 4/13*w05^9 + 3/13*w05^8 + 1/13*w05^6 - 1/13*w05^5 - 3/13*w05^3 - 4/13*w05^2 + 3/13*w05 - 2/13) * G23 + (2/13*w05^23 - 5/13*w05^22 + 7/13*w05^21 - 3/13*w05^20 + 2/13*w05^19 - 8/13*w05^18 + 4/13*w05^17 - 3/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 - 3/13*w05^11 + 4/13*w05^10 - 8/13*w05^9 + 2/13*w05^8 - 3/13*w05^7 + 7/13*w05^6 - 5/13*w05^5 + 2/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (10/13*w05^11 - 7/13*w05^10 + 4/13*w05^9 - 1/13*w05^8 - 2/13*w05^7 + 5/13*w05^6 + 5/13*w05^5 - 2/13*w05^4 - 1/13*w05^3 + 4/13*w05^2 - 7/13*w05 + 10/13) * G23 + (10/13*w05^23 + 3/13*w05^22 - 3/13*w05^21 - 7/13*w05^20 - 6/13*w05^19 - 4/13*w05^18 + 4/13*w05^17 + 9/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 - 9/13*w05^11 - 4/13*w05^10 + 4/13*w05^9 + 6/13*w05^8 + 7/13*w05^7 + 3/13*w05^6 - 3/13*w05^5 - 10/13*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (14/13*w05^11 + 17/13*w05^10 - 4/13*w05^9 + 3/13*w05^8 + 12/13*w05^7 - 3/13*w05^6 - 3/13*w05^5 + 12/13*w05^4 + 3/13*w05^3 - 4/13*w05^2 + 17/13*w05 + 14/13) * G23 + (14/13*w05^23 + 3/13*w05^22 - 21/13*w05^21 - 7/13*w05^20 + 6/13*w05^19 + 20/13*w05^18 - 4/13*w05^17 - 15/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 - 15/13*w05^11 - 4/13*w05^10 + 20/13*w05^9 + 6/13*w05^8 - 7/13*w05^7 - 21/13*w05^6 + 3/13*w05^5 + 14/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (2/13*w05^11 + 5/13*w05^10 - 8/13*w05^9 + 7/13*w05^8 - 2/13*w05^7 - 7/13*w05^6 + 7/13*w05^5 + 2/13*w05^4 - 7/13*w05^3 + 8/13*w05^2 - 5/13*w05 - 2/13) * G23 + (2/13*w05^23 + 7/13*w05^22 - 3/13*w05^21 - 3/13*w05^20 - 2/13*w05^19 - 4/13*w05^18 + 8/13*w05^17 + 1/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 - 1/13*w05^11 - 8/13*w05^10 + 4/13*w05^9 + 2/13*w05^8 + 3/13*w05^7 + 3/13*w05^6 - 7/13*w05^5 - 2/13*w05^4 + w05 + 1) * hf) (by norm_num)
    · rcases sq_split (show w04 ^ 2 = (w05 ^ 11) ^ 2 by linear_combination t04) with h04 | h04
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-2/13*w05^11 + 5/13*w05^10 + 8/13*w05^9 + 7/13*w05^8 + 2/13*w05^7 - 7/13*w05^6 - 7/13*w05^5 + 2/13*w05^4 + 7/13*w05^3 + 8/13*w05^2 + 5/13*w05 - 2/13) * G23 + (-2/13*w05^23 + 7/13*w05^22 + 3/13*w05^21 - 3/13*w05^20 + 2/13*w05^19 - 4/13*w05^18 - 8/13*w05^17 + 1/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 + 1/13*w05^11 - 8/13*w05^10 - 4/13*w05^9 + 2/13*w05^8 - 3/13*w05^7 + 3/13*w05^6 + 7/13*w05^5 - 2/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-14/13*w05^11 + 17/13*w05^10 + 4/13*w05^9 + 3/13*w05^8 - 12/13*w05^7 - 3/13*w05^6 + 3/13*w05^5 + 12/13*w05^4 - 3/13*w05^3 - 4/13*w05^2 - 17/13*w05 + 14/13) * G23 + (-14/13*w05^23 + 3/13*w05^22 + 21/13*w05^21 - 7/13*w05^20 - 6/13*w05^19 + 20/13*w05^18 + 4/13*w05^17 - 15/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 + 15/13*w05^11 - 4/13*w05^10 - 20/13*w05^9 + 6/13*w05^8 + 7/13*w05^7 - 21/13*w05^6 - 3/13*w05^5 + 14/13*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-10/13*w05^11 - 7/13*w05^10 - 4/13*w05^9 - 1/13*w05^8 + 2/13*w05^7 + 5/13*w05^6 - 5/13*w05^5 - 2/13*w05^4 + 1/13*w05^3 + 4/13*w05^2 + 7/13*w05 + 10/13) * G23 + (-10/13*w05^23 + 3/13*w05^22 + 3/13*w05^21 - 7/13*w05^20 + 6/13*w05^19 - 4/13*w05^18 - 4/13*w05^17 + 9/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 + 9/13*w05^11 - 4/13*w05^10 - 4/13*w05^9 + 6/13*w05^8 - 7/13*w05^7 + 3/13*w05^6 + 3/13*w05^5 - 10/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-2/13*w05^11 - 3/13*w05^10 - 4/13*w05^9 + 3/13*w05^8 + 1/13*w05^6 + 1/13*w05^5 + 3/13*w05^3 - 4/13*w05^2 - 3/13*w05 - 2/13) * G23 + (-2/13*w05^23 - 5/13*w05^22 - 7/13*w05^21 - 3/13*w05^20 - 2/13*w05^19 - 8/13*w05^18 - 4/13*w05^17 - 3/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 + 3/13*w05^11 + 4/13*w05^10 + 8/13*w05^9 + 2/13*w05^8 + 3/13*w05^7 + 7/13*w05^6 + 5/13*w05^5 + 2/13*w05^4 + w05 + 1) * hf) (by norm_num)
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-2/13*w05^11 + 5/13*w05^10 + 8/13*w05^9 + 7/13*w05^8 + 2/13*w05^7 - 7/13*w05^6 - 7/13*w05^5 + 2/13*w05^4 + 7/13*w05^3 + 8/13*w05^2 + 5/13*w05 - 2/13) * G23 + (-2/13*w05^23 + 7/13*w05^22 + 3/13*w05^21 - 3/13*w05^20 + 2/13*w05^19 - 4/13*w05^18 - 8/13*w05^17 + 1/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 + 1/13*w05^11 - 8/13*w05^10 - 4/13*w05^9 + 2/13*w05^8 - 3/13*w05^7 + 3/13*w05^6 + 7/13*w05^5 - 2/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-14/13*w05^11 + 17/13*w05^10 + 4/13*w05^9 + 3/13*w05^8 - 12/13*w05^7 - 3/13*w05^6 + 3/13*w05^5 + 12/13*w05^4 - 3/13*w05^3 - 4/13*w05^2 - 17/13*w05 + 14/13) * G23 + (-14/13*w05^23 + 3/13*w05^22 + 21/13*w05^21 - 7/13*w05^20 - 6/13*w05^19 + 20/13*w05^18 + 4/13*w05^17 - 15/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 + 15/13*w05^11 - 4/13*w05^10 - 20/13*w05^9 + 6/13*w05^8 + 7/13*w05^7 - 21/13*w05^6 - 3/13*w05^5 + 14/13*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (1 : ℂ) * E21 + (-1 : ℂ) * w24 * h02 + (1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-10/13*w05^11 - 7/13*w05^10 - 4/13*w05^9 - 1/13*w05^8 + 2/13*w05^7 + 5/13*w05^6 - 5/13*w05^5 - 2/13*w05^4 + 1/13*w05^3 + 4/13*w05^2 + 7/13*w05 + 10/13) * G23 + (-10/13*w05^23 + 3/13*w05^22 + 3/13*w05^21 - 7/13*w05^20 + 6/13*w05^19 - 4/13*w05^18 - 4/13*w05^17 + 9/13*w05^16 - 1/13*w05^15 - 1/13*w05^14 + 12/13*w05^13 - 1/13*w05^12 + 9/13*w05^11 - 4/13*w05^10 - 4/13*w05^9 + 6/13*w05^8 - 7/13*w05^7 + 3/13*w05^6 + 3/13*w05^5 - 10/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-2/13*w05^11 - 3/13*w05^10 - 4/13*w05^9 + 3/13*w05^8 + 1/13*w05^6 + 1/13*w05^5 + 3/13*w05^3 - 4/13*w05^2 - 3/13*w05 - 2/13) * G23 + (-2/13*w05^23 - 5/13*w05^22 - 7/13*w05^21 - 3/13*w05^20 - 2/13*w05^19 - 8/13*w05^18 - 4/13*w05^17 - 3/13*w05^16 + 1/13*w05^15 - 1/13*w05^14 - 12/13*w05^13 - 1/13*w05^12 + 3/13*w05^11 + 4/13*w05^10 + 8/13*w05^9 + 2/13*w05^8 + 3/13*w05^7 + 7/13*w05^6 + 5/13*w05^5 + 2/13*w05^4 + w05 + 1) * hf) (by norm_num)
  · rcases sq_split (show w03 ^ 2 = (w05 ^ 1) ^ 2 by linear_combination t03) with h03 | h03
    · rcases sq_split (show w04 ^ 2 = (w05 ^ 11) ^ 2 by linear_combination t04) with h04 | h04
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (174/689*w05^11 + 231/689*w05^10 + 2/689*w05^9 + 33/689*w05^8 + 220/689*w05^7 + 69/689*w05^6 - 69/689*w05^5 - 220/689*w05^4 - 33/689*w05^3 - 2/689*w05^2 - 231/689*w05 - 174/689) * G23 + (174/689*w05^23 + 57/689*w05^22 - 229/689*w05^21 - 11/53*w05^20 + 10/53*w05^19 - 96/689*w05^18 + 122/689*w05^17 + 5/689*w05^16 - 25/53*w05^15 - 1/53*w05^14 + 52/53*w05^13 - 25/53*w05^12 + 5/689*w05^11 + 122/689*w05^10 - 96/689*w05^9 + 10/53*w05^8 - 11/53*w05^7 - 229/689*w05^6 + 57/689*w05^5 + 174/689*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-10/13*w05^11 + 7/13*w05^10 + 22/13*w05^9 + 1/13*w05^8 + 2/13*w05^7 + 21/13*w05^6 + 21/13*w05^5 + 2/13*w05^4 + 1/13*w05^3 + 22/13*w05^2 + 7/13*w05 - 10/13) * G23 + (-10/13*w05^23 - 3/13*w05^22 + 29/13*w05^21 + 33/13*w05^20 + 6/13*w05^19 + 4/13*w05^18 + 2/13*w05^17 - 15/13*w05^16 + 25/13*w05^15 + 27/13*w05^14 - 40/13*w05^13 - 25/13*w05^12 + 15/13*w05^11 - 2/13*w05^10 - 4/13*w05^9 - 6/13*w05^8 - 33/13*w05^7 - 29/13*w05^6 + 3/13*w05^5 + 10/13*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-226/1027*w05^11 - 319/1027*w05^10 - 370/1027*w05^9 - 197/1027*w05^8 - 216/1027*w05^7 - 37/1027*w05^6 - 37/1027*w05^5 - 216/1027*w05^4 - 197/1027*w05^3 - 370/1027*w05^2 - 319/1027*w05 - 226/1027) * G23 + (-226/1027*w05^23 - 93/1027*w05^22 - 51/1027*w05^21 + 399/1027*w05^20 + 74/1027*w05^19 + 4/1027*w05^18 + 186/1027*w05^17 - 25/1027*w05^16 - 111/1027*w05^15 - 631/1027*w05^14 + 396/1027*w05^13 - 111/1027*w05^12 - 25/1027*w05^11 + 186/1027*w05^10 + 4/1027*w05^9 + 74/1027*w05^8 + 399/1027*w05^7 - 51/1027*w05^6 - 93/1027*w05^5 - 226/1027*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (6/65*w05^11 + 3/13*w05^10 + 2/65*w05^9 + 21/65*w05^8 - 6/65*w05^7 + 1/13*w05^6 - 1/13*w05^5 + 6/65*w05^4 - 21/65*w05^3 - 2/65*w05^2 - 3/13*w05 - 6/65) * G23 + (6/65*w05^23 + 21/65*w05^22 + 17/65*w05^21 + 17/65*w05^20 - 6/65*w05^19 - 12/65*w05^18 - 14/65*w05^17 - 3/5*w05^16 - 19/65*w05^15 - 33/65*w05^14 - 32/65*w05^13 + 19/65*w05^12 + 3/5*w05^11 + 14/65*w05^10 + 12/65*w05^9 + 6/65*w05^8 - 17/65*w05^7 - 17/65*w05^6 - 21/65*w05^5 - 6/65*w05^4 + w05 + 1) * hf) (by norm_num)
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (174/689*w05^11 + 231/689*w05^10 + 2/689*w05^9 + 33/689*w05^8 + 220/689*w05^7 + 69/689*w05^6 - 69/689*w05^5 - 220/689*w05^4 - 33/689*w05^3 - 2/689*w05^2 - 231/689*w05 - 174/689) * G23 + (174/689*w05^23 + 57/689*w05^22 - 229/689*w05^21 - 11/53*w05^20 + 10/53*w05^19 - 96/689*w05^18 + 122/689*w05^17 + 5/689*w05^16 - 25/53*w05^15 - 1/53*w05^14 + 52/53*w05^13 - 25/53*w05^12 + 5/689*w05^11 + 122/689*w05^10 - 96/689*w05^9 + 10/53*w05^8 - 11/53*w05^7 - 229/689*w05^6 + 57/689*w05^5 + 174/689*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-10/13*w05^11 + 7/13*w05^10 + 22/13*w05^9 + 1/13*w05^8 + 2/13*w05^7 + 21/13*w05^6 + 21/13*w05^5 + 2/13*w05^4 + 1/13*w05^3 + 22/13*w05^2 + 7/13*w05 - 10/13) * G23 + (-10/13*w05^23 - 3/13*w05^22 + 29/13*w05^21 + 33/13*w05^20 + 6/13*w05^19 + 4/13*w05^18 + 2/13*w05^17 - 15/13*w05^16 + 25/13*w05^15 + 27/13*w05^14 - 40/13*w05^13 - 25/13*w05^12 + 15/13*w05^11 - 2/13*w05^10 - 4/13*w05^9 - 6/13*w05^8 - 33/13*w05^7 - 29/13*w05^6 + 3/13*w05^5 + 10/13*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (-1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-226/1027*w05^11 - 319/1027*w05^10 - 370/1027*w05^9 - 197/1027*w05^8 - 216/1027*w05^7 - 37/1027*w05^6 - 37/1027*w05^5 - 216/1027*w05^4 - 197/1027*w05^3 - 370/1027*w05^2 - 319/1027*w05 - 226/1027) * G23 + (-226/1027*w05^23 - 93/1027*w05^22 - 51/1027*w05^21 + 399/1027*w05^20 + 74/1027*w05^19 + 4/1027*w05^18 + 186/1027*w05^17 - 25/1027*w05^16 - 111/1027*w05^15 - 631/1027*w05^14 + 396/1027*w05^13 - 111/1027*w05^12 - 25/1027*w05^11 + 186/1027*w05^10 + 4/1027*w05^9 + 74/1027*w05^8 + 399/1027*w05^7 - 51/1027*w05^6 - 93/1027*w05^5 - 226/1027*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (6/65*w05^11 + 3/13*w05^10 + 2/65*w05^9 + 21/65*w05^8 - 6/65*w05^7 + 1/13*w05^6 - 1/13*w05^5 + 6/65*w05^4 - 21/65*w05^3 - 2/65*w05^2 - 3/13*w05 - 6/65) * G23 + (6/65*w05^23 + 21/65*w05^22 + 17/65*w05^21 + 17/65*w05^20 - 6/65*w05^19 - 12/65*w05^18 - 14/65*w05^17 - 3/5*w05^16 - 19/65*w05^15 - 33/65*w05^14 - 32/65*w05^13 + 19/65*w05^12 + 3/5*w05^11 + 14/65*w05^10 + 12/65*w05^9 + 6/65*w05^8 - 17/65*w05^7 - 17/65*w05^6 - 21/65*w05^5 - 6/65*w05^4 + w05 + 1) * hf) (by norm_num)
    · rcases sq_split (show w04 ^ 2 = (w05 ^ 11) ^ 2 by linear_combination t04) with h04 | h04
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-6/65*w05^11 + 3/13*w05^10 - 2/65*w05^9 + 21/65*w05^8 + 6/65*w05^7 + 1/13*w05^6 + 1/13*w05^5 + 6/65*w05^4 + 21/65*w05^3 - 2/65*w05^2 + 3/13*w05 - 6/65) * G23 + (-6/65*w05^23 + 21/65*w05^22 - 17/65*w05^21 + 17/65*w05^20 + 6/65*w05^19 - 12/65*w05^18 + 14/65*w05^17 - 3/5*w05^16 + 19/65*w05^15 - 33/65*w05^14 + 32/65*w05^13 + 19/65*w05^12 - 3/5*w05^11 + 14/65*w05^10 - 12/65*w05^9 + 6/65*w05^8 + 17/65*w05^7 - 17/65*w05^6 + 21/65*w05^5 - 6/65*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (226/1027*w05^11 - 319/1027*w05^10 + 370/1027*w05^9 - 197/1027*w05^8 + 216/1027*w05^7 - 37/1027*w05^6 + 37/1027*w05^5 - 216/1027*w05^4 + 197/1027*w05^3 - 370/1027*w05^2 + 319/1027*w05 - 226/1027) * G23 + (226/1027*w05^23 - 93/1027*w05^22 + 51/1027*w05^21 + 399/1027*w05^20 - 74/1027*w05^19 + 4/1027*w05^18 - 186/1027*w05^17 - 25/1027*w05^16 + 111/1027*w05^15 - 631/1027*w05^14 - 396/1027*w05^13 - 111/1027*w05^12 + 25/1027*w05^11 + 186/1027*w05^10 - 4/1027*w05^9 + 74/1027*w05^8 - 399/1027*w05^7 - 51/1027*w05^6 + 93/1027*w05^5 - 226/1027*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (-1 : ℂ) * E1 + (-1 : ℂ) * w14 * h04 + (1 : ℂ) * w12 * h02 + (-1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (10/13*w05^11 + 7/13*w05^10 - 22/13*w05^9 + 1/13*w05^8 - 2/13*w05^7 + 21/13*w05^6 - 21/13*w05^5 + 2/13*w05^4 - 1/13*w05^3 + 22/13*w05^2 - 7/13*w05 - 10/13) * G23 + (10/13*w05^23 - 3/13*w05^22 - 29/13*w05^21 + 33/13*w05^20 - 6/13*w05^19 + 4/13*w05^18 - 2/13*w05^17 - 15/13*w05^16 - 25/13*w05^15 + 27/13*w05^14 + 40/13*w05^13 - 25/13*w05^12 - 15/13*w05^11 - 2/13*w05^10 + 4/13*w05^9 - 6/13*w05^8 + 33/13*w05^7 - 29/13*w05^6 - 3/13*w05^5 + 10/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-174/689*w05^11 + 231/689*w05^10 - 2/689*w05^9 + 33/689*w05^8 - 220/689*w05^7 + 69/689*w05^6 + 69/689*w05^5 - 220/689*w05^4 + 33/689*w05^3 - 2/689*w05^2 + 231/689*w05 - 174/689) * G23 + (-174/689*w05^23 + 57/689*w05^22 + 229/689*w05^21 - 11/53*w05^20 - 10/53*w05^19 - 96/689*w05^18 - 122/689*w05^17 + 5/689*w05^16 + 25/53*w05^15 - 1/53*w05^14 - 52/53*w05^13 - 25/53*w05^12 - 5/689*w05^11 + 122/689*w05^10 + 96/689*w05^9 + 10/53*w05^8 + 11/53*w05^7 - 229/689*w05^6 - 57/689*w05^5 + 174/689*w05^4 + w05 + 1) * hf) (by norm_num)
      · rcases sq_split (show w12 ^ 2 = (w05 ^ 3) ^ 2 by linear_combination t12) with h12 | h12
        · have x14 : w14 = w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = -w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (-w05 ^ 23) * w05 ^ 4 := by
              linear_combination (-1 : ℂ) * E37 + (-1 : ℂ) * w34 * x14 + (1 : ℂ) * h03 + (1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = -w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (-w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (w05 ^ 6) * w05 ^ 3 := by
              linear_combination (1 : ℂ) * E57 + (-1 : ℂ) * w13 * h12 + (1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = -w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (-w05 ^ 6) * w05 ^ 6 := by
              linear_combination (-1 : ℂ) * E30 + (-1 : ℂ) * w23 * x13 + (1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-6/65*w05^11 + 3/13*w05^10 - 2/65*w05^9 + 21/65*w05^8 + 6/65*w05^7 + 1/13*w05^6 + 1/13*w05^5 + 6/65*w05^4 + 21/65*w05^3 - 2/65*w05^2 + 3/13*w05 - 6/65) * G23 + (-6/65*w05^23 + 21/65*w05^22 - 17/65*w05^21 + 17/65*w05^20 + 6/65*w05^19 - 12/65*w05^18 + 14/65*w05^17 - 3/5*w05^16 + 19/65*w05^15 - 33/65*w05^14 + 32/65*w05^13 + 19/65*w05^12 - 3/5*w05^11 + 14/65*w05^10 - 12/65*w05^9 + 6/65*w05^8 + 17/65*w05^7 - 17/65*w05^6 + 21/65*w05^5 - 6/65*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (226/1027*w05^11 - 319/1027*w05^10 + 370/1027*w05^9 - 197/1027*w05^8 + 216/1027*w05^7 - 37/1027*w05^6 + 37/1027*w05^5 - 216/1027*w05^4 + 197/1027*w05^3 - 370/1027*w05^2 + 319/1027*w05 - 226/1027) * G23 + (226/1027*w05^23 - 93/1027*w05^22 + 51/1027*w05^21 + 399/1027*w05^20 - 74/1027*w05^19 + 4/1027*w05^18 - 186/1027*w05^17 - 25/1027*w05^16 + 111/1027*w05^15 - 631/1027*w05^14 - 396/1027*w05^13 - 111/1027*w05^12 + 25/1027*w05^11 + 186/1027*w05^10 - 4/1027*w05^9 + 74/1027*w05^8 - 399/1027*w05^7 - 51/1027*w05^6 + 93/1027*w05^5 - 226/1027*w05^4 + w05 + 1) * hf) (by norm_num)
        · have x14 : w14 = -w05 ^ 4 := by
            have hx : w14 * w05 ^ 11 = (-w05 ^ 4) * w05 ^ 11 := by
              linear_combination (1 : ℂ) * E1 + (1 : ℂ) * w14 * h04 + (-1 : ℂ) * w12 * h02 + (1 : ℂ) * w05 ^ 12 * h12
            exact mul_right_cancel₀ (pow_ne_zero 11 n05) hx
          have x34 : w34 = w05 ^ 23 := by
            have hx : w34 * w05 ^ 4 = (w05 ^ 23) * w05 ^ 4 := by
              linear_combination (1 : ℂ) * E37 + (1 : ℂ) * w34 * x14 + (-1 : ℂ) * h03 + (-1 : ℂ) * w05 * qf
            exact mul_right_cancel₀ (pow_ne_zero 4 n05) hx
          have x24 : w24 = w05 ^ 12 := by
            have hx : w24 * w05 ^ 12 = (w05 ^ 12) * w05 ^ 12 := by
              linear_combination (-1 : ℂ) * E21 + (1 : ℂ) * w24 * h02 + (-1 : ℂ) * w34 * h03 + (1 : ℂ) * w05 * x34
            exact mul_right_cancel₀ (pow_ne_zero 12 n05) hx
          have x13 : w13 = -w05 ^ 6 := by
            have hx : w13 * w05 ^ 3 = (-w05 ^ 6) * w05 ^ 3 := by
              linear_combination (-1 : ℂ) * E57 + (1 : ℂ) * w13 * h12 + (-1 : ℂ) * w34 * x24 + (-1 : ℂ) * w05 ^ 12 * x34 + (-1 : ℂ) * w05 ^ 9 * qf
            exact mul_right_cancel₀ (pow_ne_zero 3 n05) hx
          have x23 : w23 = w05 ^ 6 := by
            have hx : w23 * w05 ^ 6 = (w05 ^ 6) * w05 ^ 6 := by
              linear_combination (1 : ℂ) * E30 + (1 : ℂ) * w23 * x13 + (-1 : ℂ) * h02
            exact mul_right_cancel₀ (pow_ne_zero 6 n05) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow26_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (10/13*w05^11 + 7/13*w05^10 - 22/13*w05^9 + 1/13*w05^8 - 2/13*w05^7 + 21/13*w05^6 - 21/13*w05^5 + 2/13*w05^4 - 1/13*w05^3 + 22/13*w05^2 - 7/13*w05 - 10/13) * G23 + (10/13*w05^23 - 3/13*w05^22 - 29/13*w05^21 + 33/13*w05^20 - 6/13*w05^19 + 4/13*w05^18 - 2/13*w05^17 - 15/13*w05^16 - 25/13*w05^15 + 27/13*w05^14 + 40/13*w05^13 - 25/13*w05^12 - 15/13*w05^11 - 2/13*w05^10 + 4/13*w05^9 - 6/13*w05^8 + 33/13*w05^7 - 29/13*w05^6 - 3/13*w05^5 + 10/13*w05^4 - w05 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-174/689*w05^11 + 231/689*w05^10 - 2/689*w05^9 + 33/689*w05^8 - 220/689*w05^7 + 69/689*w05^6 + 69/689*w05^5 - 220/689*w05^4 + 33/689*w05^3 - 2/689*w05^2 + 231/689*w05 - 174/689) * G23 + (-174/689*w05^23 + 57/689*w05^22 + 229/689*w05^21 - 11/53*w05^20 - 10/53*w05^19 - 96/689*w05^18 - 122/689*w05^17 + 5/689*w05^16 + 25/53*w05^15 - 1/53*w05^14 - 52/53*w05^13 - 25/53*w05^12 - 5/689*w05^11 + 122/689*w05^10 + 96/689*w05^9 + 10/53*w05^8 + 11/53*w05^7 - 229/689*w05^6 - 57/689*w05^5 + 174/689*w05^4 + w05 + 1) * hf) (by norm_num)

/-- The mask of the third class of this shape. -/
def maskK27 : Mask := 19966792832064260694624258

theorem maskK27_mem : maskK27 ∈ censusRest := by decide

theorem not_supports_k27 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hsup : Supports p maskK27) : False := by
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
  have P1 : Psi (p 2) (p 4) (p 0) (p 1) = 0 := by
    have h := hsup 1 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 1 = ((0, 1), (2, 4)) from by decide)] at h
  have EQ1 : normW p 0 2 * normW p 1 2 = normW p 0 4 * normW p 1 4 :=
    witness_monomial S20 S21 S40 S41 (hC 2 0 (by decide)) (hC 2 1 (by decide)) (hC 4 0 (by decide)) (hC 4 1 (by decide)) (cell_bridge hsne htne 2 4 0 1 P1)
  have P11 : Psi (p 4) (p 5) (p 0) (p 2) = 0 := by
    have h := hsup 11 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 11 = ((0, 2), (4, 5)) from by decide)] at h
  have EQ11 : normW p 0 4 * normW p 2 4 = normW p 0 5 * normW p 2 5 :=
    witness_monomial S40 S42 S50 S52 (hC 4 0 (by decide)) (hC 4 2 (by decide)) (hC 5 0 (by decide)) (hC 5 2 (by decide)) (cell_bridge hsne htne 4 5 0 2 P11)
  have P14 : Psi (p 1) (p 5) (p 0) (p 3) = 0 := by
    have h := hsup 14 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 14 = ((0, 3), (1, 5)) from by decide)] at h
  have EQ14 : normW p 1 3 = normW p 0 5 * normW p 3 5 := by
    have k := witness_monomial S10 S13 S50 S53 (hC 1 0 (by decide)) (hC 1 3 (by decide)) (hC 5 0 (by decide)) (hC 5 3 (by decide)) (cell_bridge hsne htne 1 5 0 3 P14)
    rwa [hw01, one_mul] at k
  have P21 : Psi (p 2) (p 3) (p 0) (p 4) = 0 := by
    have h := hsup 21 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 21 = ((0, 4), (2, 3)) from by decide)] at h
  have EQ21 : normW p 0 2 * normW p 2 4 = normW p 0 3 * normW p 3 4 :=
    witness_monomial S20 S24 S30 S34 (hC 2 0 (by decide)) (hC 2 4 (by decide)) (hC 3 0 (by decide)) (hC 3 4 (by decide)) (cell_bridge hsne htne 2 3 0 4 P21)
  have P24 : Psi (p 1) (p 2) (p 0) (p 5) = 0 := by
    have h := hsup 24 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 24 = ((0, 5), (1, 2)) from by decide)] at h
  have EQ24 : normW p 1 5 = normW p 0 2 * normW p 2 5 := by
    have k := witness_monomial S10 S15 S20 S25 (hC 1 0 (by decide)) (hC 1 5 (by decide)) (hC 2 0 (by decide)) (hC 2 5 (by decide)) (cell_bridge hsne htne 1 2 0 5 P24)
    rwa [hw01, one_mul] at k
  have P30 : Psi (p 0) (p 3) (p 1) (p 2) = 0 := by
    have h := hsup 30 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 30 = ((1, 2), (0, 3)) from by decide)] at h
  have EQ30 : normW p 0 2 = normW p 1 3 * normW p 2 3 := by
    have k := witness_monomial S01 S02 S31 S32 (hC 0 1 (by decide)) (hC 0 2 (by decide)) (hC 3 1 (by decide)) (hC 3 2 (by decide)) (cell_bridge hsne htne 0 3 1 2 P30)
    rwa [hw01, one_mul] at k
  have P37 : Psi (p 0) (p 4) (p 1) (p 3) = 0 := by
    have h := hsup 37 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 37 = ((1, 3), (0, 4)) from by decide)] at h
  have EQ37 : normW p 0 3 = normW p 1 4 * normW p 3 4 := by
    have k := witness_monomial S01 S03 S41 S43 (hC 0 1 (by decide)) (hC 0 3 (by decide)) (hC 4 1 (by decide)) (hC 4 3 (by decide)) (cell_bridge hsne htne 0 4 1 3 P37)
    rwa [hw01, one_mul] at k
  have P46 : Psi (p 2) (p 5) (p 1) (p 4) = 0 := by
    have h := hsup 46 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 46 = ((1, 4), (2, 5)) from by decide)] at h
  have EQ46 : normW p 1 2 * normW p 2 4 = normW p 1 5 * normW p 4 5 :=
    witness_monomial S21 S24 S51 S54 (hC 2 1 (by decide)) (hC 2 4 (by decide)) (hC 5 1 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 2 5 1 4 P46)
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
  have P65 : Psi (p 3) (p 5) (p 2) (p 4) = 0 := by
    have h := hsup 65 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 65 = ((2, 4), (3, 5)) from by decide)] at h
  have EQ65 : normW p 2 3 * normW p 3 4 = normW p 2 5 * normW p 4 5 :=
    witness_monomial S32 S34 S52 S54 (hC 3 2 (by decide)) (hC 3 4 (by decide)) (hC 5 2 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 3 5 2 4 P65)
  have P69 : Psi (p 1) (p 3) (p 2) (p 5) = 0 := by
    have h := hsup 69 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 69 = ((2, 5), (1, 3)) from by decide)] at h
  have EQ69 : normW p 1 2 * normW p 1 5 = normW p 2 3 * normW p 3 5 :=
    witness_monomial S12 S15 S32 S35 (hC 1 2 (by decide)) (hC 1 5 (by decide)) (hC 3 2 (by decide)) (hC 3 5 (by decide)) (cell_bridge hsne htne 1 3 2 5 P69)
  have P74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hsup 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have EQ74 : normW p 0 3 * normW p 0 4 = normW p 3 5 * normW p 4 5 :=
    witness_monomial S03 S04 S53 S54 (hC 0 3 (by decide)) (hC 0 4 (by decide)) (hC 5 3 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 0 5 3 4 P74)
  have P79 : Psi (p 0) (p 2) (p 3) (p 5) = 0 := by
    have h := hsup 79 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 79 = ((3, 5), (0, 2)) from by decide)] at h
  have EQ79 : normW p 0 3 * normW p 0 5 = normW p 2 3 * normW p 2 5 :=
    witness_monomial S03 S05 S23 S25 (hC 0 3 (by decide)) (hC 0 5 (by decide)) (hC 2 3 (by decide)) (hC 2 5 (by decide)) (cell_bridge hsne htne 0 2 3 5 P79)
  have P84 : Psi (p 0) (p 1) (p 4) (p 5) = 0 := by
    have h := hsup 84 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 84 = ((4, 5), (0, 1)) from by decide)] at h
  have EQ84 : normW p 0 4 * normW p 0 5 = normW p 1 4 * normW p 1 5 :=
    witness_monomial S04 S05 S14 S15 (hC 0 4 (by decide)) (hC 0 5 (by decide)) (hC 1 4 (by decide)) (hC 1 5 (by decide)) (cell_bridge hsne htne 0 1 4 5 P84)
  have hncol : ¬ Collinear3 (p 0) (p 1) (p 3) :=
    ncol_of_gp hgp (by decide) (by decide) (by decide)
  have hYC3 : normY p 3 ≠ normC p 3 := by
    intro h
    apply hncol
    apply collinear_of_cross_eq
    rw [normY_sub hsne 3 0, normC_sub htne 3 0, hY0, hC0, h]
    ring
  have nc1 : normW p 0 3 ≠ 1 := by
    intro h
    apply hYC3
    have k := S03
    rw [h, hY0, hC0] at k
    linear_combination -k
  have nc2 : normW p 1 3 ≠ 1 := by
    intro h
    apply hYC3
    have k := S13
    rw [h, hY1, hC1] at k
    linear_combination -k
  have nc3 : normW p 0 3 ≠ normW p 1 3 := by
    intro h
    apply hYC3
    have k1 := S03
    have k2 := S13
    rw [← h] at k2
    rw [hY0, hC0] at k1
    rw [hY1, hC1] at k2
    have hw : normW p 0 3 = 1 := by linear_combination k1 - k2
    rw [hw] at k1
    linear_combination -k1
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
  have g23 : normY p 2 - normY p 3 = normW p 2 3 * (normC p 2 - normC p 3) := S23
  exact core_class27 (normW p 0 2) (normW p 0 3) (normW p 0 4) (normW p 0 5) (normW p 1 2) (normW p 1 3) (normW p 1 4) (normW p 1 5) (normW p 2 3) (normW p 2 4) (normW p 2 5) (normW p 3 4) (normW p 3 5) (normW p 4 5)
    (normY p 2) (normC p 2) (normY p 3) (normC p 3)
    N02 N03 N04 N05 N12 N13 N14 N15 N23 N24 N25 N34 N35 N45
    EQ1 EQ11 EQ14 EQ21 EQ24 EQ30 EQ37 EQ46 EQ53 EQ57 EQ65 EQ69 EQ74 EQ79 EQ84
    u2 v2 u3 v3 g23 nc1 nc2 nc3

theorem not_carries_k27 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK27) : False :=
  not_supports_k27 p hgp (supports_of_carries hc)



end QB12

end DistinctCircumradii

#print axioms DistinctCircumradii.QB12.cellPsi_eq
#print axioms DistinctCircumradii.QB12.maskK31_mem
#print axioms DistinctCircumradii.QB12.collinear_of_cross_eq
#print axioms DistinctCircumradii.QB12.div_mul_cancel_ne
#print axioms DistinctCircumradii.QB12.normY_sub
#print axioms DistinctCircumradii.QB12.normC_sub
#print axioms DistinctCircumradii.QB12.normY_zero
#print axioms DistinctCircumradii.QB12.normC_zero
#print axioms DistinctCircumradii.QB12.normY_one
#print axioms DistinctCircumradii.QB12.normC_one
#print axioms DistinctCircumradii.QB12.normY_sub_ne
#print axioms DistinctCircumradii.QB12.normC_sub_ne
#print axioms DistinctCircumradii.QB12.normW_spec
#print axioms DistinctCircumradii.QB12.normW_spec'
#print axioms DistinctCircumradii.QB12.normW_ne
#print axioms DistinctCircumradii.QB12.cell_bridge
#print axioms DistinctCircumradii.QB12.witness_monomial
#print axioms DistinctCircumradii.QB12.sq_split
#print axioms DistinctCircumradii.QB12.pow22_split
#print axioms DistinctCircumradii.QB12.pow26_split
#print axioms DistinctCircumradii.QB12.pair_relation
#print axioms DistinctCircumradii.QB12.core_class27
#print axioms DistinctCircumradii.QB12.maskK27_mem
#print axioms DistinctCircumradii.QB12.not_supports_k27
#print axioms DistinctCircumradii.QB12.not_carries_k27
