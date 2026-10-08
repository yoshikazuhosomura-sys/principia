import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（枝分かれの議論）：名前空間 `QB11` の k34

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

namespace QB11

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

set_option maxHeartbeats 20000000 in
/-- **The second class of the same shape is not supported either.** -/
theorem core_class34
    (w02 w03 w04 w05 w12 w13 w14 w15 w23 w24 w25 w34 w35 w45 : ℂ)
    (Y2 C2 Y3 C3 : ℂ)
    (n02 : w02 ≠ 0) (n03 : w03 ≠ 0) (n04 : w04 ≠ 0) (n05 : w05 ≠ 0)
    (n12 : w12 ≠ 0) (n13 : w13 ≠ 0) (n14 : w14 ≠ 0) (n15 : w15 ≠ 0)
    (n23 : w23 ≠ 0) (n24 : w24 ≠ 0) (n25 : w25 ≠ 0) (n34 : w34 ≠ 0)
    (n35 : w35 ≠ 0) (n45 : w45 ≠ 0)
    (E4 : w03 * w13 = w05 * w15)
    (E6 : w12 = w03 * w23)
    (E17 : w04 * w34 = w05 * w35)
    (E18 : w14 = w02 * w24)
    (E28 : w02 * w25 = w04 * w45)
    (E32 : w02 = w15 * w25)
    (E37 : w03 = w14 * w34)
    (E46 : w12 * w24 = w15 * w45)
    (E51 : w12 * w25 = w13 * w35)
    (E57 : w12 * w13 = w24 * w34)
    (E61 : w02 * w04 = w23 * w34)
    (E71 : w23 * w35 = w24 * w45)
    (E76 : w13 * w14 = w35 * w45)
    (E79 : w03 * w05 = w23 * w25)
    (E84 : w04 * w05 = w14 * w15)
    (u2 : Y2 = w02 * C2) (v2 : 1 - Y2 = w12 * (1 - C2))
    (u3 : Y3 = w03 * C3) (v3 : 1 - Y3 = w13 * (1 - C3))
    (g23 : Y2 - Y3 = w23 * (C2 - C3))
    (nc1 : w03 ≠ 1) (nc2 : w13 ≠ 1) (nc3 : w03 ≠ w13) :
    False := by
  have t12 : w12 ^ 2 = w35 ^ 4 := by
    have hPQ_t12 : w02 * w03 * w04 * w05 * w12 ^ 2 * w13 ^ 2 * w14 * w15 * w23 * w24 * w25 * w34 ^ 2 * w45 = w02 * w03 * w04 * w05 * w13 ^ 2 * w14 * w15 * w23 * w24 * w25 * w34 ^ 2 * w35 ^ 4 * w45 := by
      linear_combination (-w02 * w03 * w04 * w12 ^ 2 * w13 ^ 2 * w14 * w23 * w24 * w25 * w34 ^ 2 * w45) * E4 + (w02 * w03 ^ 2 * w12 ^ 2 * w13 ^ 3 * w14 * w23 * w24 * w25 * w34 * w45) * E17 + (w03 ^ 2 * w05 * w12 ^ 2 * w13 ^ 3 * w14 * w23 * w24 * w25 * w34 * w35 * w45) * E32 + (w03 * w05 * w12 ^ 2 * w13 ^ 3 * w14 * w15 * w23 * w24 * w25 ^ 2 * w34 * w35 * w45) * E37 + (w03 * w05 * w12 * w13 ^ 3 * w14 ^ 2 * w15 * w23 * w24 * w25 * w34 ^ 2 * w35 * w45) * E51 + (w03 * w05 * w13 ^ 3 * w14 ^ 2 * w15 * w23 * w24 * w25 * w34 ^ 2 * w35 ^ 2 * w45) * E57 + (-w03 * w05 * w13 ^ 3 * w14 ^ 2 * w15 * w24 ^ 2 * w25 * w34 ^ 2 * w35 ^ 2 * w45) * E61 + (-w02 * w03 * w04 * w05 * w13 ^ 3 * w14 ^ 2 * w15 * w24 * w25 * w34 ^ 2 * w35 ^ 2) * E71 + (w02 * w03 * w04 * w05 * w13 ^ 2 * w14 * w15 * w23 * w24 * w25 * w34 ^ 2 * w35 ^ 3) * E76
    have hK_t12 : w02 * w03 * w04 * w05 * w13 ^ 2 * w14 * w15 * w23 * w24 * w25 * w34 ^ 2 * w45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n02) (n03)) (n04)) (n05)) (pow_ne_zero 2 n13)) (n14)) (n15)) (n23)) (n24)) (n25)) (pow_ne_zero 2 n34)) (n45)
    exact mul_right_cancel₀ hK_t12 (by linear_combination hPQ_t12)
  have t02 : w02 ^ 2 = w35 ^ 2 := by
    have hPQ_t02 : w02 ^ 2 * w12 * w13 * w14 * w15 * w24 * w25 * w45 = w12 * w13 * w14 * w15 * w24 * w25 * w35 ^ 2 * w45 := by
      linear_combination (-w02 * w12 * w13 * w14 * w15 * w25 * w45) * E18 + (w12 * w13 * w14 ^ 2 * w15 * w25 * w45) * E32 + (-w12 * w13 * w14 ^ 2 * w15 * w25 ^ 2) * E46 + (w12 * w13 * w14 ^ 2 * w15 * w24 * w25) * E51 + (w12 * w13 * w14 * w15 * w24 * w25 * w35) * E76
    have hK_t02 : w12 * w13 * w14 * w15 * w24 * w25 * w45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n12) (n13)) (n14)) (n15)) (n24)) (n25)) (n45)
    exact mul_right_cancel₀ hK_t02 (by linear_combination hPQ_t02)
  have t45 : w45 ^ 2 = (1 : ℂ) := by
    have hPQ_t45 : w03 * w12 * w13 * w14 * w23 * w24 * w34 * w35 * w45 ^ 2 = w03 * w12 * w13 * w14 * w23 * w24 * w34 * w35 := by
      linear_combination (-w12 * w13 * w14 * w24 * w34 * w35 * w45 ^ 2) * E6 + (-w12 ^ 2 * w13 * w24 * w35 * w45 ^ 2) * E37 + (w03 * w12 * w24 * w35 * w45 ^ 2) * E57 + (-w03 * w12 * w24 * w34 * w35 * w45) * E71 + (-w03 * w12 * w23 * w24 * w34 * w35) * E76
    have hK_t45 : w03 * w12 * w13 * w14 * w23 * w24 * w34 * w35 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (n03) (n12)) (n13)) (n14)) (n23)) (n24)) (n34)) (n35)
    exact mul_right_cancel₀ hK_t45 (by linear_combination hPQ_t45)
  have t03 : w03 ^ 2 = w35 ^ 14 := by
    have hPQ_t03 : w02 ^ 5 * w03 ^ 6 * w04 ^ 4 * w05 ^ 4 * w12 ^ 2 * w13 ^ 5 * w14 ^ 7 * w15 ^ 5 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w45 ^ 6 = w02 ^ 5 * w03 ^ 4 * w04 ^ 4 * w05 ^ 4 * w12 ^ 2 * w13 ^ 5 * w14 ^ 7 * w15 ^ 5 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w35 ^ 14 * w45 ^ 6 := by
      linear_combination (-w02 ^ 5 * w03 ^ 6 * w04 ^ 4 * w05 ^ 3 * w12 ^ 2 * w13 ^ 5 * w14 ^ 7 * w15 ^ 4 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w45 ^ 6) * E4 + (-w02 ^ 5 * w03 ^ 7 * w04 ^ 4 * w05 ^ 2 * w12 ^ 2 * w13 ^ 6 * w14 ^ 7 * w15 ^ 3 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w45 ^ 6) * E4 + (-w02 ^ 5 * w03 ^ 8 * w04 ^ 4 * w05 * w12 ^ 2 * w13 ^ 7 * w14 ^ 7 * w15 ^ 2 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w45 ^ 6) * E4 + (w02 ^ 5 * w03 ^ 9 * w04 ^ 3 * w05 * w12 ^ 2 * w13 ^ 8 * w14 ^ 7 * w15 ^ 2 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 5 * w45 ^ 6) * E17 + (w02 ^ 5 * w03 ^ 9 * w04 ^ 2 * w05 ^ 2 * w12 ^ 2 * w13 ^ 8 * w14 ^ 7 * w15 ^ 2 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 4 * w35 * w45 ^ 6) * E17 + (w02 ^ 5 * w03 ^ 9 * w04 * w05 ^ 3 * w12 ^ 2 * w13 ^ 8 * w14 ^ 7 * w15 ^ 2 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 3 * w35 ^ 2 * w45 ^ 6) * E17 + (w02 ^ 5 * w03 ^ 9 * w04 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 6 * w15 ^ 2 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 3 * w35 ^ 3 * w45 ^ 6) * E18 + (w02 ^ 6 * w03 ^ 9 * w04 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 2 * w23 ^ 4 * w24 ^ 5 * w25 ^ 4 * w34 ^ 3 * w35 ^ 3 * w45 ^ 6) * E18 + (w02 ^ 6 * w03 ^ 9 * w04 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 2 * w23 ^ 4 * w24 ^ 6 * w25 ^ 3 * w34 ^ 3 * w35 ^ 3 * w45 ^ 6) * E28 + (w02 ^ 5 * w03 ^ 9 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 2 * w23 ^ 4 * w24 ^ 6 * w25 ^ 3 * w34 ^ 3 * w35 ^ 3 * w45 ^ 7) * E32 + (w02 ^ 4 * w03 ^ 9 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 3 * w23 ^ 4 * w24 ^ 6 * w25 ^ 4 * w34 ^ 3 * w35 ^ 3 * w45 ^ 7) * E32 + (w02 ^ 3 * w03 ^ 9 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 4 * w23 ^ 4 * w24 ^ 6 * w25 ^ 5 * w34 ^ 3 * w35 ^ 3 * w45 ^ 7) * E32 + (w02 ^ 2 * w03 ^ 9 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 5 * w23 ^ 4 * w24 ^ 6 * w25 ^ 6 * w34 ^ 3 * w35 ^ 3 * w45 ^ 7) * E32 + (w02 ^ 2 * w03 ^ 8 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 5 * w15 ^ 6 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 3 * w35 ^ 3 * w45 ^ 7) * E37 + (w02 ^ 2 * w03 ^ 7 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 6 * w15 ^ 6 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 4 * w35 ^ 3 * w45 ^ 7) * E37 + (w02 ^ 2 * w03 ^ 6 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 7 * w15 ^ 6 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 5 * w35 ^ 3 * w45 ^ 7) * E37 + (w02 ^ 2 * w03 ^ 5 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 8 * w15 ^ 6 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 6 * w35 ^ 3 * w45 ^ 7) * E37 + (w02 ^ 2 * w03 ^ 4 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 9 * w15 ^ 6 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 7 * w35 ^ 3 * w45 ^ 7) * E37 + (w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 10 * w15 ^ 6 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 8 * w35 ^ 3 * w45 ^ 7) * E37 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 11 * w15 ^ 5 * w23 ^ 4 * w24 ^ 6 * w25 ^ 7 * w34 ^ 9 * w35 ^ 3 * w45 ^ 6) * E46 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 3 * w13 ^ 8 * w14 ^ 11 * w15 ^ 4 * w23 ^ 4 * w24 ^ 7 * w25 ^ 7 * w34 ^ 9 * w35 ^ 3 * w45 ^ 5) * E46 + (w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 3 * w13 ^ 8 * w14 ^ 11 * w15 ^ 4 * w23 ^ 4 * w24 ^ 8 * w25 ^ 6 * w34 ^ 9 * w35 ^ 3 * w45 ^ 5) * E51 + (w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 9 * w14 ^ 11 * w15 ^ 4 * w23 ^ 4 * w24 ^ 8 * w25 ^ 5 * w34 ^ 9 * w35 ^ 4 * w45 ^ 5) * E51 + (-w02 ^ 2 * w03 ^ 3 * w04 ^ 2 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 ^ 3 * w24 ^ 8 * w25 ^ 5 * w34 ^ 8 * w35 ^ 5 * w45 ^ 5) * E61 + (-w02 ^ 3 * w03 ^ 3 * w04 ^ 3 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 ^ 2 * w24 ^ 8 * w25 ^ 5 * w34 ^ 7 * w35 ^ 5 * w45 ^ 5) * E61 + (-w02 ^ 4 * w03 ^ 3 * w04 ^ 4 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 * w24 ^ 8 * w25 ^ 5 * w34 ^ 6 * w35 ^ 5 * w45 ^ 5) * E61 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 * w24 ^ 7 * w25 ^ 5 * w34 ^ 6 * w35 ^ 5 * w45 ^ 4) * E71 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 ^ 2 * w24 ^ 6 * w25 ^ 5 * w34 ^ 6 * w35 ^ 6 * w45 ^ 3) * E71 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 ^ 3 * w24 ^ 5 * w25 ^ 5 * w34 ^ 6 * w35 ^ 7 * w45 ^ 2) * E71 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 10 * w14 ^ 11 * w15 ^ 4 * w23 ^ 4 * w24 ^ 4 * w25 ^ 5 * w34 ^ 6 * w35 ^ 8 * w45) * E71 + (w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 9 * w14 ^ 10 * w15 ^ 4 * w23 ^ 5 * w24 ^ 4 * w25 ^ 5 * w34 ^ 6 * w35 ^ 9 * w45) * E76 + (w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 8 * w14 ^ 9 * w15 ^ 4 * w23 ^ 5 * w24 ^ 4 * w25 ^ 5 * w34 ^ 6 * w35 ^ 10 * w45 ^ 2) * E76 + (w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 7 * w14 ^ 8 * w15 ^ 4 * w23 ^ 5 * w24 ^ 4 * w25 ^ 5 * w34 ^ 6 * w35 ^ 11 * w45 ^ 3) * E76 + (w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 6 * w14 ^ 7 * w15 ^ 4 * w23 ^ 5 * w24 ^ 4 * w25 ^ 5 * w34 ^ 6 * w35 ^ 12 * w45 ^ 4) * E76 + (w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 5 * w14 ^ 6 * w15 ^ 4 * w23 ^ 5 * w24 ^ 4 * w25 ^ 5 * w34 ^ 6 * w35 ^ 13 * w45 ^ 5) * E76 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 5 * w05 ^ 4 * w12 ^ 2 * w13 ^ 5 * w14 ^ 6 * w15 ^ 4 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w35 ^ 14 * w45 ^ 6) * E79 + (w02 ^ 5 * w03 ^ 4 * w04 ^ 4 * w05 ^ 4 * w12 ^ 2 * w13 ^ 5 * w14 ^ 6 * w15 ^ 4 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w35 ^ 14 * w45 ^ 6) * E84
    have hK_t03 : w02 ^ 5 * w03 ^ 4 * w04 ^ 4 * w05 ^ 4 * w12 ^ 2 * w13 ^ 5 * w14 ^ 7 * w15 ^ 5 * w23 ^ 4 * w24 ^ 4 * w25 ^ 4 * w34 ^ 6 * w45 ^ 6 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 5 n02) (pow_ne_zero 4 n03)) (pow_ne_zero 4 n04)) (pow_ne_zero 4 n05)) (pow_ne_zero 2 n12)) (pow_ne_zero 5 n13)) (pow_ne_zero 7 n14)) (pow_ne_zero 5 n15)) (pow_ne_zero 4 n23)) (pow_ne_zero 4 n24)) (pow_ne_zero 4 n25)) (pow_ne_zero 6 n34)) (pow_ne_zero 6 n45)
    exact mul_right_cancel₀ hK_t03 (by linear_combination hPQ_t03)
  have qf : w35 ^ 22 = (1 : ℂ) := by
    have hPQ_t35 : w02 ^ 7 * w03 ^ 10 * w04 ^ 5 * w05 ^ 6 * w12 ^ 7 * w13 ^ 10 * w14 ^ 12 * w15 ^ 9 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10 = w02 ^ 7 * w03 ^ 10 * w04 ^ 5 * w05 ^ 6 * w12 ^ 7 * w13 ^ 10 * w14 ^ 12 * w15 ^ 9 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w45 ^ 10 := by
      linear_combination (w02 ^ 7 * w03 ^ 9 * w04 ^ 5 * w05 ^ 6 * w12 ^ 7 * w13 ^ 9 * w14 ^ 12 * w15 ^ 9 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E4 + (w02 ^ 7 * w03 ^ 8 * w04 ^ 5 * w05 ^ 7 * w12 ^ 7 * w13 ^ 8 * w14 ^ 12 * w15 ^ 10 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E4 + (w02 ^ 7 * w03 ^ 7 * w04 ^ 5 * w05 ^ 8 * w12 ^ 7 * w13 ^ 7 * w14 ^ 12 * w15 ^ 11 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E4 + (w02 ^ 7 * w03 ^ 6 * w04 ^ 5 * w05 ^ 9 * w12 ^ 7 * w13 ^ 6 * w14 ^ 12 * w15 ^ 12 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E4 + (-w02 ^ 7 * w03 ^ 5 * w04 ^ 5 * w05 ^ 10 * w12 ^ 7 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 7 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E6 + (-w02 ^ 7 * w03 ^ 4 * w04 ^ 5 * w05 ^ 10 * w12 ^ 8 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 6 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E6 + (-w02 ^ 7 * w03 ^ 3 * w04 ^ 5 * w05 ^ 10 * w12 ^ 9 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 5 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 22 * w45 ^ 10) * E6 + (-w02 ^ 7 * w03 ^ 3 * w04 ^ 5 * w05 ^ 9 * w12 ^ 10 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 5 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w35 ^ 21 * w45 ^ 10) * E17 + (-w02 ^ 7 * w03 ^ 3 * w04 ^ 6 * w05 ^ 8 * w12 ^ 10 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 5 * w24 ^ 7 * w25 ^ 7 * w34 ^ 11 * w35 ^ 20 * w45 ^ 10) * E17 + (-w02 ^ 7 * w03 ^ 3 * w04 ^ 7 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 5 * w24 ^ 7 * w25 ^ 7 * w34 ^ 12 * w35 ^ 19 * w45 ^ 10) * E17 + (-w02 ^ 6 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 12 * w15 ^ 13 * w23 ^ 5 * w24 ^ 6 * w25 ^ 7 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E18 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 13 * w15 ^ 13 * w23 ^ 5 * w24 ^ 5 * w25 ^ 7 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E18 + (-w02 ^ 5 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 12 * w23 ^ 5 * w24 ^ 5 * w25 ^ 6 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 6 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 11 * w23 ^ 5 * w24 ^ 5 * w25 ^ 5 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 7 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 10 * w23 ^ 5 * w24 ^ 5 * w25 ^ 4 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 8 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 9 * w23 ^ 5 * w24 ^ 5 * w25 ^ 3 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 9 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 8 * w23 ^ 5 * w24 ^ 5 * w25 ^ 2 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 10 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 7 * w23 ^ 5 * w24 ^ 5 * w25 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 11 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 14 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 13 * w35 ^ 19 * w45 ^ 10) * E32 + (-w02 ^ 12 * w03 ^ 3 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 13 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 12 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 4 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 12 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 11 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 5 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 11 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 10 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 6 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 10 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 9 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 7 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 9 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 8 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 8 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 8 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 7 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 9 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 7 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 6 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 10 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 6 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 5 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 11 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 5 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 4 * w35 ^ 19 * w45 ^ 10) * E37 + (-w02 ^ 12 * w03 ^ 12 * w04 ^ 8 * w05 ^ 7 * w12 ^ 10 * w13 ^ 6 * w14 ^ 4 * w15 ^ 6 * w23 ^ 5 * w24 ^ 5 * w34 ^ 3 * w35 ^ 19 * w45 ^ 10) * E37 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 9 * w13 ^ 6 * w14 ^ 4 * w15 ^ 6 * w23 ^ 5 * w24 ^ 4 * w34 ^ 3 * w35 ^ 19 * w45 ^ 10) * E46 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 8 * w13 ^ 6 * w14 ^ 4 * w15 ^ 7 * w23 ^ 5 * w24 ^ 3 * w34 ^ 3 * w35 ^ 19 * w45 ^ 11) * E46 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 7 * w13 ^ 6 * w14 ^ 4 * w15 ^ 8 * w23 ^ 5 * w24 ^ 2 * w34 ^ 3 * w35 ^ 19 * w45 ^ 12) * E46 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 6 * w13 ^ 6 * w14 ^ 4 * w15 ^ 9 * w23 ^ 5 * w24 * w34 ^ 3 * w35 ^ 19 * w45 ^ 13) * E46 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 5 * w13 ^ 6 * w14 ^ 4 * w15 ^ 10 * w23 ^ 5 * w34 ^ 3 * w35 ^ 19 * w45 ^ 14) * E46 + (-w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 5 * w13 ^ 5 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w34 ^ 3 * w35 ^ 18 * w45 ^ 15) * E51 + (-w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 6 * w13 ^ 4 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w25 * w34 ^ 3 * w35 ^ 17 * w45 ^ 15) * E51 + (-w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 7 * w13 ^ 3 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w25 ^ 2 * w34 ^ 3 * w35 ^ 16 * w45 ^ 15) * E51 + (-w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 8 * w13 ^ 2 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w25 ^ 3 * w34 ^ 3 * w35 ^ 15 * w45 ^ 15) * E51 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 8 * w13 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w25 ^ 4 * w34 ^ 3 * w35 ^ 15 * w45 ^ 15) * E57 + (w02 ^ 12 * w03 ^ 13 * w04 ^ 8 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w24 * w25 ^ 4 * w34 ^ 4 * w35 ^ 15 * w45 ^ 15) * E57 + (w02 ^ 11 * w03 ^ 13 * w04 ^ 7 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w24 ^ 2 * w25 ^ 4 * w34 ^ 5 * w35 ^ 15 * w45 ^ 15) * E61 + (w02 ^ 10 * w03 ^ 13 * w04 ^ 6 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 6 * w24 ^ 2 * w25 ^ 4 * w34 ^ 6 * w35 ^ 15 * w45 ^ 15) * E61 + (w02 ^ 9 * w03 ^ 13 * w04 ^ 5 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 7 * w24 ^ 2 * w25 ^ 4 * w34 ^ 7 * w35 ^ 15 * w45 ^ 15) * E61 + (w02 ^ 8 * w03 ^ 13 * w04 ^ 4 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 8 * w24 ^ 2 * w25 ^ 4 * w34 ^ 8 * w35 ^ 15 * w45 ^ 15) * E61 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 9 * w24 ^ 2 * w25 ^ 4 * w34 ^ 9 * w35 ^ 15 * w45 ^ 15) * E61 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 9 * w24 ^ 2 * w25 ^ 4 * w34 ^ 10 * w35 ^ 14 * w45 ^ 15) * E71 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 8 * w24 ^ 3 * w25 ^ 4 * w34 ^ 10 * w35 ^ 13 * w45 ^ 16) * E71 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 7 * w24 ^ 4 * w25 ^ 4 * w34 ^ 10 * w35 ^ 12 * w45 ^ 17) * E71 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 6 * w24 ^ 5 * w25 ^ 4 * w34 ^ 10 * w35 ^ 11 * w45 ^ 18) * E71 + (w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w24 ^ 6 * w25 ^ 4 * w34 ^ 10 * w35 ^ 10 * w45 ^ 19) * E71 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w14 ^ 4 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 9 * w45 ^ 19) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 * w14 ^ 5 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 8 * w45 ^ 18) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 2 * w14 ^ 6 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 7 * w45 ^ 17) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 3 * w14 ^ 7 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 6 * w45 ^ 16) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 4 * w14 ^ 8 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 5 * w45 ^ 15) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 5 * w14 ^ 9 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 4 * w45 ^ 14) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 6 * w14 ^ 10 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 3 * w45 ^ 13) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 7 * w14 ^ 11 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 ^ 2 * w45 ^ 12) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 8 * w14 ^ 12 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w35 * w45 ^ 11) * E76 + (-w02 ^ 7 * w03 ^ 13 * w04 ^ 3 * w05 ^ 7 * w12 ^ 7 * w13 ^ 9 * w14 ^ 13 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w45 ^ 10) * E76 + (w02 ^ 7 * w03 ^ 12 * w04 ^ 3 * w05 ^ 6 * w12 ^ 7 * w13 ^ 10 * w14 ^ 14 * w15 ^ 11 * w23 ^ 5 * w24 ^ 7 * w25 ^ 4 * w34 ^ 10 * w45 ^ 10) * E79 + (w02 ^ 7 * w03 ^ 11 * w04 ^ 3 * w05 ^ 5 * w12 ^ 7 * w13 ^ 10 * w14 ^ 14 * w15 ^ 11 * w23 ^ 6 * w24 ^ 7 * w25 ^ 5 * w34 ^ 10 * w45 ^ 10) * E79 + (w02 ^ 7 * w03 ^ 10 * w04 ^ 3 * w05 ^ 4 * w12 ^ 7 * w13 ^ 10 * w14 ^ 14 * w15 ^ 11 * w23 ^ 7 * w24 ^ 7 * w25 ^ 6 * w34 ^ 10 * w45 ^ 10) * E79 + (-w02 ^ 7 * w03 ^ 10 * w04 ^ 3 * w05 ^ 4 * w12 ^ 7 * w13 ^ 10 * w14 ^ 13 * w15 ^ 10 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w45 ^ 10) * E84 + (-w02 ^ 7 * w03 ^ 10 * w04 ^ 4 * w05 ^ 5 * w12 ^ 7 * w13 ^ 10 * w14 ^ 12 * w15 ^ 9 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w45 ^ 10) * E84
    have hK_t35 : w02 ^ 7 * w03 ^ 10 * w04 ^ 5 * w05 ^ 6 * w12 ^ 7 * w13 ^ 10 * w14 ^ 12 * w15 ^ 9 * w23 ^ 8 * w24 ^ 7 * w25 ^ 7 * w34 ^ 10 * w45 ^ 10 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 7 n02) (pow_ne_zero 10 n03)) (pow_ne_zero 5 n04)) (pow_ne_zero 6 n05)) (pow_ne_zero 7 n12)) (pow_ne_zero 10 n13)) (pow_ne_zero 12 n14)) (pow_ne_zero 9 n15)) (pow_ne_zero 8 n23)) (pow_ne_zero 7 n24)) (pow_ne_zero 7 n25)) (pow_ne_zero 10 n34)) (pow_ne_zero 10 n45)
    exact mul_right_cancel₀ hK_t35 (by linear_combination hPQ_t35)
  have G23 := pair_relation u2 v2 u3 v3 g23
  rcases sq_split (show w12 ^ 2 = (w35 ^ 2) ^ 2 by linear_combination t12) with h12 | h12
  · rcases sq_split (show w02 ^ 2 = (w35 ^ 1) ^ 2 by linear_combination t02) with h02 | h02
    · rcases sq_split (show w45 ^ 2 = (1 : ℂ) ^ 2 by linear_combination t45) with h45 | h45
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (6/11*w35^9 + 14/11*w35^8 + 10/11*w35^7 + 2/11*w35^6 - 2/11*w35^5 + 6/11*w35^4 + 12/11*w35^3 + 13/11*w35^2 + 6/11*w35 - 1/11) * G23 + (-6/11*w35^25 - 8/11*w35^24 + 10/11*w35^23 + 16/11*w35^22 + 6/11*w35^21 - 14/11*w35^20 - 2*w35^19 + 9/11*w35^18 + 19/11*w35^17 + 8/11*w35^16 - 14/11*w35^15 - 14/11*w35^14 - 3/11*w35^13 + 14/11*w35^12 + 21/11*w35^11 - 15/11*w35^10 - 12/11*w35^9 - 8/11*w35^8 + 8/11*w35^7 + 7/11*w35^6 - 1/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (16/11*w35^9 + 10/11*w35^8 + 10/11*w35^7 - 10/11*w35^6 - 10/11*w35^5 - 16/11*w35^4 + 3/11*w35^2 + 18/11*w35 + 3/11) * G23 + (-16/11*w35^25 - 26/11*w35^24 - 4/11*w35^23 + 26/11*w35^22 + 56/11*w35^21 + 36/11*w35^20 - 10/11*w35^19 - 3*w35^18 - 47/11*w35^17 - 30/11*w35^16 + 8/11*w35^15 + 36/11*w35^14 + 41/11*w35^13 + 30/11*w35^12 - 15/11*w35^11 - 47/11*w35^10 - 40/11*w35^9 - 18/11*w35^8 + 18/11*w35^7 + 21/11*w35^6 + 3/11*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (8/11*w35^9 + 6/11*w35^8 + 16/11*w35^7 + 16/11*w35^6 + 6/11*w35^5 + 8/11*w35^4 - 7/11*w35^2 - 2/11*w35 - 7/11) * G23 + (-8/11*w35^25 + 2/11*w35^24 - 2/11*w35^23 - 2/11*w35^22 + 28/11*w35^21 - 12/11*w35^20 + 10/11*w35^19 - 9/11*w35^18 - 13/11*w35^17 - 2/11*w35^16 - 2/11*w35^15 - 2/11*w35^14 + 9/11*w35^13 + 6/11*w35^12 - 1/11*w35^11 + 21/11*w35^10 - 20/11*w35^9 - 2/11*w35^8 - 2/11*w35^7 - 5/11*w35^6 + 7/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-10/11*w35^9 - 2/11*w35^8 - 8/11*w35^7 - 4/11*w35^6 - 6/11*w35^5 - 6/11*w35^4 - 4/11*w35^3 + 3/11*w35^2 - 2/11*w35 + 1/11) * G23 + (10/11*w35^25 + 12/11*w35^24 - 10/11*w35^21 - 2/11*w35^20 + 2/11*w35^19 - 3/11*w35^18 - 7/11*w35^17 - 4/11*w35^16 + 4/11*w35^15 - 4/11*w35^14 - 7/11*w35^13 - 14/11*w35^12 - 9/11*w35^11 + 9/11*w35^10 + 12/11*w35^9 + 1/11*w35^6 - 1/11*w35^5 + w35 + 1) * hf) (by norm_num)
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (6/11*w35^9 + 14/11*w35^8 + 10/11*w35^7 + 2/11*w35^6 - 2/11*w35^5 + 6/11*w35^4 + 12/11*w35^3 + 13/11*w35^2 + 6/11*w35 - 1/11) * G23 + (-6/11*w35^25 - 8/11*w35^24 + 10/11*w35^23 + 16/11*w35^22 + 6/11*w35^21 - 14/11*w35^20 - 2*w35^19 + 9/11*w35^18 + 19/11*w35^17 + 8/11*w35^16 - 14/11*w35^15 - 14/11*w35^14 - 3/11*w35^13 + 14/11*w35^12 + 21/11*w35^11 - 15/11*w35^10 - 12/11*w35^9 - 8/11*w35^8 + 8/11*w35^7 + 7/11*w35^6 - 1/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (16/11*w35^9 + 10/11*w35^8 + 10/11*w35^7 - 10/11*w35^6 - 10/11*w35^5 - 16/11*w35^4 + 3/11*w35^2 + 18/11*w35 + 3/11) * G23 + (-16/11*w35^25 - 26/11*w35^24 - 4/11*w35^23 + 26/11*w35^22 + 56/11*w35^21 + 36/11*w35^20 - 10/11*w35^19 - 3*w35^18 - 47/11*w35^17 - 30/11*w35^16 + 8/11*w35^15 + 36/11*w35^14 + 41/11*w35^13 + 30/11*w35^12 - 15/11*w35^11 - 47/11*w35^10 - 40/11*w35^9 - 18/11*w35^8 + 18/11*w35^7 + 21/11*w35^6 + 3/11*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (8/11*w35^9 + 6/11*w35^8 + 16/11*w35^7 + 16/11*w35^6 + 6/11*w35^5 + 8/11*w35^4 - 7/11*w35^2 - 2/11*w35 - 7/11) * G23 + (-8/11*w35^25 + 2/11*w35^24 - 2/11*w35^23 - 2/11*w35^22 + 28/11*w35^21 - 12/11*w35^20 + 10/11*w35^19 - 9/11*w35^18 - 13/11*w35^17 - 2/11*w35^16 - 2/11*w35^15 - 2/11*w35^14 + 9/11*w35^13 + 6/11*w35^12 - 1/11*w35^11 + 21/11*w35^10 - 20/11*w35^9 - 2/11*w35^8 - 2/11*w35^7 - 5/11*w35^6 + 7/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-10/11*w35^9 - 2/11*w35^8 - 8/11*w35^7 - 4/11*w35^6 - 6/11*w35^5 - 6/11*w35^4 - 4/11*w35^3 + 3/11*w35^2 - 2/11*w35 + 1/11) * G23 + (10/11*w35^25 + 12/11*w35^24 - 10/11*w35^21 - 2/11*w35^20 + 2/11*w35^19 - 3/11*w35^18 - 7/11*w35^17 - 4/11*w35^16 + 4/11*w35^15 - 4/11*w35^14 - 7/11*w35^13 - 14/11*w35^12 - 9/11*w35^11 + 9/11*w35^10 + 12/11*w35^9 + 1/11*w35^6 - 1/11*w35^5 + w35 + 1) * hf) (by norm_num)
    · rcases sq_split (show w45 ^ 2 = (1 : ℂ) ^ 2 by linear_combination t45) with h45 | h45
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (10/11*w35^9 - 2/11*w35^8 + 8/11*w35^7 - 4/11*w35^6 + 6/11*w35^5 - 6/11*w35^4 + 4/11*w35^3 + 3/11*w35^2 + 2/11*w35 + 1/11) * G23 + (-10/11*w35^25 + 12/11*w35^24 + 10/11*w35^21 - 2/11*w35^20 - 2/11*w35^19 - 3/11*w35^18 + 7/11*w35^17 - 4/11*w35^16 - 4/11*w35^15 - 4/11*w35^14 + 7/11*w35^13 - 14/11*w35^12 + 9/11*w35^11 + 9/11*w35^10 - 12/11*w35^9 + 1/11*w35^6 + 1/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-8/11*w35^9 + 6/11*w35^8 - 16/11*w35^7 + 16/11*w35^6 - 6/11*w35^5 + 8/11*w35^4 - 7/11*w35^2 + 2/11*w35 - 7/11) * G23 + (8/11*w35^25 + 2/11*w35^24 + 2/11*w35^23 - 2/11*w35^22 - 28/11*w35^21 - 12/11*w35^20 - 10/11*w35^19 - 9/11*w35^18 + 13/11*w35^17 - 2/11*w35^16 + 2/11*w35^15 - 2/11*w35^14 - 9/11*w35^13 + 6/11*w35^12 + 1/11*w35^11 + 21/11*w35^10 + 20/11*w35^9 - 2/11*w35^8 + 2/11*w35^7 - 5/11*w35^6 - 7/11*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-16/11*w35^9 + 10/11*w35^8 - 10/11*w35^7 - 10/11*w35^6 + 10/11*w35^5 - 16/11*w35^4 + 3/11*w35^2 - 18/11*w35 + 3/11) * G23 + (16/11*w35^25 - 26/11*w35^24 + 4/11*w35^23 + 26/11*w35^22 - 56/11*w35^21 + 36/11*w35^20 + 10/11*w35^19 - 3*w35^18 + 47/11*w35^17 - 30/11*w35^16 - 8/11*w35^15 + 36/11*w35^14 - 41/11*w35^13 + 30/11*w35^12 + 15/11*w35^11 - 47/11*w35^10 + 40/11*w35^9 - 18/11*w35^8 - 18/11*w35^7 + 21/11*w35^6 - 3/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-6/11*w35^9 + 14/11*w35^8 - 10/11*w35^7 + 2/11*w35^6 + 2/11*w35^5 + 6/11*w35^4 - 12/11*w35^3 + 13/11*w35^2 - 6/11*w35 - 1/11) * G23 + (6/11*w35^25 - 8/11*w35^24 - 10/11*w35^23 + 16/11*w35^22 - 6/11*w35^21 - 14/11*w35^20 + 2*w35^19 + 9/11*w35^18 - 19/11*w35^17 + 8/11*w35^16 + 14/11*w35^15 - 14/11*w35^14 + 3/11*w35^13 + 14/11*w35^12 - 21/11*w35^11 - 15/11*w35^10 + 12/11*w35^9 - 8/11*w35^8 - 8/11*w35^7 + 7/11*w35^6 + 1/11*w35^5 + w35 + 1) * hf) (by norm_num)
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (10/11*w35^9 - 2/11*w35^8 + 8/11*w35^7 - 4/11*w35^6 + 6/11*w35^5 - 6/11*w35^4 + 4/11*w35^3 + 3/11*w35^2 + 2/11*w35 + 1/11) * G23 + (-10/11*w35^25 + 12/11*w35^24 + 10/11*w35^21 - 2/11*w35^20 - 2/11*w35^19 - 3/11*w35^18 + 7/11*w35^17 - 4/11*w35^16 - 4/11*w35^15 - 4/11*w35^14 + 7/11*w35^13 - 14/11*w35^12 + 9/11*w35^11 + 9/11*w35^10 - 12/11*w35^9 + 1/11*w35^6 + 1/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-8/11*w35^9 + 6/11*w35^8 - 16/11*w35^7 + 16/11*w35^6 - 6/11*w35^5 + 8/11*w35^4 - 7/11*w35^2 + 2/11*w35 - 7/11) * G23 + (8/11*w35^25 + 2/11*w35^24 + 2/11*w35^23 - 2/11*w35^22 - 28/11*w35^21 - 12/11*w35^20 - 10/11*w35^19 - 9/11*w35^18 + 13/11*w35^17 - 2/11*w35^16 + 2/11*w35^15 - 2/11*w35^14 - 9/11*w35^13 + 6/11*w35^12 + 1/11*w35^11 + 21/11*w35^10 + 20/11*w35^9 - 2/11*w35^8 + 2/11*w35^7 - 5/11*w35^6 - 7/11*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-16/11*w35^9 + 10/11*w35^8 - 10/11*w35^7 - 10/11*w35^6 + 10/11*w35^5 - 16/11*w35^4 + 3/11*w35^2 - 18/11*w35 + 3/11) * G23 + (16/11*w35^25 - 26/11*w35^24 + 4/11*w35^23 + 26/11*w35^22 - 56/11*w35^21 + 36/11*w35^20 + 10/11*w35^19 - 3*w35^18 + 47/11*w35^17 - 30/11*w35^16 - 8/11*w35^15 + 36/11*w35^14 - 41/11*w35^13 + 30/11*w35^12 + 15/11*w35^11 - 47/11*w35^10 + 40/11*w35^9 - 18/11*w35^8 - 18/11*w35^7 + 21/11*w35^6 - 3/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-6/11*w35^9 + 14/11*w35^8 - 10/11*w35^7 + 2/11*w35^6 + 2/11*w35^5 + 6/11*w35^4 - 12/11*w35^3 + 13/11*w35^2 - 6/11*w35 - 1/11) * G23 + (6/11*w35^25 - 8/11*w35^24 - 10/11*w35^23 + 16/11*w35^22 - 6/11*w35^21 - 14/11*w35^20 + 2*w35^19 + 9/11*w35^18 - 19/11*w35^17 + 8/11*w35^16 + 14/11*w35^15 - 14/11*w35^14 + 3/11*w35^13 + 14/11*w35^12 - 21/11*w35^11 - 15/11*w35^10 + 12/11*w35^9 - 8/11*w35^8 - 8/11*w35^7 + 7/11*w35^6 + 1/11*w35^5 + w35 + 1) * hf) (by norm_num)
  · rcases sq_split (show w02 ^ 2 = (w35 ^ 1) ^ 2 by linear_combination t02) with h02 | h02
    · rcases sq_split (show w45 ^ 2 = (1 : ℂ) ^ 2 by linear_combination t45) with h45 | h45
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (4/253*w35^9 + 36/253*w35^8 + 30/253*w35^7 + 30/253*w35^6 + 36/253*w35^5 + 4/253*w35^4 - 31/253*w35^2 + 54/253*w35 - 31/253) * G23 + (-4/253*w35^25 - 32/253*w35^24 + 2/253*w35^23 - 32/253*w35^22 + 4/253*w35^21 + 60/253*w35^20 - 40/253*w35^19 + 73/253*w35^18 - 39/253*w35^17 + 104/253*w35^16 - 94/253*w35^15 + 60/253*w35^14 + 27/253*w35^13 - 200/253*w35^12 + 85/253*w35^11 + 53/253*w35^10 + 50/253*w35^9 - 116/253*w35^8 + 116/253*w35^7 - 85/253*w35^6 + 31/253*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-218/473*w35^9 + 128/473*w35^8 + 6/473*w35^7 + 146/473*w35^6 - 12/473*w35^5 - 78/473*w35^4 - 140/473*w35^3 - 5/473*w35^2 - 70/473*w35 + 145/473) * G23 + (218/473*w35^25 + 90/473*w35^24 + 84/473*w35^23 - 62/473*w35^22 - 486/473*w35^21 + 6/43*w35^20 + 28/43*w35^19 + 35/473*w35^18 - 3/43*w35^17 - 10/43*w35^16 + 8/43*w35^15 + 6/43*w35^14 - 11/43*w35^13 - 460/473*w35^12 - 49/43*w35^11 + 15/43*w35^10 + 438/473*w35^9 + 70/473*w35^8 - 70/473*w35^7 - 75/473*w35^6 - 145/473*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-14/11*w35^9 + 16/11*w35^8 + 24/11*w35^7 - 12/11*w35^6 - 4/11*w35^5 + 26/11*w35^4 + 12/11*w35^3 - 13/11*w35^2 + 6/11*w35 + 25/11) * G23 + (14/11*w35^25 - 30/11*w35^24 + 6/11*w35^23 + 6/11*w35^22 - 30/11*w35^21 + 50/11*w35^20 - 16/11*w35^19 - 35/11*w35^18 + 23/11*w35^17 - 10/11*w35^16 - 10/11*w35^15 + 12/11*w35^14 + 1/11*w35^13 - 24/11*w35^12 + 17/11*w35^11 + 39/11*w35^10 - 30/11*w35^9 + 6/11*w35^8 + 6/11*w35^7 - 19/11*w35^6 + 25/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-148/253*w35^9 + 144/253*w35^8 - 32/253*w35^7 + 32/253*w35^6 - 144/253*w35^5 + 148/253*w35^4 + 63/253*w35^2 - 150/253*w35 + 63/253) * G23 + (148/253*w35^25 + 4/253*w35^24 + 36/253*w35^23 + 4/253*w35^22 - 148/253*w35^21 + 140/253*w35^20 + 80/253*w35^19 - 31/253*w35^18 - 21/253*w35^17 + 32/253*w35^16 + 56/253*w35^15 - 34/253*w35^14 - 109/253*w35^13 - 336/253*w35^12 - 217/253*w35^11 + 217/253*w35^10 - 2/253*w35^9 - 24/253*w35^8 - 24/253*w35^7 - 87/253*w35^6 + 63/253*w35^5 + w35 + 1) * hf) (by norm_num)
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (4/253*w35^9 + 36/253*w35^8 + 30/253*w35^7 + 30/253*w35^6 + 36/253*w35^5 + 4/253*w35^4 - 31/253*w35^2 + 54/253*w35 - 31/253) * G23 + (-4/253*w35^25 - 32/253*w35^24 + 2/253*w35^23 - 32/253*w35^22 + 4/253*w35^21 + 60/253*w35^20 - 40/253*w35^19 + 73/253*w35^18 - 39/253*w35^17 + 104/253*w35^16 - 94/253*w35^15 + 60/253*w35^14 + 27/253*w35^13 - 200/253*w35^12 + 85/253*w35^11 + 53/253*w35^10 + 50/253*w35^9 - 116/253*w35^8 + 116/253*w35^7 - 85/253*w35^6 + 31/253*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-218/473*w35^9 + 128/473*w35^8 + 6/473*w35^7 + 146/473*w35^6 - 12/473*w35^5 - 78/473*w35^4 - 140/473*w35^3 - 5/473*w35^2 - 70/473*w35 + 145/473) * G23 + (218/473*w35^25 + 90/473*w35^24 + 84/473*w35^23 - 62/473*w35^22 - 486/473*w35^21 + 6/43*w35^20 + 28/43*w35^19 + 35/473*w35^18 - 3/43*w35^17 - 10/43*w35^16 + 8/43*w35^15 + 6/43*w35^14 - 11/43*w35^13 - 460/473*w35^12 - 49/43*w35^11 + 15/43*w35^10 + 438/473*w35^9 + 70/473*w35^8 - 70/473*w35^7 - 75/473*w35^6 - 145/473*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-14/11*w35^9 + 16/11*w35^8 + 24/11*w35^7 - 12/11*w35^6 - 4/11*w35^5 + 26/11*w35^4 + 12/11*w35^3 - 13/11*w35^2 + 6/11*w35 + 25/11) * G23 + (14/11*w35^25 - 30/11*w35^24 + 6/11*w35^23 + 6/11*w35^22 - 30/11*w35^21 + 50/11*w35^20 - 16/11*w35^19 - 35/11*w35^18 + 23/11*w35^17 - 10/11*w35^16 - 10/11*w35^15 + 12/11*w35^14 + 1/11*w35^13 - 24/11*w35^12 + 17/11*w35^11 + 39/11*w35^10 - 30/11*w35^9 + 6/11*w35^8 + 6/11*w35^7 - 19/11*w35^6 + 25/11*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-148/253*w35^9 + 144/253*w35^8 - 32/253*w35^7 + 32/253*w35^6 - 144/253*w35^5 + 148/253*w35^4 + 63/253*w35^2 - 150/253*w35 + 63/253) * G23 + (148/253*w35^25 + 4/253*w35^24 + 36/253*w35^23 + 4/253*w35^22 - 148/253*w35^21 + 140/253*w35^20 + 80/253*w35^19 - 31/253*w35^18 - 21/253*w35^17 + 32/253*w35^16 + 56/253*w35^15 - 34/253*w35^14 - 109/253*w35^13 - 336/253*w35^12 - 217/253*w35^11 + 217/253*w35^10 - 2/253*w35^9 - 24/253*w35^8 - 24/253*w35^7 - 87/253*w35^6 + 63/253*w35^5 + w35 + 1) * hf) (by norm_num)
    · rcases sq_split (show w45 ^ 2 = (1 : ℂ) ^ 2 by linear_combination t45) with h45 | h45
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (148/253*w35^9 + 144/253*w35^8 + 32/253*w35^7 + 32/253*w35^6 + 144/253*w35^5 + 148/253*w35^4 + 63/253*w35^2 + 150/253*w35 + 63/253) * G23 + (-148/253*w35^25 + 4/253*w35^24 - 36/253*w35^23 + 4/253*w35^22 + 148/253*w35^21 + 140/253*w35^20 - 80/253*w35^19 - 31/253*w35^18 + 21/253*w35^17 + 32/253*w35^16 - 56/253*w35^15 - 34/253*w35^14 + 109/253*w35^13 - 336/253*w35^12 + 217/253*w35^11 + 217/253*w35^10 + 2/253*w35^9 - 24/253*w35^8 + 24/253*w35^7 - 87/253*w35^6 - 63/253*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (14/11*w35^9 + 16/11*w35^8 - 24/11*w35^7 - 12/11*w35^6 + 4/11*w35^5 + 26/11*w35^4 - 12/11*w35^3 - 13/11*w35^2 - 6/11*w35 + 25/11) * G23 + (-14/11*w35^25 - 30/11*w35^24 - 6/11*w35^23 + 6/11*w35^22 + 30/11*w35^21 + 50/11*w35^20 + 16/11*w35^19 - 35/11*w35^18 - 23/11*w35^17 - 10/11*w35^16 + 10/11*w35^15 + 12/11*w35^14 - 1/11*w35^13 - 24/11*w35^12 - 17/11*w35^11 + 39/11*w35^10 + 30/11*w35^9 + 6/11*w35^8 - 6/11*w35^7 - 19/11*w35^6 - 25/11*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (-1 : ℂ) * E71 + (-1 : ℂ) * w24 * h45 + (1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (218/473*w35^9 + 128/473*w35^8 - 6/473*w35^7 + 146/473*w35^6 + 12/473*w35^5 - 78/473*w35^4 + 140/473*w35^3 - 5/473*w35^2 + 70/473*w35 + 145/473) * G23 + (-218/473*w35^25 + 90/473*w35^24 - 84/473*w35^23 - 62/473*w35^22 + 486/473*w35^21 + 6/43*w35^20 - 28/43*w35^19 + 35/473*w35^18 + 3/43*w35^17 - 10/43*w35^16 - 8/43*w35^15 + 6/43*w35^14 + 11/43*w35^13 - 460/473*w35^12 + 49/43*w35^11 + 15/43*w35^10 - 438/473*w35^9 + 70/473*w35^8 + 70/473*w35^7 - 75/473*w35^6 + 145/473*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-4/253*w35^9 + 36/253*w35^8 - 30/253*w35^7 + 30/253*w35^6 - 36/253*w35^5 + 4/253*w35^4 - 31/253*w35^2 - 54/253*w35 - 31/253) * G23 + (4/253*w35^25 - 32/253*w35^24 - 2/253*w35^23 - 32/253*w35^22 - 4/253*w35^21 + 60/253*w35^20 + 40/253*w35^19 + 73/253*w35^18 + 39/253*w35^17 + 104/253*w35^16 + 94/253*w35^15 + 60/253*w35^14 - 27/253*w35^13 - 200/253*w35^12 - 85/253*w35^11 + 53/253*w35^10 - 50/253*w35^9 - 116/253*w35^8 - 116/253*w35^7 - 85/253*w35^6 - 31/253*w35^5 + w35 + 1) * hf) (by norm_num)
      · rcases sq_split (show w03 ^ 2 = (w35 ^ 7) ^ 2 by linear_combination t03) with h03 | h03
        · have x23 : w23 = -w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (-w35 ^ 17) * w35 ^ 7 := by
              linear_combination (-1 : ℂ) * E6 + (-1 : ℂ) * w23 * h03 + (1 : ℂ) * h12 + (1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = -w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (w35 ^ 4) * w35 ^ 19 := by
              linear_combination (-1 : ℂ) * E76 + (1 : ℂ) * w13 * x14 + (-1 : ℂ) * w35 * h45 + (-1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact nc2 (by rw [x13, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (148/253*w35^9 + 144/253*w35^8 + 32/253*w35^7 + 32/253*w35^6 + 144/253*w35^5 + 148/253*w35^4 + 63/253*w35^2 + 150/253*w35 + 63/253) * G23 + (-148/253*w35^25 + 4/253*w35^24 - 36/253*w35^23 + 4/253*w35^22 + 148/253*w35^21 + 140/253*w35^20 - 80/253*w35^19 - 31/253*w35^18 + 21/253*w35^17 + 32/253*w35^16 - 56/253*w35^15 - 34/253*w35^14 + 109/253*w35^13 - 336/253*w35^12 + 217/253*w35^11 + 217/253*w35^10 + 2/253*w35^9 - 24/253*w35^8 + 24/253*w35^7 - 87/253*w35^6 - 63/253*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (14/11*w35^9 + 16/11*w35^8 - 24/11*w35^7 - 12/11*w35^6 + 4/11*w35^5 + 26/11*w35^4 - 12/11*w35^3 - 13/11*w35^2 - 6/11*w35 + 25/11) * G23 + (-14/11*w35^25 - 30/11*w35^24 - 6/11*w35^23 + 6/11*w35^22 + 30/11*w35^21 + 50/11*w35^20 + 16/11*w35^19 - 35/11*w35^18 - 23/11*w35^17 - 10/11*w35^16 + 10/11*w35^15 + 12/11*w35^14 - 1/11*w35^13 - 24/11*w35^12 - 17/11*w35^11 + 39/11*w35^10 + 30/11*w35^9 + 6/11*w35^8 - 6/11*w35^7 - 19/11*w35^6 - 25/11*w35^5 + w35 + 1) * hf) (by norm_num)
        · have x23 : w23 = w35 ^ 17 := by
            have hx : w23 * w35 ^ 7 = (w35 ^ 17) * w35 ^ 7 := by
              linear_combination (1 : ℂ) * E6 + (1 : ℂ) * w23 * h03 + (-1 : ℂ) * h12 + (-1 : ℂ) * w35 ^ 2 * qf
            exact mul_right_cancel₀ (pow_ne_zero 7 n35) hx
          have x24 : w24 = -w35 ^ 18 := by
            linear_combination (1 : ℂ) * E71 + (1 : ℂ) * w24 * h45 + (-1 : ℂ) * w35 * x23
          have x14 : w14 = w35 ^ 19 := by
            linear_combination E18 + w24 * h02 + (-1 : ℂ) * w35 * x24
          have x13 : w13 = -w35 ^ 4 := by
            have hx : w13 * w35 ^ 19 = (-w35 ^ 4) * w35 ^ 19 := by
              linear_combination (1 : ℂ) * E76 + (-1 : ℂ) * w13 * x14 + (1 : ℂ) * w35 * h45 + (1 : ℂ) * w35 * qf
            exact mul_right_cancel₀ (pow_ne_zero 19 n35) hx
          rw [h02, h12, h03, x13, x23] at G23
          rcases pow22_split qf with hf | hf | hf | hf
          · exact nc3 (by rw [h03, x13, hf] <;> norm_num)
          · exact nc1 (by rw [h03, hf] <;> norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (218/473*w35^9 + 128/473*w35^8 - 6/473*w35^7 + 146/473*w35^6 + 12/473*w35^5 - 78/473*w35^4 + 140/473*w35^3 - 5/473*w35^2 + 70/473*w35 + 145/473) * G23 + (-218/473*w35^25 + 90/473*w35^24 - 84/473*w35^23 - 62/473*w35^22 + 486/473*w35^21 + 6/43*w35^20 - 28/43*w35^19 + 35/473*w35^18 + 3/43*w35^17 - 10/43*w35^16 - 8/43*w35^15 + 6/43*w35^14 + 11/43*w35^13 - 460/473*w35^12 + 49/43*w35^11 + 15/43*w35^10 - 438/473*w35^9 + 70/473*w35^8 + 70/473*w35^7 - 75/473*w35^6 + 145/473*w35^5 - w35 + 1) * hf) (by norm_num)
          · exact absurd (show ((1 : ℂ)) = 0 by
              linear_combination (-4/253*w35^9 + 36/253*w35^8 - 30/253*w35^7 + 30/253*w35^6 - 36/253*w35^5 + 4/253*w35^4 - 31/253*w35^2 - 54/253*w35 - 31/253) * G23 + (4/253*w35^25 - 32/253*w35^24 - 2/253*w35^23 - 32/253*w35^22 - 4/253*w35^21 + 60/253*w35^20 + 40/253*w35^19 + 73/253*w35^18 + 39/253*w35^17 + 104/253*w35^16 + 94/253*w35^15 + 60/253*w35^14 - 27/253*w35^13 - 200/253*w35^12 - 85/253*w35^11 + 53/253*w35^10 - 50/253*w35^9 - 116/253*w35^8 - 116/253*w35^7 - 85/253*w35^6 - 31/253*w35^5 + w35 + 1) * hf) (by norm_num)

/-- The mask of the second class of this shape. -/
def maskK34 : Mask := 20025197522889238378840144

theorem maskK34_mem : maskK34 ∈ censusRest := by decide

/-- **The second class is not supported.** -/
theorem not_supports_k34 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hsup : Supports p maskK34) : False := by
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
  have P4 : Psi (p 3) (p 5) (p 0) (p 1) = 0 := by
    have h := hsup 4 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 4 = ((0, 1), (3, 5)) from by decide)] at h
  have EQ4 : normW p 0 3 * normW p 1 3 = normW p 0 5 * normW p 1 5 :=
    witness_monomial S30 S31 S50 S51 (hC 3 0 (by decide)) (hC 3 1 (by decide)) (hC 5 0 (by decide)) (hC 5 1 (by decide)) (cell_bridge hsne htne 3 5 0 1 P4)
  have P6 : Psi (p 1) (p 3) (p 0) (p 2) = 0 := by
    have h := hsup 6 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 6 = ((0, 2), (1, 3)) from by decide)] at h
  have EQ6 : normW p 1 2 = normW p 0 3 * normW p 2 3 := by
    have k := witness_monomial S10 S12 S30 S32 (hC 1 0 (by decide)) (hC 1 2 (by decide)) (hC 3 0 (by decide)) (hC 3 2 (by decide)) (cell_bridge hsne htne 1 3 0 2 P6)
    rwa [hw01, one_mul] at k
  have P17 : Psi (p 4) (p 5) (p 0) (p 3) = 0 := by
    have h := hsup 17 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 17 = ((0, 3), (4, 5)) from by decide)] at h
  have EQ17 : normW p 0 4 * normW p 3 4 = normW p 0 5 * normW p 3 5 :=
    witness_monomial S40 S43 S50 S53 (hC 4 0 (by decide)) (hC 4 3 (by decide)) (hC 5 0 (by decide)) (hC 5 3 (by decide)) (cell_bridge hsne htne 4 5 0 3 P17)
  have P18 : Psi (p 1) (p 2) (p 0) (p 4) = 0 := by
    have h := hsup 18 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 18 = ((0, 4), (1, 2)) from by decide)] at h
  have EQ18 : normW p 1 4 = normW p 0 2 * normW p 2 4 := by
    have k := witness_monomial S10 S14 S20 S24 (hC 1 0 (by decide)) (hC 1 4 (by decide)) (hC 2 0 (by decide)) (hC 2 4 (by decide)) (cell_bridge hsne htne 1 2 0 4 P18)
    rwa [hw01, one_mul] at k
  have P28 : Psi (p 2) (p 4) (p 0) (p 5) = 0 := by
    have h := hsup 28 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 28 = ((0, 5), (2, 4)) from by decide)] at h
  have EQ28 : normW p 0 2 * normW p 2 5 = normW p 0 4 * normW p 4 5 :=
    witness_monomial S20 S25 S40 S45 (hC 2 0 (by decide)) (hC 2 5 (by decide)) (hC 4 0 (by decide)) (hC 4 5 (by decide)) (cell_bridge hsne htne 2 4 0 5 P28)
  have P32 : Psi (p 0) (p 5) (p 1) (p 2) = 0 := by
    have h := hsup 32 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 32 = ((1, 2), (0, 5)) from by decide)] at h
  have EQ32 : normW p 0 2 = normW p 1 5 * normW p 2 5 := by
    have k := witness_monomial S01 S02 S51 S52 (hC 0 1 (by decide)) (hC 0 2 (by decide)) (hC 5 1 (by decide)) (hC 5 2 (by decide)) (cell_bridge hsne htne 0 5 1 2 P32)
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
  have P51 : Psi (p 2) (p 3) (p 1) (p 5) = 0 := by
    have h := hsup 51 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 51 = ((1, 5), (2, 3)) from by decide)] at h
  have EQ51 : normW p 1 2 * normW p 2 5 = normW p 1 3 * normW p 3 5 :=
    witness_monomial S21 S25 S31 S35 (hC 2 1 (by decide)) (hC 2 5 (by decide)) (hC 3 1 (by decide)) (hC 3 5 (by decide)) (cell_bridge hsne htne 2 3 1 5 P51)
  have P57 : Psi (p 1) (p 4) (p 2) (p 3) = 0 := by
    have h := hsup 57 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 57 = ((2, 3), (1, 4)) from by decide)] at h
  have EQ57 : normW p 1 2 * normW p 1 3 = normW p 2 4 * normW p 3 4 :=
    witness_monomial S12 S13 S42 S43 (hC 1 2 (by decide)) (hC 1 3 (by decide)) (hC 4 2 (by decide)) (hC 4 3 (by decide)) (cell_bridge hsne htne 1 4 2 3 P57)
  have P61 : Psi (p 0) (p 3) (p 2) (p 4) = 0 := by
    have h := hsup 61 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 61 = ((2, 4), (0, 3)) from by decide)] at h
  have EQ61 : normW p 0 2 * normW p 0 4 = normW p 2 3 * normW p 3 4 :=
    witness_monomial S02 S04 S32 S34 (hC 0 2 (by decide)) (hC 0 4 (by decide)) (hC 3 2 (by decide)) (hC 3 4 (by decide)) (cell_bridge hsne htne 0 3 2 4 P61)
  have P71 : Psi (p 3) (p 4) (p 2) (p 5) = 0 := by
    have h := hsup 71 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 71 = ((2, 5), (3, 4)) from by decide)] at h
  have EQ71 : normW p 2 3 * normW p 3 5 = normW p 2 4 * normW p 4 5 :=
    witness_monomial S32 S35 S42 S45 (hC 3 2 (by decide)) (hC 3 5 (by decide)) (hC 4 2 (by decide)) (hC 4 5 (by decide)) (cell_bridge hsne htne 3 4 2 5 P71)
  have P76 : Psi (p 1) (p 5) (p 3) (p 4) = 0 := by
    have h := hsup 76 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 76 = ((3, 4), (1, 5)) from by decide)] at h
  have EQ76 : normW p 1 3 * normW p 1 4 = normW p 3 5 * normW p 4 5 :=
    witness_monomial S13 S14 S53 S54 (hC 1 3 (by decide)) (hC 1 4 (by decide)) (hC 5 3 (by decide)) (hC 5 4 (by decide)) (cell_bridge hsne htne 1 5 3 4 P76)
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
  exact core_class34 (normW p 0 2) (normW p 0 3) (normW p 0 4) (normW p 0 5) (normW p 1 2) (normW p 1 3) (normW p 1 4) (normW p 1 5) (normW p 2 3) (normW p 2 4) (normW p 2 5) (normW p 3 4) (normW p 3 5) (normW p 4 5)
    (normY p 2) (normC p 2) (normY p 3) (normC p 3)
    N02 N03 N04 N05 N12 N13 N14 N15 N23 N24 N25 N34 N35 N45
    EQ4 EQ6 EQ17 EQ18 EQ28 EQ32 EQ37 EQ46 EQ51 EQ57 EQ61 EQ71 EQ76 EQ79 EQ84
    u2 v2 u3 v3 g23 nc1 nc2 nc3

theorem not_carries_k34 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK34) : False :=
  not_supports_k34 p hgp (supports_of_carries hc)



end QB11

end DistinctCircumradii

#print axioms DistinctCircumradii.QB11.cellPsi_eq
#print axioms DistinctCircumradii.QB11.maskK31_mem
#print axioms DistinctCircumradii.QB11.collinear_of_cross_eq
#print axioms DistinctCircumradii.QB11.div_mul_cancel_ne
#print axioms DistinctCircumradii.QB11.normY_sub
#print axioms DistinctCircumradii.QB11.normC_sub
#print axioms DistinctCircumradii.QB11.normY_zero
#print axioms DistinctCircumradii.QB11.normC_zero
#print axioms DistinctCircumradii.QB11.normY_one
#print axioms DistinctCircumradii.QB11.normC_one
#print axioms DistinctCircumradii.QB11.normY_sub_ne
#print axioms DistinctCircumradii.QB11.normC_sub_ne
#print axioms DistinctCircumradii.QB11.normW_spec
#print axioms DistinctCircumradii.QB11.normW_spec'
#print axioms DistinctCircumradii.QB11.normW_ne
#print axioms DistinctCircumradii.QB11.cell_bridge
#print axioms DistinctCircumradii.QB11.witness_monomial
#print axioms DistinctCircumradii.QB11.sq_split
#print axioms DistinctCircumradii.QB11.pow22_split
#print axioms DistinctCircumradii.QB11.pair_relation
#print axioms DistinctCircumradii.QB11.core_class34
#print axioms DistinctCircumradii.QB11.maskK34_mem
#print axioms DistinctCircumradii.QB11.not_supports_k34
#print axioms DistinctCircumradii.QB11.not_carries_k34
