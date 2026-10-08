/-
  The `(j;2,2)` second difference of the secant test function `((t_j − u_j)² + q)·u_k²u_l²`
  on a complete-intersection piece `D_a ∩ D_b`, and the elementary facts behind its sign.

  Coordinates: `aj, bj` are the slot-`j` coordinates of the two classes, `ak, al, bk, bl` the other two;
  `π_a = ak*al`, `π_b = bk*bl`, `P = π_{a+b} = (ak+bk)*(al+bl)`, `A = √π_a`, `B = √π_b`.
  Nothing here is geometry: the Koszul formula and the secant space enter only through these identities.
-/
import Mathlib

namespace SecondDifference

/-- The `(j;2,2)` test function in slot coordinates: `x` is slot `j`, `y z` the other two. -/
def f (t q x y z : ℝ) : ℝ := ((t - x)^2 + q) * y^2 * z^2

/-- Identity S0. -/
theorem delta_identity (t q aj ak al bj bk bl : ℝ) :
    f t q (aj+bj) (ak+bk) (al+bl) - f t q aj ak al - f t q bj bk bl + f t q 0 0 0
      = ((t-(aj+bj))^2+q) * ((ak+bk)^2*(al+bl)^2 - ak^2*al^2 - bk^2*bl^2)
        - bj*(2*t-2*aj-bj)*(ak^2*al^2) - aj*(2*t-2*bj-aj)*(bk^2*bl^2) := by
  unfold f; ring

theorem cross_expand (ak al bk bl : ℝ) :
    (ak+bk)^2*(al+bl)^2 - ak^2*al^2 - bk^2*bl^2
      = 2*(ak*al)*(bk*bl) + 2*(ak*al + bk*bl)*(ak*bl + al*bk) + (ak*bl + al*bk)^2 := by
  ring

theorem cross_pos (ak al bk bl : ℝ) (h1 : 0 < ak) (h2 : 0 < al) (h3 : 0 < bk) (h4 : 0 < bl) :
    0 < (ak+bk)^2*(al+bl)^2 - ak^2*al^2 - bk^2*bl^2 := by
  rw [cross_expand]; positivity

/-- Lemma S1: a nonpositive slot of the twist makes every second difference at least `q·C`. -/
theorem nonpos_slot (t q aj bj C Ya Yb : ℝ) (ht : t ≤ 0) (haj : 0 ≤ aj) (hbj : 0 ≤ bj)
    (hC : 0 ≤ C) (hYa : 0 ≤ Ya) (hYb : 0 ≤ Yb) :
    q*C ≤ ((t-(aj+bj))^2+q)*C - bj*(2*t-2*aj-bj)*Ya - aj*(2*t-2*bj-aj)*Yb := by
  have h1 : 0 ≤ (t-(aj+bj))^2*C := mul_nonneg (sq_nonneg _) hC
  have h2 : 0 ≤ -(bj*(2*t-2*aj-bj))*Ya := mul_nonneg (by nlinarith) hYa
  have h3 : 0 ≤ -(aj*(2*t-2*bj-aj))*Yb := mul_nonneg (by nlinarith) hYb
  nlinarith

/-- The weak (sum) form of the lower bound, valid for every real twist coordinate. -/
theorem delta_lower_simple (t q aj bj C Ya Yb : ℝ) (haj : 0 ≤ aj) (hbj : 0 ≤ bj)
    (hC : 0 ≤ C) (hYa : 0 ≤ Ya) (hYb : 0 ≤ Yb) :
    q*C - t^2*(Ya + Yb) ≤ ((t-(aj+bj))^2+q)*C - bj*(2*t-2*aj-bj)*Ya - aj*(2*t-2*bj-aj)*Yb := by
  have h1 : bj*(2*t-2*aj-bj) ≤ t^2 := by nlinarith [sq_nonneg (t-bj), mul_nonneg haj hbj]
  have h2 : aj*(2*t-2*bj-aj) ≤ t^2 := by nlinarith [sq_nonneg (t-aj), mul_nonneg haj hbj]
  have h3 : 0 ≤ (t-(aj+bj))^2*C := mul_nonneg (sq_nonneg _) hC
  nlinarith [mul_le_mul_of_nonneg_right h1 hYa, mul_le_mul_of_nonneg_right h2 hYb]

/-- The core of Proposition S: an explicit sum of three nonnegative terms. -/
theorem slot_min_identity (t α β x y : ℝ) :
    (t-α-β)^2*(x+y)^2 - (t-α)^2*x^2 - (t-β)^2*y^2 + t^2*x^2
      = (x^2 - y^2)*(t-β)^2 + (y^2 + 2*x*y)*(t-α-β)^2 + 2*α*β*x^2 := by
  ring

theorem slot_min (t α β x y : ℝ) (hαβ : 0 ≤ α*β) (hy : 0 ≤ y) (hxy : y ≤ x) :
    0 ≤ (t-α-β)^2*(x+y)^2 - (t-α)^2*x^2 - (t-β)^2*y^2 + t^2*x^2 := by
  rw [slot_min_identity]
  have hx : 0 ≤ x := le_trans hy hxy
  have h1 : 0 ≤ x^2 - y^2 := by nlinarith
  have h2 : 0 ≤ y^2 + 2*x*y := by positivity
  have h3 : 0 ≤ 2*α*β*x^2 := by
    have : 0 ≤ (α*β)*x^2 := mul_nonneg hαβ (sq_nonneg x)
    nlinarith
  have h4 : 0 ≤ (x^2 - y^2)*(t-β)^2 := mul_nonneg h1 (sq_nonneg _)
  have h5 : 0 ≤ (y^2 + 2*x*y)*(t-α-β)^2 := mul_nonneg h2 (sq_nonneg _)
  linarith

/-- Proposition S (sharp lower bound): `x = π_a ≥ y = π_b ≥ 0`, `P = π_{a+b} ≥ x + y`, slot coordinates `α, β ≥ 0`. -/
theorem delta_lower_sharp (t q α β x y P : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hy : 0 ≤ y) (hxy : y ≤ x)
    (hP : x + y ≤ P) :
    q*(P^2 - x^2 - y^2) - t^2*x^2 ≤ ((t-(α+β))^2+q)*P^2 - ((t-α)^2+q)*x^2 - ((t-β)^2+q)*y^2 := by
  have hE := slot_min t α β x y (mul_nonneg hα hβ) hy hxy
  have hxy0 : 0 ≤ x + y := by linarith
  have hP2 : (x+y)^2 ≤ P^2 := by nlinarith
  have : (t-α-β)^2*(x+y)^2 ≤ (t-(α+β))^2*P^2 := by
    have e : t-α-β = t-(α+β) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
  nlinarith

/-- Equality in Proposition S at slot coordinates `(0, t)`. -/
theorem delta_sharp_equality (t q x y P : ℝ) :
    ((t-(0+t))^2+q)*P^2 - ((t-0)^2+q)*x^2 - ((t-t)^2+q)*y^2 = q*(P^2 - x^2 - y^2) - t^2*x^2 := by
  ring

theorem ratio_form (A B : ℝ) : (A+B)^4 - A^4 - B^4 = 4*A^3*B + 6*A^2*B^2 + 4*A*B^3 := by ring

/-- The region of Proposition S: with `A ≥ B > 0` (`A² = π_a`, `B² = π_b`), `P ≥ (A+B)²` (Cauchy–Schwarz) and
`t²A⁴ < q(4A³B + 6A²B² + 4AB³)` (i.e. `t² < q(4r+6r²+4r³)`, `r = B/A`), the second difference is positive
whatever the slot-`j` coordinates are. -/
theorem region_positive (t q α β A B P : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB : 0 < B) (hAB : B ≤ A)
    (hP : (A+B)^2 ≤ P) (hq : 0 ≤ q) (hreg : t^2*A^4 < q*(4*A^3*B + 6*A^2*B^2 + 4*A*B^3)) :
    0 < ((t-(α+β))^2+q)*P^2 - ((t-α)^2+q)*(A^2)^2 - ((t-β)^2+q)*(B^2)^2 := by
  have hA : 0 < A := lt_of_lt_of_le hB hAB
  have hxy : B^2 ≤ A^2 := by nlinarith
  have hsum : A^2 + B^2 ≤ P := by nlinarith
  have hs := delta_lower_sharp t q α β (A^2) (B^2) P hα hβ (sq_nonneg B) hxy hsum
  have hP0 : 0 ≤ (A+B)^2 := sq_nonneg _
  have hP4 : ((A+B)^2)^2 ≤ P^2 := by nlinarith
  have hC : q*(((A+B)^2)^2 - (A^2)^2 - (B^2)^2) ≤ q*(P^2 - (A^2)^2 - (B^2)^2) :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  have e : ((A+B)^2)^2 - (A^2)^2 - (B^2)^2 = 4*A^3*B + 6*A^2*B^2 + 4*A*B^3 := by ring
  have e2 : t^2*(A^2)^2 = t^2*A^4 := by ring
  nlinarith

/-- `t = 3`, `q = 19`: the boundary lies between `r = 1/10` (outside) and `r = 1/8` (inside). -/
theorem boundary_t3 :
    (3:ℝ)^2 < 19*(4*(1/8) + 6*(1/8)^2 + 4*(1/8)^3) ∧ 19*(4*(1/10) + 6*(1/10)^2 + 4*(1/10)^3) < (3:ℝ)^2 := by
  norm_num

/-- One variable: `K(x,y) = (h(x)−h(y))/(x−y)` for `h(u) = u³((t−u)²+q)` is positive when `t² ≤ 15q`, `x ≠ y`. -/
theorem K_pos (t q x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ y) (hq : t^2 ≤ 15*q) :
    0 < t^2*(x^2+x*y+y^2) - 2*t*((x+y)*(x^2+y^2)) + (x^4+x^3*y+x^2*y^2+x*y^3+y^4) + q*(x^2+x*y+y^2) := by
  set S2 := x^2+x*y+y^2 with hS2
  set S3 := (x+y)*(x^2+y^2) with hS3
  set S4 := x^4+x^3*y+x^2*y^2+x*y^3+y^4 with hS4
  have hd : 0 < (x-y)^2 := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hP : 0 < x^4 + 4*x^3*y + 10*x^2*y^2 + 4*x*y^3 + y^4 := by
    have hxy : 0 < x + y := by
      rcases lt_or_gt_of_ne hne with h | h <;> linarith
    nlinarith [pow_pos hxy 4, mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) (mul_nonneg hx hy),
      mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hy), mul_nonneg (mul_nonneg hy hy) (mul_nonneg hx hy)]
  have hD : 0 < 16*S2*S4 - 15*S3^2 := by
    have e : 16*S2*S4 - 15*S3^2 = (x-y)^2*(x^4 + 4*x^3*y + 10*x^2*y^2 + 4*x*y^3 + y^4) := by
      simp only [hS2, hS3, hS4]; ring
    rw [e]; exact mul_pos hd hP
  have hS2pos : 0 < S2 := by
    have : 0 < x^2 + y^2 := by
      rcases lt_or_gt_of_ne hne with h | h
      · have : 0 < y := lt_of_le_of_lt hx h; positivity
      · have : 0 < x := lt_of_le_of_lt hy h; positivity
    nlinarith [mul_nonneg hx hy]
  have key : 16*S2*(16*S2*t^2 - 30*S3*t + 15*S4) = (16*S2*t - 15*S3)^2 + 15*(16*S2*S4 - 15*S3^2) := by
    ring
  have hQ : 0 < 16*S2*t^2 - 30*S3*t + 15*S4 := by
    have : 0 < 16*S2*(16*S2*t^2 - 30*S3*t + 15*S4) := by rw [key]; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have hq' : 0 ≤ (15*q - t^2)*S2 := mul_nonneg (by linarith) hS2pos.le
  nlinarith

/-- Proposition S′ (one variable, rational classes, rational twist): for `t² ≤ 15q` every piece has a
positive second difference of `F(u) = ((t−u)²+q)u⁴`. -/
theorem one_variable_positive (t q α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hq : t^2 ≤ 15*q) :
    0 < ((t-(α+β))^2+q)*(α+β)^4 - ((t-α)^2+q)*α^4 - ((t-β)^2+q)*β^4 := by
  have e : ((t-(α+β))^2+q)*(α+β)^4 - ((t-α)^2+q)*α^4 - ((t-β)^2+q)*β^4
      = α*β*((t^2*((α+β)^2+(α+β)*α+α^2) - 2*t*(((α+β)+α)*((α+β)^2+α^2))
              + ((α+β)^4+(α+β)^3*α+(α+β)^2*α^2+(α+β)*α^3+α^4) + q*((α+β)^2+(α+β)*α+α^2))
            + (t^2*((α+β)^2+(α+β)*β+β^2) - 2*t*(((α+β)+β)*((α+β)^2+β^2))
              + ((α+β)^4+(α+β)^3*β+(α+β)^2*β^2+(α+β)*β^3+β^4) + q*((α+β)^2+(α+β)*β+β^2))) := by
    ring
  rw [e]
  have k1 := K_pos t q (α+β) α (by linarith) hα.le (by linarith) hq
  have k2 := K_pos t q (α+β) β (by linarith) hβ.le (by linarith) hq
  have := mul_pos hα hβ
  positivity

/-- Equal pieces in one variable, and the rational boundary `8t² = 217q`. -/
theorem equal_pieces (t q α : ℝ) :
    ((t-2*α)^2+q)*(2*α)^4 - 2*(((t-α)^2+q)*α^4) = 2*α^4*(31*α^2 - 30*t*α + 7*(t^2+q)) := by ring

theorem equal_pieces_pos (t q α : ℝ) (h : 8*t^2 < 217*q) : 0 < 31*α^2 - 30*t*α + 7*(t^2+q) := by
  nlinarith [sq_nonneg (31*α - 15*t)]

theorem equal_pieces_neg (t q : ℝ) (h : 217*q < 8*t^2) :
    31*(15*t/31)^2 - 30*t*(15*t/31) + 7*(t^2+q) < 0 := by
  nlinarith

/-- The certificate step: a nonnegative combination of positive numbers summing to zero is empty,
which contradicts (C2) with nonzero right-hand side. -/
theorem no_full_separation {ι : Type*} (s : Finset ι) (n v w : ι → ℝ) (c : ℝ)
    (hn : ∀ i ∈ s, 0 ≤ n i) (hv : ∀ i ∈ s, 0 < v i)
    (h22 : ∑ i ∈ s, n i * v i = 0) (hC2 : ∑ i ∈ s, n i * w i = c) (hc : c ≠ 0) : False := by
  have hz : ∀ i ∈ s, n i * v i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => mul_nonneg (hn i hi) (hv i hi).le)).1 h22
  have hn0 : ∀ i ∈ s, n i = 0 := by
    intro i hi
    rcases mul_eq_zero.1 (hz i hi) with h | h
    · exact h
    · exact absurd h (ne_of_gt (hv i hi))
  apply hc; rw [← hC2]
  exact Finset.sum_eq_zero (fun i hi => by rw [hn0 i hi, zero_mul])

end SecondDifference

#print axioms SecondDifference.delta_identity
#print axioms SecondDifference.cross_pos
#print axioms SecondDifference.nonpos_slot
#print axioms SecondDifference.delta_lower_simple
#print axioms SecondDifference.slot_min
#print axioms SecondDifference.delta_lower_sharp
#print axioms SecondDifference.delta_sharp_equality
#print axioms SecondDifference.ratio_form
#print axioms SecondDifference.region_positive
#print axioms SecondDifference.boundary_t3
#print axioms SecondDifference.K_pos
#print axioms SecondDifference.one_variable_positive
#print axioms SecondDifference.equal_pieces
#print axioms SecondDifference.equal_pieces_pos
#print axioms SecondDifference.equal_pieces_neg
#print axioms SecondDifference.no_full_separation
