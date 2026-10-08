/-
  Elementary algebra behind the degree-six equation for triples of divisor classes
  taken from a rank-three commutative order (the "order version").
  No geometry, no sheaves, no cycles; no statement about the Hodge conjecture.

  Contents.
  1. The trace form of a triple:  Q p = 3*(sum p^2) - (sum p)^2 = sum_{j<l} (p_j - p_l)^2,
     hence Q p >= 0.
  2. The budget lemma: for 0 <= p_j <= G one has  a*(3G - a) - Q p = 3 * sum p_j (G - p_j) >= 0,
     where a = sum p.  (This is "the cost of absorbing is at least the amount absorbed".)
  3. The symmetric-function forms of the three coordinates of a cyclic triple, and
     the fact that the antisymmetric coordinate squares to the discriminant.
  4. Three-variable AM-GM, giving  e3 <= (e1/3)^3  for non-negative entries.
  5. The weight bound that follows from 2 + 4 (the arithmetic step of the
     obstruction theorem), both in the plain and in the scaled form.
-/
import Mathlib

namespace OrderTriples

open scoped BigOperators

/-! ### 1. The trace form of a triple -/

/-- `Q p q r = 3 (p^2+q^2+r^2) - (p+q+r)^2`. -/
def Q {R : Type*} [CommRing R] (p q r : R) : R := 3*(p^2+q^2+r^2) - (p+q+r)^2

theorem Q_eq_sum_sq {R : Type*} [CommRing R] (p q r : R) :
    Q p q r = (p-q)^2 + (q-r)^2 + (p-r)^2 := by
  unfold Q; ring

theorem Q_nonneg (p q r : ℝ) : 0 ≤ Q p q r := by
  rw [Q_eq_sum_sq]
  have h1 := sq_nonneg (p-q); have h2 := sq_nonneg (q-r); have h3 := sq_nonneg (p-r)
  linarith

/-! ### 2. The budget lemma -/

theorem budget_identity {R : Type*} [CommRing R] (G p q r : R) :
    (p+q+r)*(3*G - (p+q+r)) - Q p q r = 3*(p*(G-p) + q*(G-q) + r*(G-r)) := by
  unfold Q; ring

/-- If every entry lies in `[0,G]`, the "cost" `a (3G - a)` is at least the trace form. -/
theorem Q_le_cost {G p q r : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hp' : p ≤ G) (hq' : q ≤ G) (hr' : r ≤ G) :
    Q p q r ≤ (p+q+r)*(3*G - (p+q+r)) := by
  have h := budget_identity G p q r
  have h1 : 0 ≤ p*(G-p) := mul_nonneg hp (by linarith)
  have h2 : 0 ≤ q*(G-q) := mul_nonneg hq (by linarith)
  have h3 : 0 ≤ r*(G-r) := mul_nonneg hr (by linarith)
  linarith

/-! ### 3. Symmetric functions of a triple -/

variable {R : Type*} [CommRing R]

/-- `e1`, `e2`, `e3` of a triple. -/
def e1 (p q r : R) : R := p + q + r
def e2 (p q r : R) : R := p*q + p*r + q*r
def e3 (p q r : R) : R := p*q*r

/-- The sum of the six monomials `p^2 q` (two distinct indices). -/
def mixed (p q r : R) : R := p^2*q + p^2*r + q^2*p + q^2*r + r^2*p + r^2*q
/-- The sum of cubes. -/
def cubes (p q r : R) : R := p^3 + q^3 + r^3
/-- The antisymmetric combination; its square is the discriminant. -/
def anti (p q r : R) : R := p^2*q + q^2*r + r^2*p - (p^2*r + q^2*p + r^2*q)

theorem mixed_eq (p q r : R) : mixed p q r = e1 p q r * e2 p q r - 3 * e3 p q r := by
  unfold mixed e1 e2 e3; ring

theorem cubes_eq (p q r : R) :
    cubes p q r = (e1 p q r)^3 - 3 * e1 p q r * e2 p q r + 3 * e3 p q r := by
  unfold cubes e1 e2 e3; ring

/-- The `per`-coordinate of a cyclic triple. -/
theorem per_eq (p q r : R) :
    3 * e3 p q r + cubes p q r
      = (e1 p q r)^3 - 3 * e1 p q r * e2 p q r + 6 * e3 p q r := by
  rw [cubes_eq]; ring

/-- The `l`-coordinate of a cyclic triple. -/
theorem ell_eq (p q r : R) :
    mixed p q r - (3 * e3 p q r + cubes p q r)
      = 4 * e1 p q r * e2 p q r - (e1 p q r)^3 - 9 * e3 p q r := by
  rw [mixed_eq, cubes_eq]; ring

/-- The antisymmetric coordinate squares to the discriminant of the characteristic
polynomial, written in the elementary symmetric functions. -/
theorem anti_sq_eq_disc (p q r : R) :
    (anti p q r)^2 =
      (e1 p q r)^2 * (e2 p q r)^2 - 4*(e2 p q r)^3
        - 4*(e1 p q r)^3 * e3 p q r + 18 * e1 p q r * e2 p q r * e3 p q r
        - 27 * (e3 p q r)^2 := by
  unfold anti e1 e2 e3; ring

/-! ### 4. Three-variable AM-GM -/

theorem amgm3 {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    27 * (p*q*r) ≤ (p+q+r)^3 := by
  nlinarith [sq_nonneg (p-q), sq_nonneg (q-r), sq_nonneg (p-r), sq_nonneg (p+q+r),
    mul_nonneg hp hq, mul_nonneg hq hr, mul_nonneg hp hr,
    mul_nonneg (mul_nonneg hp hq) hr,
    mul_nonneg hp (sq_nonneg (q-r)), mul_nonneg hq (sq_nonneg (p-r)),
    mul_nonneg hr (sq_nonneg (p-q))]

/-- `e3 <= (e1/3)^3` in the form used by the obstruction argument. -/
theorem e3_le {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    27 * e3 p q r ≤ (e1 p q r)^3 := by
  unfold e3 e1; exact amgm3 hp hq hr

/-! ### 5. The arithmetic step of the obstruction -/

/-- With `g = 7560`, `q = 19`: if the weight `Y` on cyclic triples and the weighted sum
`S3` of the norms satisfy the two bounds coming from the budget and from AM-GM, then
`Y ≤ 1`. -/
theorem weight_le_one {Y S3 : ℤ} (hY : 0 ≤ Y) (hS : 0 ≤ S3)
    (h1 : 432081216000 * (Y - 1) - 3 * 7560 * 19 ≤ 3 * S3)
    (h2 : 27 * S3 ≤ Y * 432081216000) : Y ≤ 1 := by
  by_contra h
  have hY2 : 2 ≤ Y := by omega
  nlinarith [h1, h2, hY2]

/-- The same step for the scaled (equivariant, `c = 105`) target forces `Y = 0`. -/
theorem weight_eq_zero_scaled {Y S3 : ℤ} (hY : 0 ≤ Y) (hS : 0 ≤ S3)
    (h1 : 432081216000 * Y - 4115059200 - 4104 ≤ 3 * S3)
    (h2 : 27 * S3 ≤ Y * 432081216000) : Y = 0 := by
  by_contra h
  have hY1 : 1 ≤ Y := by omega
  nlinarith [h1, h2, hY1]

/-- Every one of the six mixed monomials is non-negative when the entries are, so the
two `E`-coordinates and the `per`-coordinate of a triple are non-negative. -/
theorem mixed_nonneg {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ mixed p q r := by
  unfold mixed
  have := mul_nonneg (mul_nonneg hp hp) hq
  nlinarith [mul_nonneg (mul_nonneg hp hp) hq, mul_nonneg (mul_nonneg hp hp) hr,
    mul_nonneg (mul_nonneg hq hq) hp, mul_nonneg (mul_nonneg hq hq) hr,
    mul_nonneg (mul_nonneg hr hr) hp, mul_nonneg (mul_nonneg hr hr) hq]

end OrderTriples

#print axioms OrderTriples.Q_nonneg
#print axioms OrderTriples.Q_le_cost
#print axioms OrderTriples.mixed_eq
#print axioms OrderTriples.ell_eq
#print axioms OrderTriples.anti_sq_eq_disc
#print axioms OrderTriples.e3_le
#print axioms OrderTriples.weight_le_one
#print axioms OrderTriples.weight_eq_zero_scaled
#print axioms OrderTriples.mixed_nonneg
