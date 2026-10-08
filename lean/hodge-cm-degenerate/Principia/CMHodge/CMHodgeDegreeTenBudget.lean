/-
  Elementary algebra behind the degree-ten bookkeeping for triples of divisor classes
  taken from a rank-three commutative order (the "order version").
  No geometry, no sheaves, no cycles; nothing about the Hodge conjecture is asserted.

  Contents.
  1. The degree-two coefficient of the Koszul factor of a triple:
       1/6 (x^2+y^2+z^2) + 1/4 (xy+yz+zx) = (x+y+z)^2/8 + (x^2+y^2+z^2)/24,
     which turns the degree-ten requirement into  G_10 - (1/24) * COST.
  2. The antisymmetric identity  3 (x^2+y^2+z^2) - (x+y+z)^2 = sum_{i<j} (x_i-x_j)^2,
     and its consequence for the cost of a single triple.
  3. The budget arithmetic:  24 (3 g^5/8 - 6 g q^2) = 9 g^5 - 144 g q^2,
     (g^2/3)(30 g^3 + 72 g q) = 10 g^5 + 24 g^3 q, and the gap between them.
  4. The symmetric-function coordinates of a cyclic triple, and the extremal point
     e1 = g, e2 = g^2/4, e3 = 0 where the cost equals the budget exactly.
  5. The obstruction: asking one cyclic triple alone to meet the three degree-six
     equations forces  e3 = -g q  (negative) and the antisymmetric coordinate to vanish.
  6. The closed form of the sum of the five divisor classes of a glued pair.
-/
import Mathlib

namespace DegreeTenBudget

/-! ### 1. The degree-two coefficient of the Koszul factor -/

/-- The degree-two part of `prod_i (1 - exp(-x_i))/x_i` is
`1/6 * (sum x_i^2) + 1/4 * (sum_{i<j} x_i x_j)`; rewritten with the total `x+y+z`. -/
theorem koszul_deg2 (x y z : ℚ) :
    (1/6) * (x^2 + y^2 + z^2) + (1/4) * (x*y + y*z + z*x)
      = (x + y + z)^2 / 8 + (x^2 + y^2 + z^2) / 24 := by
  ring

/-- With `x + y + z = g` the first term is `g^2/8`, so the whole dependence on the
triple sits in `(x^2+y^2+z^2)/24`. -/
theorem koszul_deg2_fixed_sum (x y z g : ℚ) (h : x + y + z = g) :
    (1/6) * (x^2 + y^2 + z^2) + (1/4) * (x*y + y*z + z*x)
      = g^2 / 8 + (x^2 + y^2 + z^2) / 24 := by
  rw [koszul_deg2, h]

/-! ### 2. The antisymmetric identity -/

/-- `3 (x^2+y^2+z^2) - (x+y+z)^2 = (x-y)^2 + (y-z)^2 + (z-x)^2`. -/
theorem three_sq_sub_sq (x y z : ℚ) :
    3 * (x^2 + y^2 + z^2) - (x + y + z)^2
      = (x - y)^2 + (y - z)^2 + (z - x)^2 := by
  ring

/-- Hence `sum x_i^2 = g^2/3 + (1/3) * sum_{i<j}(x_i-x_j)^2` when `x+y+z = g`:
the cost of a triple is the "balanced" value plus one third of the antisymmetric part. -/
theorem cost_split (x y z g : ℚ) (h : x + y + z = g) :
    x^2 + y^2 + z^2
      = g^2 / 3 + ((x - y)^2 + (y - z)^2 + (z - x)^2) / 3 := by
  have := three_sq_sub_sq x y z
  rw [h] at this
  linarith

/-- The antisymmetric part is non-negative for real (here: rational) entries, so the
balanced value is a lower bound for a single triple of scalars. -/
theorem cost_ge_balanced (x y z g : ℚ) (h : x + y + z = g) :
    g^2 / 3 ≤ x^2 + y^2 + z^2 := by
  have h1 : (0:ℚ) ≤ (x - y)^2 + (y - z)^2 + (z - x)^2 := by positivity
  have h2 := cost_split x y z g h
  linarith

/-! ### 3. The budget arithmetic -/

/-- The degree-ten budget: `24 * (3 g^5/8 - 6 g q^2) = 9 g^5 - 144 g q^2`. -/
theorem budget_eq (g q : ℚ) :
    24 * (3 * g^5 / 8 - 6 * g * q^2) = 9 * g^5 - 144 * g * q^2 := by
  ring

/-- The "balanced" cost, i.e. the value of `COST` when every antisymmetric part vanishes:
`(g^2/3) * (30 g^3 + 72 g q) = 10 g^5 + 24 g^3 q`. -/
theorem balanced_cost_eq (g q : ℚ) :
    (g^2 / 3) * (30 * g^3 + 72 * g * q) = 10 * g^5 + 24 * g^3 * q := by
  ring

/-- The gap: the balanced cost exceeds the budget by `g^5 + 24 g^3 q + 144 g q^2`,
so the antisymmetric part must supply at least that much (divided by three). -/
theorem balanced_minus_budget (g q : ℚ) :
    (10 * g^5 + 24 * g^3 * q) - (9 * g^5 - 144 * g * q^2)
      = g^5 + 24 * g^3 * q + 144 * g * q^2 := by
  ring

/-- Explicit numbers for `g = 7560`, `q = 19`. -/
theorem budget_num :
    9 * (7560:ℚ)^5 - 144 * 7560 * 19^2 = 222254972880605400960 := by
  norm_num

theorem balanced_cost_num :
    10 * (7560:ℚ)^5 + 24 * 7560^3 * 19 = 246950166896810496000 := by
  norm_num

/-! ### 4. The coordinates of a cyclic triple -/

/-- For a cyclic triple the three coordinates are symmetric functions of one element:
`X1 + X2 = e1 e2 - 3 e3`, `P = e1^3 - 3 e1 e2 + 6 e3`, and
`l := X1 + X2 - P = 4 e1 e2 - e1^3 - 9 e3`. -/
theorem ell_eq (e1 e2 e3 : ℚ) :
    (e1 * e2 - 3 * e3) - (e1^3 - 3 * e1 * e2 + 6 * e3)
      = 4 * e1 * e2 - e1^3 - 9 * e3 := by
  ring

/-- The extremal point: `e1 = g`, `e2 = g^2/4`, `e3 = 0` gives `l = 0`,
`P = g^3/4` and `X1 + X2 = g^3/4`. -/
theorem extremal_point (g : ℚ) :
    (4 * g * (g^2/4) - g^3 - 9 * 0 = 0)
      ∧ (g^3 - 3 * g * (g^2/4) + 6 * 0 = g^3 / 4)
      ∧ (g * (g^2/4) - 3 * 0 = g^3 / 4) := by
  refine ⟨by ring, by ring, by ring⟩

/-! ### 5. One cyclic triple cannot meet the three equations -/

/-- If a single cyclic triple with weight one satisfies `X1 + X2 = 2A` and `P = B`
with `A = g^3/8 + g q/2` and `B = g^3/4`, then `e3 = - g q`. -/
theorem cyclic_forces_e3 (g q e1 e2 e3 : ℚ) (h1 : e1 = g)
    (hX : e1 * e2 - 3 * e3 = 2 * (g^3/8 + g * q / 2))
    (hP : e1^3 - 3 * e1 * e2 + 6 * e3 = g^3 / 4) :
    e3 = - (g * q) := by
  subst h1
  linarith [hX, hP]

/-- With `g > 0` and `q > 0` the forced value is negative, so the norm of the element
is negative and the divisor class is not effective. -/
theorem cyclic_e3_neg (g q e1 e2 e3 : ℚ) (hg : 0 < g) (hq : 0 < q) (h1 : e1 = g)
    (hX : e1 * e2 - 3 * e3 = 2 * (g^3/8 + g * q / 2))
    (hP : e1^3 - 3 * e1 * e2 + 6 * e3 = g^3 / 4) :
    e3 < 0 := by
  rw [cyclic_forces_e3 g q e1 e2 e3 h1 hX hP]
  have : 0 < g * q := mul_pos hg hq
  linarith

/-- The same hypotheses also force `e2 = g^2/4 - 2 q` when `g ≠ 0`. -/
theorem cyclic_forces_e2 (g q e1 e2 e3 : ℚ) (hg : g ≠ 0) (h1 : e1 = g)
    (hX : e1 * e2 - 3 * e3 = 2 * (g^3/8 + g * q / 2))
    (hP : e1^3 - 3 * e1 * e2 + 6 * e3 = g^3 / 4) :
    e2 = g^2 / 4 - 2 * q := by
  have he3 := cyclic_forces_e3 g q e1 e2 e3 h1 hX hP
  rw [h1, he3] at hX
  have hexp : g * (g^2/4 - 2*q) = g^3/4 - 2*(g*q) := by ring
  have h2 : g * e2 = g^3/4 - 2*(g*q) := by linarith [hX]
  exact mul_left_cancel₀ hg (by rw [h2, hexp])

/-! ### 6. The glued pair -/

/-- If two triples share the divisor class `1` and each triple's classes sum to `g`,
the five distinct classes of the pair sum to `2 g - 1`. -/
theorem glued_pair_sum (g a b a' b' : ℚ) (h : 1 + a + b = g) (h' : 1 + a' + b' = g) :
    1 + a + b + a' + b' = 2 * g - 1 := by
  linarith

end DegreeTenBudget

#print axioms DegreeTenBudget.koszul_deg2
#print axioms DegreeTenBudget.koszul_deg2_fixed_sum
#print axioms DegreeTenBudget.three_sq_sub_sq
#print axioms DegreeTenBudget.cost_split
#print axioms DegreeTenBudget.cost_ge_balanced
#print axioms DegreeTenBudget.budget_eq
#print axioms DegreeTenBudget.balanced_cost_eq
#print axioms DegreeTenBudget.balanced_minus_budget
#print axioms DegreeTenBudget.budget_num
#print axioms DegreeTenBudget.balanced_cost_num
#print axioms DegreeTenBudget.ell_eq
#print axioms DegreeTenBudget.extremal_point
#print axioms DegreeTenBudget.cyclic_forces_e3
#print axioms DegreeTenBudget.cyclic_e3_neg
#print axioms DegreeTenBudget.cyclic_forces_e2
#print axioms DegreeTenBudget.glued_pair_sum
