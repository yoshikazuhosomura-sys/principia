/-
  Elementary algebra behind the glue window for the degree-ten and degree-twelve
  bookkeeping of a cycle assembled from triples of divisor classes in a rank-three
  commutative order.  No geometry, no sheaves, no cycles; nothing about the Hodge
  conjecture, algebraicity or semiregularity is asserted.

  Contents.
  1. Schur's inequality in the form  e1^3 - 4 e1 e2 + 9 e3 >= 0  for non-negative
     entries, with its two equality configurations (all equal, and one zero with the
     other two equal).  Consequence: the "outside-ness" of a cyclic triple,
     ell = 4 g e2 - g^3 - 9 e3, is never positive.
  2. The closed form of the outside-ness of a general triple in the three-places model,
       Out = (sum u)(sum v)(sum w) - (diagonal) - 4 (permanent),
     that it vanishes when the three vectors are constant, and that it is therefore
     divisible by any modulus at which the three places collapse.
  3. The trace form  Qform x y = 3 Tr(x y) - Tr x * Tr y  of the order
     Z[t]/(t^3 + t^2 - 6 t - 7)  and its value  38 (x^2 + x y + y^2)  on the span of
     t and t^2, with 38 = 2 * 19.
  4. The window: a lower bound on the glue from degree ten and an upper bound from
     degree twelve, the resulting bound on the cost, and the numeric instance.
-/
import Mathlib

namespace GlueWindow

/-! ### 1. Schur's inequality and the sign of the outside-ness of a cyclic triple -/

/-- The Schur expression is a sum of three products. -/
theorem schur_identity (x y z : ℚ) :
    (x + y + z)^3 - 4*(x + y + z)*(x*y + y*z + z*x) + 9*(x*y*z)
      = x*(x - y)*(x - z) + y*(y - x)*(y - z) + z*(z - x)*(z - y) := by
  ring

/-- Schur's inequality for the exponent one: the expression is non-negative on the
positive octant. -/
theorem schur_nonneg {x y z : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x + y + z)^3 - 4*(x + y + z)*(x*y + y*z + z*x) + 9*(x*y*z) := by
  rw [schur_identity]
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz <;>
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
        mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz]

/-- Equality when all three entries agree (the flat point). -/
theorem schur_eq_flat (t : ℚ) :
    (t + t + t)^3 - 4*(t + t + t)*(t*t + t*t + t*t) + 9*(t*t*t) = 0 := by ring

/-- Equality at the corner: one entry zero, the other two equal. -/
theorem schur_eq_corner (t : ℚ) :
    ((0:ℚ) + t + t)^3 - 4*(0 + t + t)*(0*t + t*t + t*0) + 9*(0*t*t) = 0 := by ring

/-- The outside-ness of a cyclic triple, written in the symmetric functions of its three
places, is never positive. -/
theorem ell_cyclic_nonpos {x y z g e2 e3 : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hg : g = x + y + z) (h2 : e2 = x*y + y*z + z*x) (h3 : e3 = x*y*z) :
    4*g*e2 - g^3 - 9*e3 ≤ 0 := by
  have h := schur_nonneg hx hy hz
  rw [hg, h2, h3]; linarith

/-! ### 2. The outside-ness of a general triple, and the collapse at a ramified modulus -/

/-- The three-places model: `u1 u2 u3` are the values of the first component of the
triple at the three places, and likewise for `v` and `w`. -/
def Out (u1 u2 u3 v1 v2 v3 w1 w2 w3 : ℤ) : ℤ :=
  (u1 + u2 + u3) * (v1 + v2 + v3) * (w1 + w2 + w3)
    - (u1*v1*w1 + u2*v2*w2 + u3*v3*w3)
    - 4 * (u1*v2*w3 + u1*v3*w2 + u2*v1*w3 + u2*v3*w1 + u3*v1*w2 + u3*v2*w1)

/-- On constant vectors (a triple of rational elements) the outside-ness vanishes: the
coefficients `27 - 3 - 4 * 6` cancel. -/
theorem out_const (a b c : ℤ) : Out a a a b b b c c c = 0 := by
  unfold Out; ring

/-- If the three places of each component agree modulo `p`, the outside-ness is divisible
by `p`.  At a totally ramified prime of a cyclic cubic order the three places do collapse
modulo that prime, so this applies with `p` its residue characteristic. -/
theorem out_dvd_of_collapse (p a b c u1 u2 u3 v1 v2 v3 w1 w2 w3 : ℤ)
    (hu1 : u1 ≡ a [ZMOD p]) (hu2 : u2 ≡ a [ZMOD p]) (hu3 : u3 ≡ a [ZMOD p])
    (hv1 : v1 ≡ b [ZMOD p]) (hv2 : v2 ≡ b [ZMOD p]) (hv3 : v3 ≡ b [ZMOD p])
    (hw1 : w1 ≡ c [ZMOD p]) (hw2 : w2 ≡ c [ZMOD p]) (hw3 : w3 ≡ c [ZMOD p]) :
    p ∣ Out u1 u2 u3 v1 v2 v3 w1 w2 w3 := by
  have key : Out u1 u2 u3 v1 v2 v3 w1 w2 w3 ≡ Out a a a b b b c c c [ZMOD p] := by
    unfold Out
    exact (((hu1.add hu2).add hu3).mul ((hv1.add hv2).add hv3)).mul
        (((hw1.add hw2).add hw3)) |>.sub
      ((((hu1.mul hv1).mul hw1).add ((hu2.mul hv2).mul hw2)).add ((hu3.mul hv3).mul hw3))
      |>.sub ((Int.ModEq.refl 4).mul
        ((((((hu1.mul hv2).mul hw3).add ((hu1.mul hv3).mul hw2)).add
          ((hu2.mul hv1).mul hw3)).add ((hu2.mul hv3).mul hw1)).add
          ((hu3.mul hv1).mul hw2) |>.add ((hu3.mul hv2).mul hw1)))
  rw [out_const a b c] at key
  exact (Int.modEq_zero_iff_dvd).mp key

/-! ### 3. The trace form of the order `Z[t]/(t^3 + t^2 - 6 t - 7)` -/

/-- Multiplication in the order, reducing with `t^3 = -t^2 + 6 t + 7` and
`t^4 = 7 t^2 + t - 7`. -/
def omul1 (a0 a1 a2 b0 b1 b2 : ℤ) : ℤ := a0*b0 + 7*(a1*b2 + a2*b1) - 7*(a2*b2)
def omul2 (a0 a1 a2 b0 b1 b2 : ℤ) : ℤ := a0*b1 + a1*b0 + 6*(a1*b2 + a2*b1) + a2*b2
def omul3 (a0 a1 a2 b0 b1 b2 : ℤ) : ℤ :=
  a0*b2 + a1*b1 + a2*b0 - (a1*b2 + a2*b1) + 7*(a2*b2)

/-- The trace of the order: `Tr 1 = 3`, `Tr t = -1`, `Tr t^2 = 13`. -/
def otr (c0 c1 c2 : ℤ) : ℤ := 3*c0 - c1 + 13*c2

/-- The trace form attached to the outside-ness of a triple with one rational component. -/
def Qform (a0 a1 a2 b0 b1 b2 : ℤ) : ℤ :=
  3 * otr (omul1 a0 a1 a2 b0 b1 b2) (omul2 a0 a1 a2 b0 b1 b2) (omul3 a0 a1 a2 b0 b1 b2)
    - otr a0 a1 a2 * otr b0 b1 b2

/-- On the span of `t` and `t^2` the trace form is `38 (x^2 + x y + y^2)`; here
`38 = 2 * 19` and `19` is the residue characteristic of the ramified prime. -/
theorem Qform_span (x y : ℤ) : Qform 0 x y 0 x y = 38 * (x^2 + x*y + y^2) := by
  unfold Qform otr omul1 omul2 omul3; ring

/-- Hence the trace form is divisible by `19` on that span. -/
theorem Qform_dvd_nineteen (x y : ℤ) : (19 : ℤ) ∣ Qform 0 x y 0 x y := by
  rw [Qform_span]; exact Dvd.intro (2 * (x^2 + x*y + y^2)) (by ring)

/-- The outside-ness of a triple with one rational component `n` is `- n * Qform`, so it
too is divisible by `19`. -/
theorem typeb_out_dvd (n x y : ℤ) : (19 : ℤ) ∣ (-(n * Qform 0 x y 0 x y)) := by
  rw [Qform_span]; exact Dvd.intro (-(n * (2 * (x^2 + x*y + y^2)))) (by ring)

/-! ### 4. The window on the glue -/

/-- Degree ten asks the glue to be at least `(cost - budget)/24`; degree twelve asks the
residual point count `n0 - rate * glue` to be non-negative.  Together they bound the cost. -/
theorem window_cost_bound {cost budget glue n0 rate : ℚ} (hrate : 0 < rate)
    (h10 : cost ≤ budget + 24 * glue) (h12 : 0 ≤ n0 - rate * glue) :
    rate * (cost - budget) ≤ 24 * n0 := by
  have h1 : cost - budget ≤ 24 * glue := by linarith
  have h2 : rate * (cost - budget) ≤ rate * (24 * glue) :=
    mul_le_mul_of_nonneg_left h1 hrate.le
  nlinarith [h12]

/-- Conversely the window is non-empty as soon as the cost obeys that bound. -/
theorem window_nonempty {cost budget n0 rate : ℚ} (hb : budget ≤ cost)
    (hc : rate * (cost - budget) ≤ 24 * n0) :
    ∃ glue : ℚ, 0 ≤ glue ∧ cost ≤ budget + 24 * glue ∧ 0 ≤ n0 - rate * glue := by
  refine ⟨(cost - budget)/24, by linarith, by linarith, ?_⟩
  have h : rate * ((cost - budget)/24) = rate * (cost - budget) / 24 := by ring
  rw [h]; linarith

/-- The numeric instance: the design's cost, the budget, the residual point count at zero
glue, the rate `(2 g + 1)/2 = 15121/2`, and one admissible glue value.  All four
inequalities of the window hold. -/
theorem window_numeric :
    (339730415179989962688 : ℚ) ≤ 222254972880605400960 + 24 * 6636257135593521408
    ∧ (0 : ℚ) ≤ 108872438127675098482368 - (15121/2) * 6636257135593521408
    ∧ (0 : ℚ) ≤ (222254972880605400960 - 339730415179989962688)/24 + 6636257135593521408
    ∧ (15121/2 : ℚ) * (339730415179989962688 - 222254972880605400960)
        ≤ 24 * 108872438127675098482368 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The outside-ness required of the whole design is `2 A - B = g q` when
`A = g^3/8 + g q/2` and `B = g^3/4`. -/
theorem outside_total (g q : ℚ) : 2 * (g^3/8 + g*q/2) - g^3/4 = g*q := by ring

/-- With `g = 7560` and `q = 19` that total is `143640 = 19 * 7560`; since every triple
contributes a multiple of `19`, the condition reads `sum y (ell/19) = g`. -/
theorem outside_total_num :
    2 * ((7560:ℚ)^3/8 + 7560*19/2) - (7560:ℚ)^3/4 = 19 * 7560 := by norm_num


/-! ### 5. A rank consequence for the degree-one part -/

/-- For an abelian variety the Hochschild cohomology is the free graded-commutative algebra
on its degree-one part, so `HH^2 = wedge^2 HH^1` with `dim HH^1 = 2 dim X`.  If `K` is a
`k`-dimensional subspace of a `12`-dimensional space `H`, then `K wedge H` has dimension
`k(k-1)/2 + k(12-k)`.  Asking that this stay inside a `12`-dimensional subspace forces
`k <= 1`. -/
theorem wedge_dim_le_one (k : ℕ) (hk : k ≤ 12)
    (h : k*(k-1)/2 + k*(12-k) ≤ 12) : k ≤ 1 := by
  interval_cases k <;> omega

/-- The dimension of `K wedge H` at the first two values, for the record. -/
theorem wedge_dim_values : (1*(1-1)/2 + 1*(12-1) = 11) ∧ (2*(2-1)/2 + 2*(12-2) = 21) := by
  refine ⟨by norm_num, by norm_num⟩

end GlueWindow

#print axioms GlueWindow.schur_identity
#print axioms GlueWindow.schur_nonneg
#print axioms GlueWindow.schur_eq_flat
#print axioms GlueWindow.schur_eq_corner
#print axioms GlueWindow.ell_cyclic_nonpos
#print axioms GlueWindow.out_const
#print axioms GlueWindow.out_dvd_of_collapse
#print axioms GlueWindow.Qform_span
#print axioms GlueWindow.Qform_dvd_nineteen
#print axioms GlueWindow.typeb_out_dvd
#print axioms GlueWindow.window_cost_bound
#print axioms GlueWindow.window_nonempty
#print axioms GlueWindow.window_numeric
#print axioms GlueWindow.outside_total
#print axioms GlueWindow.outside_total_num
#print axioms GlueWindow.wedge_dim_le_one
#print axioms GlueWindow.wedge_dim_values
