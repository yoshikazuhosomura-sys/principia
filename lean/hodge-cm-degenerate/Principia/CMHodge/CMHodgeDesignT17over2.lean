/-
  `t = 17/2` (q = 19, rational twist, totally split §12-type separation, the 27 rows of degrees 4..12, `O`-version):
  a test polynomial `q ∈ T_{17/2}` with `q(0) = 0` and `Δ_{ab} q < 0` on every admissible piece, given the box table.

  * `q` is `S₃`-symmetric of multidegree ≤ (2,2,2) and vanishes at the eight points `(17/2 ± i√19)³`
    (`q_mem`: `q = Σ_j g(u_j)·h_j`, `g(x) = (x − 17/2)² + 19`).  `p0 ∈ T_{17/2}` has `p0(0) = 1`.
    Orbit coefficients: c100 = 1806531/1600, c110 = −511949/1000, c111 = 421413/2500, c211 = −1, c221 = −339/2500,
    all others 0.
  * Outside the box: if one of the six coordinates of a positive piece `(a,b)` is `≥ 169`, then `Δq < 0`
    (`dq_neg_of_some_coord_ge`): with `a₁ = d + 169`, `−Δq` is a polynomial with positive coefficients
    (`dq_neg_shift`); the other five cases follow by the symmetry of `q`.  No norm condition is used.
  * Inside the box: ASSUMPTION `hbox` = the finite table "every piece with all coordinates `≤ 169` has `Δq < 0`".
    For pieces of totally positive elements of `O = Z[θ]` (θ³+θ²−6θ−7 = 0) this was checked exactly, outside Lean,
    on the 254,041 elements of the box (all 32,268,541,861 unordered pairs; integer arithmetic on characteristic
    polynomials).  Lean does not see `O`; it sees the table as a hypothesis.
  * `no_design_of_box_table`: positive coordinates + nonnegative weights + the two design equations for `q` and `p0`
    + the box table ⟹ `False`.
  The dictionary "design ⟺ `Σ n Δp = p(0)` for all `p ∈ T_t`" (earlier notes, on paper) is not formalised here.
-/
import Mathlib

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace DesignT17Half

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 17*x + (365/4)

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '1806531/1600', '-511949/1000', '421413/2500', '0', '0', '-1', '0', '-339/2500', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((1806531:ℝ)/1600)*u3 + ((1806531:ℝ)/1600)*u2 + ((-511949:ℝ)/1000)*u2*u3 + ((1806531:ℝ)/1600)*u1 + ((-511949:ℝ)/1000)*u1*u3 + ((-511949:ℝ)/1000)*u1*u2 + ((421413:ℝ)/2500)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + ((-339:ℝ)/2500)*u1*u2^2*u3^2 + (-1:ℝ)*u1^2*u2*u3 + ((-339:ℝ)/2500)*u1^2*u2*u3^2 + ((-339:ℝ)/2500)*u1^2*u2^2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3 + ((-339:ℝ)/2500)*u2*u3^2 + ((-339:ℝ)/2500)*u2^2*u3) + g u2 * (((24747:ℝ)/2000)*u3 + ((-8263:ℝ)/2500)*u1*u3 + ((-339:ℝ)/2500)*u1*u3^2) + g u3 * (((24747:ℝ)/2000)*u2 + ((24747:ℝ)/2000)*u1 + ((-7013:ℝ)/1250)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-68:ℝ)/1095)*u3 + ((4:ℝ)/1095)*u3^2 + ((-68:ℝ)/1095)*u2 + ((4:ℝ)/1095)*u2^2 + ((-68:ℝ)/1095)*u1 + ((4:ℝ)/1095)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((4:ℝ)/1095)) + g u2 * (((4:ℝ)/1095)) + g u3 * (((4:ℝ)/1095)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 169`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 169) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 169) a2 a3 b1 b2 b3 = -(((86519381:ℝ)/1000)*b3 + ((86519381:ℝ)/1000)*b2 + ((183703:ℝ)/2500)*b2*b3 + ((10104679:ℝ)/2500)*b2*b3^2 + ((10104679:ℝ)/2500)*b2^2*b3 + ((57291:ℝ)/2500)*b2^2*b3^2 + (338:ℝ)*b1*b2*b3 + ((57291:ℝ)/1250)*b1*b2*b3^2 + ((57291:ℝ)/1250)*b1*b2^2*b3 + ((2927151:ℝ)/5000)*a3*b2 + ((10104679:ℝ)/1250)*a3*b2*b3 + ((10104679:ℝ)/2500)*a3*b2^2 + ((57291:ℝ)/1250)*a3*b2^2*b3 + ((511949:ℝ)/1000)*a3*b1 + ((423587:ℝ)/2500)*a3*b1*b2 + ((58541:ℝ)/625)*a3*b1*b2*b3 + ((58541:ℝ)/1250)*a3*b1*b2^2 + ((339:ℝ)/1250)*a3*b1*b2^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((339:ℝ)/1250)*a3*b1^2*b2*b3 + ((339:ℝ)/2500)*a3*b1^2*b2^2 + ((10104679:ℝ)/2500)*a3^2*b2 + ((57291:ℝ)/2500)*a3^2*b2^2 + ((58541:ℝ)/1250)*a3^2*b1*b2 + ((339:ℝ)/2500)*a3^2*b1*b2^2 + ((339:ℝ)/2500)*a3^2*b1^2*b2 + ((2927151:ℝ)/5000)*a2*b3 + ((10104679:ℝ)/2500)*a2*b3^2 + ((10104679:ℝ)/1250)*a2*b2*b3 + ((57291:ℝ)/1250)*a2*b2*b3^2 + ((511949:ℝ)/1000)*a2*b1 + ((423587:ℝ)/2500)*a2*b1*b3 + ((58541:ℝ)/1250)*a2*b1*b3^2 + ((58541:ℝ)/625)*a2*b1*b2*b3 + ((339:ℝ)/1250)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((339:ℝ)/2500)*a2*b1^2*b3^2 + ((339:ℝ)/1250)*a2*b1^2*b2*b3 + ((10104679:ℝ)/1250)*a2*a3*b3 + ((10104679:ℝ)/1250)*a2*a3*b2 + ((57291:ℝ)/625)*a2*a3*b2*b3 + ((423587:ℝ)/2500)*a2*a3*b1 + ((58541:ℝ)/625)*a2*a3*b1*b3 + ((58541:ℝ)/625)*a2*a3*b1*b2 + ((339:ℝ)/625)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((339:ℝ)/1250)*a2*a3*b1^2*b3 + ((339:ℝ)/1250)*a2*a3*b1^2*b2 + ((57291:ℝ)/1250)*a2*a3^2*b2 + ((58541:ℝ)/1250)*a2*a3^2*b1 + ((339:ℝ)/1250)*a2*a3^2*b1*b2 + ((339:ℝ)/2500)*a2*a3^2*b1^2 + ((10104679:ℝ)/2500)*a2^2*b3 + ((57291:ℝ)/2500)*a2^2*b3^2 + ((58541:ℝ)/1250)*a2^2*b1*b3 + ((339:ℝ)/2500)*a2^2*b1*b3^2 + ((339:ℝ)/2500)*a2^2*b1^2*b3 + ((57291:ℝ)/1250)*a2^2*a3*b3 + ((58541:ℝ)/1250)*a2^2*a3*b1 + ((339:ℝ)/1250)*a2^2*a3*b1*b3 + ((339:ℝ)/2500)*a2^2*a3*b1^2 + ((339:ℝ)/2500)*a2^2*a3^2*b1 + ((511949:ℝ)/1000)*d*b3 + ((511949:ℝ)/1000)*d*b2 + ((423587:ℝ)/2500)*d*b2*b3 + ((58541:ℝ)/1250)*d*b2*b3^2 + ((58541:ℝ)/1250)*d*b2^2*b3 + ((339:ℝ)/2500)*d*b2^2*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((339:ℝ)/1250)*d*b1*b2*b3^2 + ((339:ℝ)/1250)*d*b1*b2^2*b3 + ((423587:ℝ)/2500)*d*a3*b2 + ((58541:ℝ)/625)*d*a3*b2*b3 + ((58541:ℝ)/1250)*d*a3*b2^2 + ((339:ℝ)/1250)*d*a3*b2^2*b3 + (2:ℝ)*d*a3*b1*b2 + ((339:ℝ)/625)*d*a3*b1*b2*b3 + ((339:ℝ)/1250)*d*a3*b1*b2^2 + ((58541:ℝ)/1250)*d*a3^2*b2 + ((339:ℝ)/2500)*d*a3^2*b2^2 + ((339:ℝ)/1250)*d*a3^2*b1*b2 + ((423587:ℝ)/2500)*d*a2*b3 + ((58541:ℝ)/1250)*d*a2*b3^2 + ((58541:ℝ)/625)*d*a2*b2*b3 + ((339:ℝ)/1250)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((339:ℝ)/1250)*d*a2*b1*b3^2 + ((339:ℝ)/625)*d*a2*b1*b2*b3 + ((58541:ℝ)/625)*d*a2*a3*b3 + ((58541:ℝ)/625)*d*a2*a3*b2 + ((339:ℝ)/625)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((339:ℝ)/625)*d*a2*a3*b1*b3 + ((339:ℝ)/625)*d*a2*a3*b1*b2 + ((339:ℝ)/1250)*d*a2*a3^2*b2 + ((339:ℝ)/1250)*d*a2*a3^2*b1 + ((58541:ℝ)/1250)*d*a2^2*b3 + ((339:ℝ)/2500)*d*a2^2*b3^2 + ((339:ℝ)/1250)*d*a2^2*b1*b3 + ((339:ℝ)/1250)*d*a2^2*a3*b3 + ((339:ℝ)/1250)*d*a2^2*a3*b1 + (1:ℝ)*d^2*b2*b3 + ((339:ℝ)/2500)*d^2*b2*b3^2 + ((339:ℝ)/2500)*d^2*b2^2*b3 + (1:ℝ)*d^2*a3*b2 + ((339:ℝ)/1250)*d^2*a3*b2*b3 + ((339:ℝ)/2500)*d^2*a3*b2^2 + ((339:ℝ)/2500)*d^2*a3^2*b2 + (1:ℝ)*d^2*a2*b3 + ((339:ℝ)/2500)*d^2*a2*b3^2 + ((339:ℝ)/1250)*d^2*a2*b2*b3 + ((339:ℝ)/1250)*d^2*a2*a3*b3 + ((339:ℝ)/1250)*d^2*a2*a3*b2 + ((339:ℝ)/2500)*d^2*a2^2*b3) := by
    unfold dq q; ring
  have hp : 0 < ((86519381:ℝ)/1000)*b3 + ((86519381:ℝ)/1000)*b2 + ((183703:ℝ)/2500)*b2*b3 + ((10104679:ℝ)/2500)*b2*b3^2 + ((10104679:ℝ)/2500)*b2^2*b3 + ((57291:ℝ)/2500)*b2^2*b3^2 + (338:ℝ)*b1*b2*b3 + ((57291:ℝ)/1250)*b1*b2*b3^2 + ((57291:ℝ)/1250)*b1*b2^2*b3 + ((2927151:ℝ)/5000)*a3*b2 + ((10104679:ℝ)/1250)*a3*b2*b3 + ((10104679:ℝ)/2500)*a3*b2^2 + ((57291:ℝ)/1250)*a3*b2^2*b3 + ((511949:ℝ)/1000)*a3*b1 + ((423587:ℝ)/2500)*a3*b1*b2 + ((58541:ℝ)/625)*a3*b1*b2*b3 + ((58541:ℝ)/1250)*a3*b1*b2^2 + ((339:ℝ)/1250)*a3*b1*b2^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((339:ℝ)/1250)*a3*b1^2*b2*b3 + ((339:ℝ)/2500)*a3*b1^2*b2^2 + ((10104679:ℝ)/2500)*a3^2*b2 + ((57291:ℝ)/2500)*a3^2*b2^2 + ((58541:ℝ)/1250)*a3^2*b1*b2 + ((339:ℝ)/2500)*a3^2*b1*b2^2 + ((339:ℝ)/2500)*a3^2*b1^2*b2 + ((2927151:ℝ)/5000)*a2*b3 + ((10104679:ℝ)/2500)*a2*b3^2 + ((10104679:ℝ)/1250)*a2*b2*b3 + ((57291:ℝ)/1250)*a2*b2*b3^2 + ((511949:ℝ)/1000)*a2*b1 + ((423587:ℝ)/2500)*a2*b1*b3 + ((58541:ℝ)/1250)*a2*b1*b3^2 + ((58541:ℝ)/625)*a2*b1*b2*b3 + ((339:ℝ)/1250)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((339:ℝ)/2500)*a2*b1^2*b3^2 + ((339:ℝ)/1250)*a2*b1^2*b2*b3 + ((10104679:ℝ)/1250)*a2*a3*b3 + ((10104679:ℝ)/1250)*a2*a3*b2 + ((57291:ℝ)/625)*a2*a3*b2*b3 + ((423587:ℝ)/2500)*a2*a3*b1 + ((58541:ℝ)/625)*a2*a3*b1*b3 + ((58541:ℝ)/625)*a2*a3*b1*b2 + ((339:ℝ)/625)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((339:ℝ)/1250)*a2*a3*b1^2*b3 + ((339:ℝ)/1250)*a2*a3*b1^2*b2 + ((57291:ℝ)/1250)*a2*a3^2*b2 + ((58541:ℝ)/1250)*a2*a3^2*b1 + ((339:ℝ)/1250)*a2*a3^2*b1*b2 + ((339:ℝ)/2500)*a2*a3^2*b1^2 + ((10104679:ℝ)/2500)*a2^2*b3 + ((57291:ℝ)/2500)*a2^2*b3^2 + ((58541:ℝ)/1250)*a2^2*b1*b3 + ((339:ℝ)/2500)*a2^2*b1*b3^2 + ((339:ℝ)/2500)*a2^2*b1^2*b3 + ((57291:ℝ)/1250)*a2^2*a3*b3 + ((58541:ℝ)/1250)*a2^2*a3*b1 + ((339:ℝ)/1250)*a2^2*a3*b1*b3 + ((339:ℝ)/2500)*a2^2*a3*b1^2 + ((339:ℝ)/2500)*a2^2*a3^2*b1 + ((511949:ℝ)/1000)*d*b3 + ((511949:ℝ)/1000)*d*b2 + ((423587:ℝ)/2500)*d*b2*b3 + ((58541:ℝ)/1250)*d*b2*b3^2 + ((58541:ℝ)/1250)*d*b2^2*b3 + ((339:ℝ)/2500)*d*b2^2*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((339:ℝ)/1250)*d*b1*b2*b3^2 + ((339:ℝ)/1250)*d*b1*b2^2*b3 + ((423587:ℝ)/2500)*d*a3*b2 + ((58541:ℝ)/625)*d*a3*b2*b3 + ((58541:ℝ)/1250)*d*a3*b2^2 + ((339:ℝ)/1250)*d*a3*b2^2*b3 + (2:ℝ)*d*a3*b1*b2 + ((339:ℝ)/625)*d*a3*b1*b2*b3 + ((339:ℝ)/1250)*d*a3*b1*b2^2 + ((58541:ℝ)/1250)*d*a3^2*b2 + ((339:ℝ)/2500)*d*a3^2*b2^2 + ((339:ℝ)/1250)*d*a3^2*b1*b2 + ((423587:ℝ)/2500)*d*a2*b3 + ((58541:ℝ)/1250)*d*a2*b3^2 + ((58541:ℝ)/625)*d*a2*b2*b3 + ((339:ℝ)/1250)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((339:ℝ)/1250)*d*a2*b1*b3^2 + ((339:ℝ)/625)*d*a2*b1*b2*b3 + ((58541:ℝ)/625)*d*a2*a3*b3 + ((58541:ℝ)/625)*d*a2*a3*b2 + ((339:ℝ)/625)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((339:ℝ)/625)*d*a2*a3*b1*b3 + ((339:ℝ)/625)*d*a2*a3*b1*b2 + ((339:ℝ)/1250)*d*a2*a3^2*b2 + ((339:ℝ)/1250)*d*a2*a3^2*b1 + ((58541:ℝ)/1250)*d*a2^2*b3 + ((339:ℝ)/2500)*d*a2^2*b3^2 + ((339:ℝ)/1250)*d*a2^2*b1*b3 + ((339:ℝ)/1250)*d*a2^2*a3*b3 + ((339:ℝ)/1250)*d*a2^2*a3*b1 + (1:ℝ)*d^2*b2*b3 + ((339:ℝ)/2500)*d^2*b2*b3^2 + ((339:ℝ)/2500)*d^2*b2^2*b3 + (1:ℝ)*d^2*a3*b2 + ((339:ℝ)/1250)*d^2*a3*b2*b3 + ((339:ℝ)/2500)*d^2*a3*b2^2 + ((339:ℝ)/2500)*d^2*a3^2*b2 + (1:ℝ)*d^2*a2*b3 + ((339:ℝ)/2500)*d^2*a2*b3^2 + ((339:ℝ)/1250)*d^2*a2*b2*b3 + ((339:ℝ)/1250)*d^2*a2*a3*b3 + ((339:ℝ)/1250)*d^2*a2*a3*b2 + ((339:ℝ)/2500)*d^2*a2^2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 169 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 169 := ⟨a1 - 169, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 169`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 169 ≤ a1 ∨ 169 ≤ a2 ∨ 169 ≤ a3 ∨ 169 ≤ b1 ∨ 169 ≤ b2 ∨ 169 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 169`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 169 → a2 i ≤ 169 → a3 i ≤ 169 → b1 i ≤ 169 → b2 i ≤ 169 → b3 i ≤ 169 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 169 ∧ a2 i ≤ 169 ∧ a3 i ≤ 169 ∧ b1 i ≤ 169 ∧ b2 i ≤ 169 ∧ b3 i ≤ 169
    · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hall; exact hbox i hi c1 c2 c3 c4 c5 c6
    · apply dq_neg_of_some_coord_ge _ _ _ _ _ _ p1 p2 p3 p4 p5 p6
      by_contra hc; simp only [not_or, not_le] at hc; exact hall ⟨hc.1.le, hc.2.1.le, hc.2.2.1.le, hc.2.2.2.1.le, hc.2.2.2.2.1.le, hc.2.2.2.2.2.le⟩
  have hterm : ∀ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) ≤ 0 :=
    fun i hi => mul_nonpos_of_nonneg_of_nonpos (hn i hi) (hneg i hi).le
  rw [q_zero] at hq
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hq
  have hn0 : ∀ i ∈ s, n i = 0 := by
    intro i hi
    rcases mul_eq_zero.1 (hz i hi) with h | h
    · exact h
    · exact absurd h (hneg i hi).ne
  have : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hn0 i hi, zero_mul])
  rw [this, p0_zero] at hp; norm_num at hp

end DesignT17Half

-- axioms (every theorem)
#print axioms DesignT17Half.q_mem
#print axioms DesignT17Half.q_zero
#print axioms DesignT17Half.p0_mem
#print axioms DesignT17Half.p0_zero
#print axioms DesignT17Half.dq_neg_shift
#print axioms DesignT17Half.dq_neg_of_a1_ge
#print axioms DesignT17Half.dq_perm12
#print axioms DesignT17Half.dq_perm13
#print axioms DesignT17Half.dq_swap
#print axioms DesignT17Half.dq_neg_of_some_coord_ge
#print axioms DesignT17Half.no_design_of_box_table
