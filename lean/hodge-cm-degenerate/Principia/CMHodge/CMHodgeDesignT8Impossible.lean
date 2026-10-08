/-
  `t = 8` (q = 19, rational twist, totally split §12-type separation, the 27 rows of degrees 4..12, `O`-version):
  a strict test polynomial `q ∈ T_8` with `q(0) = 0` and `Δ_{ab} q < 0` on every admissible piece.

  * `q` is `S₃`-symmetric of multidegree ≤ (2,2,2) and vanishes at the eight points `(8 ± i√19)³`
    (`q_mem`: `q = Σ_j g(u_j)·h_j`, `g(x) = (x−8)² + 19`).  `p0 ∈ T_8` has `p0(0) = 1` (`p0_mem`, `p0_zero`).
  * Outside the box: if one of the six coordinates of a positive piece `(a,b)` is `≥ 82`, then `Δq < 0`
    (`dq_neg_of_some_coord_ge`): with `a₁ = d + 82`, `−Δq` is a polynomial with positive coefficients
    (`dq_neg_shift`), and the other five cases follow by the symmetry of `q` (`dq_perm12`, `dq_perm13`, `dq_swap`).
    No norm condition is used here.
  * Inside the box: ASSUMPTION `hbox` = the finite table "every piece with all coordinates `≤ 82` has `Δq < 0`".
    For pieces of totally positive elements of `O = Z[θ]` (θ³+θ²−6θ−7 = 0) this was checked exactly, outside Lean,
    on all 421,094,710 unordered pairs of the 29,020 elements of the box (integer arithmetic on characteristic
    polynomials).  Lean does not see `O`; it sees the table as a hypothesis.
  * `no_design_of_box_table`: positive coordinates + nonnegative weights + the two design equations for `q` and `p0`
    + the box table ⟹ `False`.
  The dictionary "design ⟺ `Σ n Δp = p(0)` for all `p ∈ T_t`" (earlier notes, on paper) is not formalised here.
  The same mechanism, with its own `q`, box bound `R` and (outside Lean) exact box table, is repeated for
    `DesignT3Control` (t = 3, R = 19), `DesignT4` (t = 4, R = 25), `DesignT5` (R = 31),
    `DesignT6` (R = 37), `DesignT13Half` (t = 13/2, R = 40), `DesignT7` (R = 52), `DesignT15Half` (t = 15/2, R = 66),
    `DesignT31Quarter` (t = 31/4, R = 73), `DesignT33Quarter` (t = 33/4, R = 103).  t = 3 is the positive control (system D3 of the earlier notes).
-/
import Mathlib

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace DesignT8

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 16*x + 83

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '2969159/10000', '-123421/625', '50688/625', '0', '0', '-1', '0', '-431/10000', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((2969159:ℝ)/10000)*u3 + ((2969159:ℝ)/10000)*u2 + ((-123421:ℝ)/625)*u2*u3 + ((2969159:ℝ)/10000)*u1 + ((-123421:ℝ)/625)*u1*u3 + ((-123421:ℝ)/625)*u1*u2 + ((50688:ℝ)/625)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + ((-431:ℝ)/10000)*u1*u2^2*u3^2 + (-1:ℝ)*u1^2*u2*u3 + ((-431:ℝ)/10000)*u1^2*u2*u3^2 + ((-431:ℝ)/10000)*u1^2*u2^2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3 + ((-431:ℝ)/10000)*u2*u3^2 + ((-431:ℝ)/10000)*u2^2*u3) + g u2 * (((35773:ℝ)/10000)*u3 + ((-1056:ℝ)/625)*u1*u3 + ((-431:ℝ)/10000)*u1*u3^2) + g u3 * (((35773:ℝ)/10000)*u2 + ((35773:ℝ)/10000)*u1 + ((-1487:ℝ)/625)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-16:ℝ)/249)*u3 + ((1:ℝ)/249)*u3^2 + ((-16:ℝ)/249)*u2 + ((1:ℝ)/249)*u2^2 + ((-16:ℝ)/249)*u1 + ((1:ℝ)/249)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((1:ℝ)/249)) + g u2 * (((1:ℝ)/249)) + g u3 * (((1:ℝ)/249)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 82`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 82) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 82) a2 a3 b1 b2 b3 = -(((10120522:ℝ)/625)*b3 + ((10120522:ℝ)/625)*b2 + ((46084:ℝ)/625)*b2*b3 + ((929511:ℝ)/2500)*b2*b3^2 + ((929511:ℝ)/2500)*b2^2*b3 + ((17671:ℝ)/5000)*b2^2*b3^2 + (164:ℝ)*b1*b2*b3 + ((17671:ℝ)/2500)*b1*b2*b3^2 + ((17671:ℝ)/2500)*b1*b2^2*b3 + ((33901:ℝ)/125)*a3*b2 + ((929511:ℝ)/1250)*a3*b2*b3 + ((929511:ℝ)/2500)*a3*b2^2 + ((17671:ℝ)/2500)*a3*b2^2*b3 + ((123421:ℝ)/625)*a3*b1 + ((51812:ℝ)/625)*a3*b1*b2 + ((20171:ℝ)/1250)*a3*b1*b2*b3 + ((20171:ℝ)/2500)*a3*b1*b2^2 + ((431:ℝ)/5000)*a3*b1*b2^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((431:ℝ)/5000)*a3*b1^2*b2*b3 + ((431:ℝ)/10000)*a3*b1^2*b2^2 + ((929511:ℝ)/2500)*a3^2*b2 + ((17671:ℝ)/5000)*a3^2*b2^2 + ((20171:ℝ)/2500)*a3^2*b1*b2 + ((431:ℝ)/10000)*a3^2*b1*b2^2 + ((431:ℝ)/10000)*a3^2*b1^2*b2 + ((33901:ℝ)/125)*a2*b3 + ((929511:ℝ)/2500)*a2*b3^2 + ((929511:ℝ)/1250)*a2*b2*b3 + ((17671:ℝ)/2500)*a2*b2*b3^2 + ((123421:ℝ)/625)*a2*b1 + ((51812:ℝ)/625)*a2*b1*b3 + ((20171:ℝ)/2500)*a2*b1*b3^2 + ((20171:ℝ)/1250)*a2*b1*b2*b3 + ((431:ℝ)/5000)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((431:ℝ)/10000)*a2*b1^2*b3^2 + ((431:ℝ)/5000)*a2*b1^2*b2*b3 + ((929511:ℝ)/1250)*a2*a3*b3 + ((929511:ℝ)/1250)*a2*a3*b2 + ((17671:ℝ)/1250)*a2*a3*b2*b3 + ((51812:ℝ)/625)*a2*a3*b1 + ((20171:ℝ)/1250)*a2*a3*b1*b3 + ((20171:ℝ)/1250)*a2*a3*b1*b2 + ((431:ℝ)/2500)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((431:ℝ)/5000)*a2*a3*b1^2*b3 + ((431:ℝ)/5000)*a2*a3*b1^2*b2 + ((17671:ℝ)/2500)*a2*a3^2*b2 + ((20171:ℝ)/2500)*a2*a3^2*b1 + ((431:ℝ)/5000)*a2*a3^2*b1*b2 + ((431:ℝ)/10000)*a2*a3^2*b1^2 + ((929511:ℝ)/2500)*a2^2*b3 + ((17671:ℝ)/5000)*a2^2*b3^2 + ((20171:ℝ)/2500)*a2^2*b1*b3 + ((431:ℝ)/10000)*a2^2*b1*b3^2 + ((431:ℝ)/10000)*a2^2*b1^2*b3 + ((17671:ℝ)/2500)*a2^2*a3*b3 + ((20171:ℝ)/2500)*a2^2*a3*b1 + ((431:ℝ)/5000)*a2^2*a3*b1*b3 + ((431:ℝ)/10000)*a2^2*a3*b1^2 + ((431:ℝ)/10000)*a2^2*a3^2*b1 + ((123421:ℝ)/625)*d*b3 + ((123421:ℝ)/625)*d*b2 + ((51812:ℝ)/625)*d*b2*b3 + ((20171:ℝ)/2500)*d*b2*b3^2 + ((20171:ℝ)/2500)*d*b2^2*b3 + ((431:ℝ)/10000)*d*b2^2*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((431:ℝ)/5000)*d*b1*b2*b3^2 + ((431:ℝ)/5000)*d*b1*b2^2*b3 + ((51812:ℝ)/625)*d*a3*b2 + ((20171:ℝ)/1250)*d*a3*b2*b3 + ((20171:ℝ)/2500)*d*a3*b2^2 + ((431:ℝ)/5000)*d*a3*b2^2*b3 + (2:ℝ)*d*a3*b1*b2 + ((431:ℝ)/2500)*d*a3*b1*b2*b3 + ((431:ℝ)/5000)*d*a3*b1*b2^2 + ((20171:ℝ)/2500)*d*a3^2*b2 + ((431:ℝ)/10000)*d*a3^2*b2^2 + ((431:ℝ)/5000)*d*a3^2*b1*b2 + ((51812:ℝ)/625)*d*a2*b3 + ((20171:ℝ)/2500)*d*a2*b3^2 + ((20171:ℝ)/1250)*d*a2*b2*b3 + ((431:ℝ)/5000)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((431:ℝ)/5000)*d*a2*b1*b3^2 + ((431:ℝ)/2500)*d*a2*b1*b2*b3 + ((20171:ℝ)/1250)*d*a2*a3*b3 + ((20171:ℝ)/1250)*d*a2*a3*b2 + ((431:ℝ)/2500)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((431:ℝ)/2500)*d*a2*a3*b1*b3 + ((431:ℝ)/2500)*d*a2*a3*b1*b2 + ((431:ℝ)/5000)*d*a2*a3^2*b2 + ((431:ℝ)/5000)*d*a2*a3^2*b1 + ((20171:ℝ)/2500)*d*a2^2*b3 + ((431:ℝ)/10000)*d*a2^2*b3^2 + ((431:ℝ)/5000)*d*a2^2*b1*b3 + ((431:ℝ)/5000)*d*a2^2*a3*b3 + ((431:ℝ)/5000)*d*a2^2*a3*b1 + (1:ℝ)*d^2*b2*b3 + ((431:ℝ)/10000)*d^2*b2*b3^2 + ((431:ℝ)/10000)*d^2*b2^2*b3 + (1:ℝ)*d^2*a3*b2 + ((431:ℝ)/5000)*d^2*a3*b2*b3 + ((431:ℝ)/10000)*d^2*a3*b2^2 + ((431:ℝ)/10000)*d^2*a3^2*b2 + (1:ℝ)*d^2*a2*b3 + ((431:ℝ)/10000)*d^2*a2*b3^2 + ((431:ℝ)/5000)*d^2*a2*b2*b3 + ((431:ℝ)/5000)*d^2*a2*a3*b3 + ((431:ℝ)/5000)*d^2*a2*a3*b2 + ((431:ℝ)/10000)*d^2*a2^2*b3) := by
    unfold dq q; ring
  have hp : 0 < ((10120522:ℝ)/625)*b3 + ((10120522:ℝ)/625)*b2 + ((46084:ℝ)/625)*b2*b3 + ((929511:ℝ)/2500)*b2*b3^2 + ((929511:ℝ)/2500)*b2^2*b3 + ((17671:ℝ)/5000)*b2^2*b3^2 + (164:ℝ)*b1*b2*b3 + ((17671:ℝ)/2500)*b1*b2*b3^2 + ((17671:ℝ)/2500)*b1*b2^2*b3 + ((33901:ℝ)/125)*a3*b2 + ((929511:ℝ)/1250)*a3*b2*b3 + ((929511:ℝ)/2500)*a3*b2^2 + ((17671:ℝ)/2500)*a3*b2^2*b3 + ((123421:ℝ)/625)*a3*b1 + ((51812:ℝ)/625)*a3*b1*b2 + ((20171:ℝ)/1250)*a3*b1*b2*b3 + ((20171:ℝ)/2500)*a3*b1*b2^2 + ((431:ℝ)/5000)*a3*b1*b2^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((431:ℝ)/5000)*a3*b1^2*b2*b3 + ((431:ℝ)/10000)*a3*b1^2*b2^2 + ((929511:ℝ)/2500)*a3^2*b2 + ((17671:ℝ)/5000)*a3^2*b2^2 + ((20171:ℝ)/2500)*a3^2*b1*b2 + ((431:ℝ)/10000)*a3^2*b1*b2^2 + ((431:ℝ)/10000)*a3^2*b1^2*b2 + ((33901:ℝ)/125)*a2*b3 + ((929511:ℝ)/2500)*a2*b3^2 + ((929511:ℝ)/1250)*a2*b2*b3 + ((17671:ℝ)/2500)*a2*b2*b3^2 + ((123421:ℝ)/625)*a2*b1 + ((51812:ℝ)/625)*a2*b1*b3 + ((20171:ℝ)/2500)*a2*b1*b3^2 + ((20171:ℝ)/1250)*a2*b1*b2*b3 + ((431:ℝ)/5000)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((431:ℝ)/10000)*a2*b1^2*b3^2 + ((431:ℝ)/5000)*a2*b1^2*b2*b3 + ((929511:ℝ)/1250)*a2*a3*b3 + ((929511:ℝ)/1250)*a2*a3*b2 + ((17671:ℝ)/1250)*a2*a3*b2*b3 + ((51812:ℝ)/625)*a2*a3*b1 + ((20171:ℝ)/1250)*a2*a3*b1*b3 + ((20171:ℝ)/1250)*a2*a3*b1*b2 + ((431:ℝ)/2500)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((431:ℝ)/5000)*a2*a3*b1^2*b3 + ((431:ℝ)/5000)*a2*a3*b1^2*b2 + ((17671:ℝ)/2500)*a2*a3^2*b2 + ((20171:ℝ)/2500)*a2*a3^2*b1 + ((431:ℝ)/5000)*a2*a3^2*b1*b2 + ((431:ℝ)/10000)*a2*a3^2*b1^2 + ((929511:ℝ)/2500)*a2^2*b3 + ((17671:ℝ)/5000)*a2^2*b3^2 + ((20171:ℝ)/2500)*a2^2*b1*b3 + ((431:ℝ)/10000)*a2^2*b1*b3^2 + ((431:ℝ)/10000)*a2^2*b1^2*b3 + ((17671:ℝ)/2500)*a2^2*a3*b3 + ((20171:ℝ)/2500)*a2^2*a3*b1 + ((431:ℝ)/5000)*a2^2*a3*b1*b3 + ((431:ℝ)/10000)*a2^2*a3*b1^2 + ((431:ℝ)/10000)*a2^2*a3^2*b1 + ((123421:ℝ)/625)*d*b3 + ((123421:ℝ)/625)*d*b2 + ((51812:ℝ)/625)*d*b2*b3 + ((20171:ℝ)/2500)*d*b2*b3^2 + ((20171:ℝ)/2500)*d*b2^2*b3 + ((431:ℝ)/10000)*d*b2^2*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((431:ℝ)/5000)*d*b1*b2*b3^2 + ((431:ℝ)/5000)*d*b1*b2^2*b3 + ((51812:ℝ)/625)*d*a3*b2 + ((20171:ℝ)/1250)*d*a3*b2*b3 + ((20171:ℝ)/2500)*d*a3*b2^2 + ((431:ℝ)/5000)*d*a3*b2^2*b3 + (2:ℝ)*d*a3*b1*b2 + ((431:ℝ)/2500)*d*a3*b1*b2*b3 + ((431:ℝ)/5000)*d*a3*b1*b2^2 + ((20171:ℝ)/2500)*d*a3^2*b2 + ((431:ℝ)/10000)*d*a3^2*b2^2 + ((431:ℝ)/5000)*d*a3^2*b1*b2 + ((51812:ℝ)/625)*d*a2*b3 + ((20171:ℝ)/2500)*d*a2*b3^2 + ((20171:ℝ)/1250)*d*a2*b2*b3 + ((431:ℝ)/5000)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((431:ℝ)/5000)*d*a2*b1*b3^2 + ((431:ℝ)/2500)*d*a2*b1*b2*b3 + ((20171:ℝ)/1250)*d*a2*a3*b3 + ((20171:ℝ)/1250)*d*a2*a3*b2 + ((431:ℝ)/2500)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((431:ℝ)/2500)*d*a2*a3*b1*b3 + ((431:ℝ)/2500)*d*a2*a3*b1*b2 + ((431:ℝ)/5000)*d*a2*a3^2*b2 + ((431:ℝ)/5000)*d*a2*a3^2*b1 + ((20171:ℝ)/2500)*d*a2^2*b3 + ((431:ℝ)/10000)*d*a2^2*b3^2 + ((431:ℝ)/5000)*d*a2^2*b1*b3 + ((431:ℝ)/5000)*d*a2^2*a3*b3 + ((431:ℝ)/5000)*d*a2^2*a3*b1 + (1:ℝ)*d^2*b2*b3 + ((431:ℝ)/10000)*d^2*b2*b3^2 + ((431:ℝ)/10000)*d^2*b2^2*b3 + (1:ℝ)*d^2*a3*b2 + ((431:ℝ)/5000)*d^2*a3*b2*b3 + ((431:ℝ)/10000)*d^2*a3*b2^2 + ((431:ℝ)/10000)*d^2*a3^2*b2 + (1:ℝ)*d^2*a2*b3 + ((431:ℝ)/10000)*d^2*a2*b3^2 + ((431:ℝ)/5000)*d^2*a2*b2*b3 + ((431:ℝ)/5000)*d^2*a2*a3*b3 + ((431:ℝ)/5000)*d^2*a2*a3*b2 + ((431:ℝ)/10000)*d^2*a2^2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 82 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 82 := ⟨a1 - 82, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 82`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 82 ≤ a1 ∨ 82 ≤ a2 ∨ 82 ≤ a3 ∨ 82 ≤ b1 ∨ 82 ≤ b2 ∨ 82 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 82`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 82 → a2 i ≤ 82 → a3 i ≤ 82 → b1 i ≤ 82 → b2 i ≤ 82 → b3 i ≤ 82 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 82 ∧ a2 i ≤ 82 ∧ a3 i ≤ 82 ∧ b1 i ≤ 82 ∧ b2 i ≤ 82 ∧ b3 i ≤ 82
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

end DesignT8

namespace DesignT3Control

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 6*x + 28

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '0', '-28', '18', '0', '0', '-1', '0', '0', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := (-28:ℝ)*u2*u3 + (-28:ℝ)*u1*u3 + (-28:ℝ)*u1*u2 + (18:ℝ)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + (-1:ℝ)*u1^2*u2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3) + g u2 * ((-1:ℝ)*u1*u3) + g u3 * ((-1:ℝ)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-1:ℝ)/14)*u3 + ((1:ℝ)/84)*u3^2 + ((-1:ℝ)/14)*u2 + ((1:ℝ)/84)*u2^2 + ((-1:ℝ)/14)*u1 + ((1:ℝ)/84)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((1:ℝ)/84)) + g u2 * (((1:ℝ)/84)) + g u3 * (((1:ℝ)/84)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 19`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 19) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 19) a2 a3 b1 b2 b3 = -((532:ℝ)*b3 + (532:ℝ)*b2 + (19:ℝ)*b2*b3 + (19:ℝ)*b2*b3^2 + (19:ℝ)*b2^2*b3 + (38:ℝ)*b1*b2*b3 + (47:ℝ)*a3*b2 + (38:ℝ)*a3*b2*b3 + (19:ℝ)*a3*b2^2 + (28:ℝ)*a3*b1 + (20:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (19:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (47:ℝ)*a2*b3 + (19:ℝ)*a2*b3^2 + (38:ℝ)*a2*b2*b3 + (28:ℝ)*a2*b1 + (20:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (38:ℝ)*a2*a3*b3 + (38:ℝ)*a2*a3*b2 + (20:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (19:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (28:ℝ)*d*b3 + (28:ℝ)*d*b2 + (20:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (20:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (20:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3) := by
    unfold dq q; ring
  have hp : 0 < (532:ℝ)*b3 + (532:ℝ)*b2 + (19:ℝ)*b2*b3 + (19:ℝ)*b2*b3^2 + (19:ℝ)*b2^2*b3 + (38:ℝ)*b1*b2*b3 + (47:ℝ)*a3*b2 + (38:ℝ)*a3*b2*b3 + (19:ℝ)*a3*b2^2 + (28:ℝ)*a3*b1 + (20:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (19:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (47:ℝ)*a2*b3 + (19:ℝ)*a2*b3^2 + (38:ℝ)*a2*b2*b3 + (28:ℝ)*a2*b1 + (20:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (38:ℝ)*a2*a3*b3 + (38:ℝ)*a2*a3*b2 + (20:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (19:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (28:ℝ)*d*b3 + (28:ℝ)*d*b2 + (20:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (20:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (20:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 19 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 19 := ⟨a1 - 19, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 19`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 19 ≤ a1 ∨ 19 ≤ a2 ∨ 19 ≤ a3 ∨ 19 ≤ b1 ∨ 19 ≤ b2 ∨ 19 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 19`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 19 → a2 i ≤ 19 → a3 i ≤ 19 → b1 i ≤ 19 → b2 i ≤ 19 → b3 i ≤ 19 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 19 ∧ a2 i ≤ 19 ∧ a3 i ≤ 19 ∧ b1 i ≤ 19 ∧ b2 i ≤ 19 ∧ b3 i ≤ 19
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

end DesignT3Control

namespace DesignT4

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 8*x + 35

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '0', '-35', '24', '0', '0', '-1', '0', '0', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := (-35:ℝ)*u2*u3 + (-35:ℝ)*u1*u3 + (-35:ℝ)*u1*u2 + (24:ℝ)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + (-1:ℝ)*u1^2*u2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3) + g u2 * ((-1:ℝ)*u1*u3) + g u3 * ((-1:ℝ)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-8:ℝ)/105)*u3 + ((1:ℝ)/105)*u3^2 + ((-8:ℝ)/105)*u2 + ((1:ℝ)/105)*u2^2 + ((-8:ℝ)/105)*u1 + ((1:ℝ)/105)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((1:ℝ)/105)) + g u2 * (((1:ℝ)/105)) + g u3 * (((1:ℝ)/105)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 25`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 25) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 25) a2 a3 b1 b2 b3 = -((875:ℝ)*b3 + (875:ℝ)*b2 + (25:ℝ)*b2*b3 + (25:ℝ)*b2*b3^2 + (25:ℝ)*b2^2*b3 + (50:ℝ)*b1*b2*b3 + (60:ℝ)*a3*b2 + (50:ℝ)*a3*b2*b3 + (25:ℝ)*a3*b2^2 + (35:ℝ)*a3*b1 + (26:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (25:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (60:ℝ)*a2*b3 + (25:ℝ)*a2*b3^2 + (50:ℝ)*a2*b2*b3 + (35:ℝ)*a2*b1 + (26:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (50:ℝ)*a2*a3*b3 + (50:ℝ)*a2*a3*b2 + (26:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (25:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (35:ℝ)*d*b3 + (35:ℝ)*d*b2 + (26:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (26:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (26:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3) := by
    unfold dq q; ring
  have hp : 0 < (875:ℝ)*b3 + (875:ℝ)*b2 + (25:ℝ)*b2*b3 + (25:ℝ)*b2*b3^2 + (25:ℝ)*b2^2*b3 + (50:ℝ)*b1*b2*b3 + (60:ℝ)*a3*b2 + (50:ℝ)*a3*b2*b3 + (25:ℝ)*a3*b2^2 + (35:ℝ)*a3*b1 + (26:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (25:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (60:ℝ)*a2*b3 + (25:ℝ)*a2*b3^2 + (50:ℝ)*a2*b2*b3 + (35:ℝ)*a2*b1 + (26:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (50:ℝ)*a2*a3*b3 + (50:ℝ)*a2*a3*b2 + (26:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (25:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (35:ℝ)*d*b3 + (35:ℝ)*d*b2 + (26:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (26:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (26:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 25 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 25 := ⟨a1 - 25, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 25`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 25 ≤ a1 ∨ 25 ≤ a2 ∨ 25 ≤ a3 ∨ 25 ≤ b1 ∨ 25 ≤ b2 ∨ 25 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 25`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 25 → a2 i ≤ 25 → a3 i ≤ 25 → b1 i ≤ 25 → b2 i ≤ 25 → b3 i ≤ 25 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 25 ∧ a2 i ≤ 25 ∧ a3 i ≤ 25 ∧ b1 i ≤ 25 ∧ b2 i ≤ 25 ∧ b3 i ≤ 25
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

end DesignT4

namespace DesignT5

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 10*x + 44

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '0', '-44', '30', '0', '0', '-1', '0', '0', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := (-44:ℝ)*u2*u3 + (-44:ℝ)*u1*u3 + (-44:ℝ)*u1*u2 + (30:ℝ)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + (-1:ℝ)*u1^2*u2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3) + g u2 * ((-1:ℝ)*u1*u3) + g u3 * ((-1:ℝ)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-5:ℝ)/66)*u3 + ((1:ℝ)/132)*u3^2 + ((-5:ℝ)/66)*u2 + ((1:ℝ)/132)*u2^2 + ((-5:ℝ)/66)*u1 + ((1:ℝ)/132)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((1:ℝ)/132)) + g u2 * (((1:ℝ)/132)) + g u3 * (((1:ℝ)/132)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 31`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 31) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 31) a2 a3 b1 b2 b3 = -((1364:ℝ)*b3 + (1364:ℝ)*b2 + (31:ℝ)*b2*b3 + (31:ℝ)*b2*b3^2 + (31:ℝ)*b2^2*b3 + (62:ℝ)*b1*b2*b3 + (75:ℝ)*a3*b2 + (62:ℝ)*a3*b2*b3 + (31:ℝ)*a3*b2^2 + (44:ℝ)*a3*b1 + (32:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (31:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (75:ℝ)*a2*b3 + (31:ℝ)*a2*b3^2 + (62:ℝ)*a2*b2*b3 + (44:ℝ)*a2*b1 + (32:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (62:ℝ)*a2*a3*b3 + (62:ℝ)*a2*a3*b2 + (32:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (31:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (44:ℝ)*d*b3 + (44:ℝ)*d*b2 + (32:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (32:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (32:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3) := by
    unfold dq q; ring
  have hp : 0 < (1364:ℝ)*b3 + (1364:ℝ)*b2 + (31:ℝ)*b2*b3 + (31:ℝ)*b2*b3^2 + (31:ℝ)*b2^2*b3 + (62:ℝ)*b1*b2*b3 + (75:ℝ)*a3*b2 + (62:ℝ)*a3*b2*b3 + (31:ℝ)*a3*b2^2 + (44:ℝ)*a3*b1 + (32:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (31:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (75:ℝ)*a2*b3 + (31:ℝ)*a2*b3^2 + (62:ℝ)*a2*b2*b3 + (44:ℝ)*a2*b1 + (32:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (62:ℝ)*a2*a3*b3 + (62:ℝ)*a2*a3*b2 + (32:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (31:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (44:ℝ)*d*b3 + (44:ℝ)*d*b2 + (32:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (32:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (32:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 31 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 31 := ⟨a1 - 31, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 31`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 31 ≤ a1 ∨ 31 ≤ a2 ∨ 31 ≤ a3 ∨ 31 ≤ b1 ∨ 31 ≤ b2 ∨ 31 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 31`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 31 → a2 i ≤ 31 → a3 i ≤ 31 → b1 i ≤ 31 → b2 i ≤ 31 → b3 i ≤ 31 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 31 ∧ a2 i ≤ 31 ∧ a3 i ≤ 31 ∧ b1 i ≤ 31 ∧ b2 i ≤ 31 ∧ b3 i ≤ 31
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

end DesignT5

namespace DesignT6

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 12*x + 55

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '0', '-55', '36', '0', '0', '-1', '0', '0', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := (-55:ℝ)*u2*u3 + (-55:ℝ)*u1*u3 + (-55:ℝ)*u1*u2 + (36:ℝ)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + (-1:ℝ)*u1^2*u2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3) + g u2 * ((-1:ℝ)*u1*u3) + g u3 * ((-1:ℝ)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-4:ℝ)/55)*u3 + ((1:ℝ)/165)*u3^2 + ((-4:ℝ)/55)*u2 + ((1:ℝ)/165)*u2^2 + ((-4:ℝ)/55)*u1 + ((1:ℝ)/165)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((1:ℝ)/165)) + g u2 * (((1:ℝ)/165)) + g u3 * (((1:ℝ)/165)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 37`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 37) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 37) a2 a3 b1 b2 b3 = -((2035:ℝ)*b3 + (2035:ℝ)*b2 + (37:ℝ)*b2*b3 + (37:ℝ)*b2*b3^2 + (37:ℝ)*b2^2*b3 + (74:ℝ)*b1*b2*b3 + (92:ℝ)*a3*b2 + (74:ℝ)*a3*b2*b3 + (37:ℝ)*a3*b2^2 + (55:ℝ)*a3*b1 + (38:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (37:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (92:ℝ)*a2*b3 + (37:ℝ)*a2*b3^2 + (74:ℝ)*a2*b2*b3 + (55:ℝ)*a2*b1 + (38:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (74:ℝ)*a2*a3*b3 + (74:ℝ)*a2*a3*b2 + (38:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (37:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (55:ℝ)*d*b3 + (55:ℝ)*d*b2 + (38:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (38:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (38:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3) := by
    unfold dq q; ring
  have hp : 0 < (2035:ℝ)*b3 + (2035:ℝ)*b2 + (37:ℝ)*b2*b3 + (37:ℝ)*b2*b3^2 + (37:ℝ)*b2^2*b3 + (74:ℝ)*b1*b2*b3 + (92:ℝ)*a3*b2 + (74:ℝ)*a3*b2*b3 + (37:ℝ)*a3*b2^2 + (55:ℝ)*a3*b1 + (38:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (37:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + (92:ℝ)*a2*b3 + (37:ℝ)*a2*b3^2 + (74:ℝ)*a2*b2*b3 + (55:ℝ)*a2*b1 + (38:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (74:ℝ)*a2*a3*b3 + (74:ℝ)*a2*a3*b2 + (38:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (37:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + (55:ℝ)*d*b3 + (55:ℝ)*d*b2 + (38:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (38:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (38:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 37 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 37 := ⟨a1 - 37, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 37`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 37 ≤ a1 ∨ 37 ≤ a2 ∨ 37 ≤ a3 ∨ 37 ≤ b1 ∨ 37 ≤ b2 ∨ 37 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 37`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 37 → a2 i ≤ 37 → a3 i ≤ 37 → b1 i ≤ 37 → b2 i ≤ 37 → b3 i ≤ 37 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 37 ∧ a2 i ≤ 37 ∧ a3 i ≤ 37 ∧ b1 i ≤ 37 ∧ b2 i ≤ 37 ∧ b3 i ≤ 37
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

end DesignT6

namespace DesignT13Half

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 13*x + (245/4)

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '0', '-245/4', '39', '0', '0', '-1', '0', '0', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((-245:ℝ)/4)*u2*u3 + ((-245:ℝ)/4)*u1*u3 + ((-245:ℝ)/4)*u1*u2 + (39:ℝ)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + (-1:ℝ)*u1^2*u2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3) + g u2 * ((-1:ℝ)*u1*u3) + g u3 * ((-1:ℝ)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-52:ℝ)/735)*u3 + ((4:ℝ)/735)*u3^2 + ((-52:ℝ)/735)*u2 + ((4:ℝ)/735)*u2^2 + ((-52:ℝ)/735)*u1 + ((4:ℝ)/735)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((4:ℝ)/735)) + g u2 * (((4:ℝ)/735)) + g u3 * (((4:ℝ)/735)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 40`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 40) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 40) a2 a3 b1 b2 b3 = -((2450:ℝ)*b3 + (2450:ℝ)*b2 + (40:ℝ)*b2*b3 + (40:ℝ)*b2*b3^2 + (40:ℝ)*b2^2*b3 + (80:ℝ)*b1*b2*b3 + ((405:ℝ)/4)*a3*b2 + (80:ℝ)*a3*b2*b3 + (40:ℝ)*a3*b2^2 + ((245:ℝ)/4)*a3*b1 + (41:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (40:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + ((405:ℝ)/4)*a2*b3 + (40:ℝ)*a2*b3^2 + (80:ℝ)*a2*b2*b3 + ((245:ℝ)/4)*a2*b1 + (41:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (80:ℝ)*a2*a3*b3 + (80:ℝ)*a2*a3*b2 + (41:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (40:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + ((245:ℝ)/4)*d*b3 + ((245:ℝ)/4)*d*b2 + (41:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (41:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (41:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3) := by
    unfold dq q; ring
  have hp : 0 < (2450:ℝ)*b3 + (2450:ℝ)*b2 + (40:ℝ)*b2*b3 + (40:ℝ)*b2*b3^2 + (40:ℝ)*b2^2*b3 + (80:ℝ)*b1*b2*b3 + ((405:ℝ)/4)*a3*b2 + (80:ℝ)*a3*b2*b3 + (40:ℝ)*a3*b2^2 + ((245:ℝ)/4)*a3*b1 + (41:ℝ)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + (1:ℝ)*a3*b1^2*b2 + (40:ℝ)*a3^2*b2 + (1:ℝ)*a3^2*b1*b2 + ((405:ℝ)/4)*a2*b3 + (40:ℝ)*a2*b3^2 + (80:ℝ)*a2*b2*b3 + ((245:ℝ)/4)*a2*b1 + (41:ℝ)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + (2:ℝ)*a2*b1*b2*b3 + (1:ℝ)*a2*b1^2*b3 + (80:ℝ)*a2*a3*b3 + (80:ℝ)*a2*a3*b2 + (41:ℝ)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + (1:ℝ)*a2*a3*b1^2 + (1:ℝ)*a2*a3^2*b1 + (40:ℝ)*a2^2*b3 + (1:ℝ)*a2^2*b1*b3 + (1:ℝ)*a2^2*a3*b1 + ((245:ℝ)/4)*d*b3 + ((245:ℝ)/4)*d*b2 + (41:ℝ)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + (1:ℝ)*d*b2^2*b3 + (2:ℝ)*d*b1*b2*b3 + (41:ℝ)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + (2:ℝ)*d*a3*b1*b2 + (1:ℝ)*d*a3^2*b2 + (41:ℝ)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + (2:ℝ)*d*a2*b2*b3 + (2:ℝ)*d*a2*b1*b3 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + (2:ℝ)*d*a2*a3*b1 + (1:ℝ)*d*a2^2*b3 + (1:ℝ)*d^2*b2*b3 + (1:ℝ)*d^2*a3*b2 + (1:ℝ)*d^2*a2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 40 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 40 := ⟨a1 - 40, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 40`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 40 ≤ a1 ∨ 40 ≤ a2 ∨ 40 ≤ a3 ∨ 40 ≤ b1 ∨ 40 ≤ b2 ∨ 40 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 40`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 40 → a2 i ≤ 40 → a3 i ≤ 40 → b1 i ≤ 40 → b2 i ≤ 40 → b3 i ≤ 40 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 40 ∧ a2 i ≤ 40 ∧ a3 i ≤ 40 ∧ b1 i ≤ 40 ∧ b2 i ≤ 40 ∧ b3 i ≤ 40
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

end DesignT13Half

namespace DesignT7

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 14*x + 68

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '88417/1250', '-121407/1250', '4334547/85000', '0', '0', '-1', '-743/10000', '0', '-2229/680000']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((88417:ℝ)/1250)*u3 + ((88417:ℝ)/1250)*u2 + ((-121407:ℝ)/1250)*u2*u3 + ((-743:ℝ)/10000)*u2^2*u3^2 + ((88417:ℝ)/1250)*u1 + ((-121407:ℝ)/1250)*u1*u3 + ((-121407:ℝ)/1250)*u1*u2 + ((4334547:ℝ)/85000)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + ((-743:ℝ)/10000)*u1^2*u3^2 + (-1:ℝ)*u1^2*u2*u3 + ((-743:ℝ)/10000)*u1^2*u2^2 + ((-2229:ℝ)/680000)*u1^2*u2^2*u3^2

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * (((-743:ℝ)/10000)*u3^2 + (-1:ℝ)*u2*u3 + ((-743:ℝ)/10000)*u2^2 + ((-2229:ℝ)/680000)*u2^2*u3^2) + g u2 * (((12631:ℝ)/2500) + ((743:ℝ)/5000)*u3^2 + ((-5201:ℝ)/5000)*u1 + (-1:ℝ)*u1*u3 + ((-15603:ℝ)/340000)*u1*u3^2) + g u3 * (((-12631:ℝ)/2500) + ((5201:ℝ)/2500)*u2 + ((5201:ℝ)/2500)*u1 + ((-279221:ℝ)/170000)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-7:ℝ)/102)*u3 + ((1:ℝ)/204)*u3^2 + ((-7:ℝ)/102)*u2 + ((1:ℝ)/204)*u2^2 + ((-7:ℝ)/102)*u1 + ((1:ℝ)/204)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((1:ℝ)/204)) + g u2 * (((1:ℝ)/204)) + g u3 * (((1:ℝ)/204)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 52`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 52) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 52) a2 a3 b1 b2 b3 = -(((3156582:ℝ)/625)*b3 + ((125567:ℝ)/625)*b3^2 + ((3156582:ℝ)/625)*b2 + ((1110889:ℝ)/21250)*b2*b3 + (52:ℝ)*b2*b3^2 + ((125567:ℝ)/625)*b2^2 + (52:ℝ)*b2^2*b3 + ((376701:ℝ)/42500)*b2^2*b3^2 + ((9659:ℝ)/1250)*b1*b3^2 + (104:ℝ)*b1*b2*b3 + ((9659:ℝ)/1250)*b1*b2^2 + ((28977:ℝ)/85000)*b1*b2^2*b3^2 + ((251134:ℝ)/625)*a3*b3 + ((1587404:ℝ)/10625)*a3*b2 + (104:ℝ)*a3*b2*b3 + (52:ℝ)*a3*b2^2 + ((303887:ℝ)/17000)*a3*b2^2*b3 + ((121407:ℝ)/1250)*a3*b1 + ((9659:ℝ)/625)*a3*b1*b3 + ((4505453:ℝ)/85000)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + ((28977:ℝ)/42500)*a3*b1*b2^2*b3 + ((743:ℝ)/5000)*a3*b1^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((2229:ℝ)/340000)*a3*b1^2*b2^2*b3 + (52:ℝ)*a3^2*b2 + ((303887:ℝ)/34000)*a3^2*b2^2 + ((9659:ℝ)/1250)*a3^2*b1 + (1:ℝ)*a3^2*b1*b2 + ((28977:ℝ)/85000)*a3^2*b1*b2^2 + ((743:ℝ)/10000)*a3^2*b1^2 + ((2229:ℝ)/680000)*a3^2*b1^2*b2^2 + ((1587404:ℝ)/10625)*a2*b3 + (52:ℝ)*a2*b3^2 + ((251134:ℝ)/625)*a2*b2 + (104:ℝ)*a2*b2*b3 + ((303887:ℝ)/17000)*a2*b2*b3^2 + ((121407:ℝ)/1250)*a2*b1 + ((4505453:ℝ)/85000)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + ((9659:ℝ)/625)*a2*b1*b2 + (2:ℝ)*a2*b1*b2*b3 + ((28977:ℝ)/42500)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((743:ℝ)/5000)*a2*b1^2*b2 + ((2229:ℝ)/340000)*a2*b1^2*b2*b3^2 + (104:ℝ)*a2*a3*b3 + (104:ℝ)*a2*a3*b2 + ((303887:ℝ)/8500)*a2*a3*b2*b3 + ((4505453:ℝ)/85000)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + ((28977:ℝ)/21250)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((2229:ℝ)/170000)*a2*a3*b1^2*b2*b3 + ((303887:ℝ)/17000)*a2*a3^2*b2 + (1:ℝ)*a2*a3^2*b1 + ((28977:ℝ)/42500)*a2*a3^2*b1*b2 + ((2229:ℝ)/340000)*a2*a3^2*b1^2*b2 + (52:ℝ)*a2^2*b3 + ((303887:ℝ)/34000)*a2^2*b3^2 + ((9659:ℝ)/1250)*a2^2*b1 + (1:ℝ)*a2^2*b1*b3 + ((28977:ℝ)/85000)*a2^2*b1*b3^2 + ((743:ℝ)/10000)*a2^2*b1^2 + ((2229:ℝ)/680000)*a2^2*b1^2*b3^2 + ((303887:ℝ)/17000)*a2^2*a3*b3 + (1:ℝ)*a2^2*a3*b1 + ((28977:ℝ)/42500)*a2^2*a3*b1*b3 + ((2229:ℝ)/340000)*a2^2*a3*b1^2*b3 + ((28977:ℝ)/85000)*a2^2*a3^2*b1 + ((2229:ℝ)/680000)*a2^2*a3^2*b1^2 + ((121407:ℝ)/1250)*d*b3 + ((9659:ℝ)/1250)*d*b3^2 + ((121407:ℝ)/1250)*d*b2 + ((4505453:ℝ)/85000)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + ((9659:ℝ)/1250)*d*b2^2 + (1:ℝ)*d*b2^2*b3 + ((28977:ℝ)/85000)*d*b2^2*b3^2 + ((743:ℝ)/5000)*d*b1*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((743:ℝ)/5000)*d*b1*b2^2 + ((2229:ℝ)/340000)*d*b1*b2^2*b3^2 + ((9659:ℝ)/625)*d*a3*b3 + ((4505453:ℝ)/85000)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + ((28977:ℝ)/42500)*d*a3*b2^2*b3 + ((743:ℝ)/2500)*d*a3*b1*b3 + (2:ℝ)*d*a3*b1*b2 + ((2229:ℝ)/170000)*d*a3*b1*b2^2*b3 + (1:ℝ)*d*a3^2*b2 + ((28977:ℝ)/85000)*d*a3^2*b2^2 + ((743:ℝ)/5000)*d*a3^2*b1 + ((2229:ℝ)/340000)*d*a3^2*b1*b2^2 + ((4505453:ℝ)/85000)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + ((9659:ℝ)/625)*d*a2*b2 + (2:ℝ)*d*a2*b2*b3 + ((28977:ℝ)/42500)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((743:ℝ)/2500)*d*a2*b1*b2 + ((2229:ℝ)/170000)*d*a2*b1*b2*b3^2 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + ((28977:ℝ)/21250)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((2229:ℝ)/85000)*d*a2*a3*b1*b2*b3 + ((28977:ℝ)/42500)*d*a2*a3^2*b2 + ((2229:ℝ)/170000)*d*a2*a3^2*b1*b2 + (1:ℝ)*d*a2^2*b3 + ((28977:ℝ)/85000)*d*a2^2*b3^2 + ((743:ℝ)/5000)*d*a2^2*b1 + ((2229:ℝ)/340000)*d*a2^2*b1*b3^2 + ((28977:ℝ)/42500)*d*a2^2*a3*b3 + ((2229:ℝ)/170000)*d*a2^2*a3*b1*b3 + ((2229:ℝ)/340000)*d*a2^2*a3^2*b1 + ((743:ℝ)/10000)*d^2*b3^2 + (1:ℝ)*d^2*b2*b3 + ((743:ℝ)/10000)*d^2*b2^2 + ((2229:ℝ)/680000)*d^2*b2^2*b3^2 + ((743:ℝ)/5000)*d^2*a3*b3 + (1:ℝ)*d^2*a3*b2 + ((2229:ℝ)/340000)*d^2*a3*b2^2*b3 + ((2229:ℝ)/680000)*d^2*a3^2*b2^2 + (1:ℝ)*d^2*a2*b3 + ((743:ℝ)/5000)*d^2*a2*b2 + ((2229:ℝ)/340000)*d^2*a2*b2*b3^2 + ((2229:ℝ)/170000)*d^2*a2*a3*b2*b3 + ((2229:ℝ)/340000)*d^2*a2*a3^2*b2 + ((2229:ℝ)/680000)*d^2*a2^2*b3^2 + ((2229:ℝ)/340000)*d^2*a2^2*a3*b3) := by
    unfold dq q; ring
  have hp : 0 < ((3156582:ℝ)/625)*b3 + ((125567:ℝ)/625)*b3^2 + ((3156582:ℝ)/625)*b2 + ((1110889:ℝ)/21250)*b2*b3 + (52:ℝ)*b2*b3^2 + ((125567:ℝ)/625)*b2^2 + (52:ℝ)*b2^2*b3 + ((376701:ℝ)/42500)*b2^2*b3^2 + ((9659:ℝ)/1250)*b1*b3^2 + (104:ℝ)*b1*b2*b3 + ((9659:ℝ)/1250)*b1*b2^2 + ((28977:ℝ)/85000)*b1*b2^2*b3^2 + ((251134:ℝ)/625)*a3*b3 + ((1587404:ℝ)/10625)*a3*b2 + (104:ℝ)*a3*b2*b3 + (52:ℝ)*a3*b2^2 + ((303887:ℝ)/17000)*a3*b2^2*b3 + ((121407:ℝ)/1250)*a3*b1 + ((9659:ℝ)/625)*a3*b1*b3 + ((4505453:ℝ)/85000)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + ((28977:ℝ)/42500)*a3*b1*b2^2*b3 + ((743:ℝ)/5000)*a3*b1^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((2229:ℝ)/340000)*a3*b1^2*b2^2*b3 + (52:ℝ)*a3^2*b2 + ((303887:ℝ)/34000)*a3^2*b2^2 + ((9659:ℝ)/1250)*a3^2*b1 + (1:ℝ)*a3^2*b1*b2 + ((28977:ℝ)/85000)*a3^2*b1*b2^2 + ((743:ℝ)/10000)*a3^2*b1^2 + ((2229:ℝ)/680000)*a3^2*b1^2*b2^2 + ((1587404:ℝ)/10625)*a2*b3 + (52:ℝ)*a2*b3^2 + ((251134:ℝ)/625)*a2*b2 + (104:ℝ)*a2*b2*b3 + ((303887:ℝ)/17000)*a2*b2*b3^2 + ((121407:ℝ)/1250)*a2*b1 + ((4505453:ℝ)/85000)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + ((9659:ℝ)/625)*a2*b1*b2 + (2:ℝ)*a2*b1*b2*b3 + ((28977:ℝ)/42500)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((743:ℝ)/5000)*a2*b1^2*b2 + ((2229:ℝ)/340000)*a2*b1^2*b2*b3^2 + (104:ℝ)*a2*a3*b3 + (104:ℝ)*a2*a3*b2 + ((303887:ℝ)/8500)*a2*a3*b2*b3 + ((4505453:ℝ)/85000)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + ((28977:ℝ)/21250)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((2229:ℝ)/170000)*a2*a3*b1^2*b2*b3 + ((303887:ℝ)/17000)*a2*a3^2*b2 + (1:ℝ)*a2*a3^2*b1 + ((28977:ℝ)/42500)*a2*a3^2*b1*b2 + ((2229:ℝ)/340000)*a2*a3^2*b1^2*b2 + (52:ℝ)*a2^2*b3 + ((303887:ℝ)/34000)*a2^2*b3^2 + ((9659:ℝ)/1250)*a2^2*b1 + (1:ℝ)*a2^2*b1*b3 + ((28977:ℝ)/85000)*a2^2*b1*b3^2 + ((743:ℝ)/10000)*a2^2*b1^2 + ((2229:ℝ)/680000)*a2^2*b1^2*b3^2 + ((303887:ℝ)/17000)*a2^2*a3*b3 + (1:ℝ)*a2^2*a3*b1 + ((28977:ℝ)/42500)*a2^2*a3*b1*b3 + ((2229:ℝ)/340000)*a2^2*a3*b1^2*b3 + ((28977:ℝ)/85000)*a2^2*a3^2*b1 + ((2229:ℝ)/680000)*a2^2*a3^2*b1^2 + ((121407:ℝ)/1250)*d*b3 + ((9659:ℝ)/1250)*d*b3^2 + ((121407:ℝ)/1250)*d*b2 + ((4505453:ℝ)/85000)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + ((9659:ℝ)/1250)*d*b2^2 + (1:ℝ)*d*b2^2*b3 + ((28977:ℝ)/85000)*d*b2^2*b3^2 + ((743:ℝ)/5000)*d*b1*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((743:ℝ)/5000)*d*b1*b2^2 + ((2229:ℝ)/340000)*d*b1*b2^2*b3^2 + ((9659:ℝ)/625)*d*a3*b3 + ((4505453:ℝ)/85000)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + ((28977:ℝ)/42500)*d*a3*b2^2*b3 + ((743:ℝ)/2500)*d*a3*b1*b3 + (2:ℝ)*d*a3*b1*b2 + ((2229:ℝ)/170000)*d*a3*b1*b2^2*b3 + (1:ℝ)*d*a3^2*b2 + ((28977:ℝ)/85000)*d*a3^2*b2^2 + ((743:ℝ)/5000)*d*a3^2*b1 + ((2229:ℝ)/340000)*d*a3^2*b1*b2^2 + ((4505453:ℝ)/85000)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + ((9659:ℝ)/625)*d*a2*b2 + (2:ℝ)*d*a2*b2*b3 + ((28977:ℝ)/42500)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((743:ℝ)/2500)*d*a2*b1*b2 + ((2229:ℝ)/170000)*d*a2*b1*b2*b3^2 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + ((28977:ℝ)/21250)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((2229:ℝ)/85000)*d*a2*a3*b1*b2*b3 + ((28977:ℝ)/42500)*d*a2*a3^2*b2 + ((2229:ℝ)/170000)*d*a2*a3^2*b1*b2 + (1:ℝ)*d*a2^2*b3 + ((28977:ℝ)/85000)*d*a2^2*b3^2 + ((743:ℝ)/5000)*d*a2^2*b1 + ((2229:ℝ)/340000)*d*a2^2*b1*b3^2 + ((28977:ℝ)/42500)*d*a2^2*a3*b3 + ((2229:ℝ)/170000)*d*a2^2*a3*b1*b3 + ((2229:ℝ)/340000)*d*a2^2*a3^2*b1 + ((743:ℝ)/10000)*d^2*b3^2 + (1:ℝ)*d^2*b2*b3 + ((743:ℝ)/10000)*d^2*b2^2 + ((2229:ℝ)/680000)*d^2*b2^2*b3^2 + ((743:ℝ)/5000)*d^2*a3*b3 + (1:ℝ)*d^2*a3*b2 + ((2229:ℝ)/340000)*d^2*a3*b2^2*b3 + ((2229:ℝ)/680000)*d^2*a3^2*b2^2 + (1:ℝ)*d^2*a2*b3 + ((743:ℝ)/5000)*d^2*a2*b2 + ((2229:ℝ)/340000)*d^2*a2*b2*b3^2 + ((2229:ℝ)/170000)*d^2*a2*a3*b2*b3 + ((2229:ℝ)/340000)*d^2*a2*a3^2*b2 + ((2229:ℝ)/680000)*d^2*a2^2*b3^2 + ((2229:ℝ)/340000)*d^2*a2^2*a3*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 52 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 52 := ⟨a1 - 52, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 52`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 52 ≤ a1 ∨ 52 ≤ a2 ∨ 52 ≤ a3 ∨ 52 ≤ b1 ∨ 52 ≤ b2 ∨ 52 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 52`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 52 → a2 i ≤ 52 → a3 i ≤ 52 → b1 i ≤ 52 → b2 i ≤ 52 → b3 i ≤ 52 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 52 ∧ a2 i ≤ 52 ∧ a3 i ≤ 52 ∧ b1 i ≤ 52 ∧ b2 i ≤ 52 ∧ b3 i ≤ 52
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

end DesignT7

namespace DesignT15Half

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - 15*x + (301/4)

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '1362627/8000', '-28631/200', '393129/6020', '0', '0', '-1', '-1509/10000', '0', '-4527/752500']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((1362627:ℝ)/8000)*u3 + ((1362627:ℝ)/8000)*u2 + ((-28631:ℝ)/200)*u2*u3 + ((-1509:ℝ)/10000)*u2^2*u3^2 + ((1362627:ℝ)/8000)*u1 + ((-28631:ℝ)/200)*u1*u3 + ((-28631:ℝ)/200)*u1*u2 + ((393129:ℝ)/6020)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + ((-1509:ℝ)/10000)*u1^2*u3^2 + (-1:ℝ)*u1^2*u2*u3 + ((-1509:ℝ)/10000)*u1^2*u2^2 + ((-4527:ℝ)/752500)*u1^2*u2^2*u3^2

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * (((-1509:ℝ)/10000)*u3^2 + (-1:ℝ)*u2*u3 + ((-1509:ℝ)/10000)*u2^2 + ((-4527:ℝ)/752500)*u2^2*u3^2) + g u2 * (((454209:ℝ)/40000) + ((1509:ℝ)/5000)*u3^2 + ((-4527:ℝ)/2000)*u1 + (-1:ℝ)*u1*u3 + ((-13581:ℝ)/150500)*u1*u3^2) + g u3 * (((-454209:ℝ)/40000) + ((4527:ℝ)/1000)*u2 + ((4527:ℝ)/1000)*u1 + ((-70843:ℝ)/30100)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-20:ℝ)/301)*u3 + ((4:ℝ)/903)*u3^2 + ((-20:ℝ)/301)*u2 + ((4:ℝ)/903)*u2^2 + ((-20:ℝ)/301)*u1 + ((4:ℝ)/903)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((4:ℝ)/903)) + g u2 * (((4:ℝ)/903)) + g u3 * (((4:ℝ)/903)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 66`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 66) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 66) a2 a3 b1 b2 b3 = -(((944823:ℝ)/100)*b3 + ((1643301:ℝ)/2500)*b3^2 + ((944823:ℝ)/100)*b2 + ((138303:ℝ)/3010)*b2*b3 + (66:ℝ)*b2*b3^2 + ((1643301:ℝ)/2500)*b2^2 + (66:ℝ)*b2^2*b3 + ((4929903:ℝ)/188125)*b2^2*b3^2 + ((49797:ℝ)/2500)*b1*b3^2 + (132:ℝ)*b1*b2*b3 + ((49797:ℝ)/2500)*b1*b2^2 + ((149391:ℝ)/188125)*b1*b2^2*b3^2 + ((1643301:ℝ)/1250)*a3*b3 + ((11383991:ℝ)/60200)*a3*b2 + (132:ℝ)*a3*b2*b3 + (66:ℝ)*a3*b2^2 + ((79332657:ℝ)/1505000)*a3*b2^2*b3 + ((28631:ℝ)/200)*a3*b1 + ((49797:ℝ)/1250)*a3*b1*b3 + ((401511:ℝ)/6020)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + ((298782:ℝ)/188125)*a3*b1*b2^2*b3 + ((1509:ℝ)/5000)*a3*b1^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((4527:ℝ)/376250)*a3*b1^2*b2^2*b3 + (66:ℝ)*a3^2*b2 + ((79332657:ℝ)/3010000)*a3^2*b2^2 + ((49797:ℝ)/2500)*a3^2*b1 + (1:ℝ)*a3^2*b1*b2 + ((149391:ℝ)/188125)*a3^2*b1*b2^2 + ((1509:ℝ)/10000)*a3^2*b1^2 + ((4527:ℝ)/752500)*a3^2*b1^2*b2^2 + ((11383991:ℝ)/60200)*a2*b3 + (66:ℝ)*a2*b3^2 + ((1643301:ℝ)/1250)*a2*b2 + (132:ℝ)*a2*b2*b3 + ((79332657:ℝ)/1505000)*a2*b2*b3^2 + ((28631:ℝ)/200)*a2*b1 + ((401511:ℝ)/6020)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + ((49797:ℝ)/1250)*a2*b1*b2 + (2:ℝ)*a2*b1*b2*b3 + ((298782:ℝ)/188125)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((1509:ℝ)/5000)*a2*b1^2*b2 + ((4527:ℝ)/376250)*a2*b1^2*b2*b3^2 + (132:ℝ)*a2*a3*b3 + (132:ℝ)*a2*a3*b2 + ((79332657:ℝ)/752500)*a2*a3*b2*b3 + ((401511:ℝ)/6020)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + ((597564:ℝ)/188125)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((4527:ℝ)/188125)*a2*a3*b1^2*b2*b3 + ((79332657:ℝ)/1505000)*a2*a3^2*b2 + (1:ℝ)*a2*a3^2*b1 + ((298782:ℝ)/188125)*a2*a3^2*b1*b2 + ((4527:ℝ)/376250)*a2*a3^2*b1^2*b2 + (66:ℝ)*a2^2*b3 + ((79332657:ℝ)/3010000)*a2^2*b3^2 + ((49797:ℝ)/2500)*a2^2*b1 + (1:ℝ)*a2^2*b1*b3 + ((149391:ℝ)/188125)*a2^2*b1*b3^2 + ((1509:ℝ)/10000)*a2^2*b1^2 + ((4527:ℝ)/752500)*a2^2*b1^2*b3^2 + ((79332657:ℝ)/1505000)*a2^2*a3*b3 + (1:ℝ)*a2^2*a3*b1 + ((298782:ℝ)/188125)*a2^2*a3*b1*b3 + ((4527:ℝ)/376250)*a2^2*a3*b1^2*b3 + ((149391:ℝ)/188125)*a2^2*a3^2*b1 + ((4527:ℝ)/752500)*a2^2*a3^2*b1^2 + ((28631:ℝ)/200)*d*b3 + ((49797:ℝ)/2500)*d*b3^2 + ((28631:ℝ)/200)*d*b2 + ((401511:ℝ)/6020)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + ((49797:ℝ)/2500)*d*b2^2 + (1:ℝ)*d*b2^2*b3 + ((149391:ℝ)/188125)*d*b2^2*b3^2 + ((1509:ℝ)/5000)*d*b1*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((1509:ℝ)/5000)*d*b1*b2^2 + ((4527:ℝ)/376250)*d*b1*b2^2*b3^2 + ((49797:ℝ)/1250)*d*a3*b3 + ((401511:ℝ)/6020)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + ((298782:ℝ)/188125)*d*a3*b2^2*b3 + ((1509:ℝ)/2500)*d*a3*b1*b3 + (2:ℝ)*d*a3*b1*b2 + ((4527:ℝ)/188125)*d*a3*b1*b2^2*b3 + (1:ℝ)*d*a3^2*b2 + ((149391:ℝ)/188125)*d*a3^2*b2^2 + ((1509:ℝ)/5000)*d*a3^2*b1 + ((4527:ℝ)/376250)*d*a3^2*b1*b2^2 + ((401511:ℝ)/6020)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + ((49797:ℝ)/1250)*d*a2*b2 + (2:ℝ)*d*a2*b2*b3 + ((298782:ℝ)/188125)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((1509:ℝ)/2500)*d*a2*b1*b2 + ((4527:ℝ)/188125)*d*a2*b1*b2*b3^2 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + ((597564:ℝ)/188125)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((9054:ℝ)/188125)*d*a2*a3*b1*b2*b3 + ((298782:ℝ)/188125)*d*a2*a3^2*b2 + ((4527:ℝ)/188125)*d*a2*a3^2*b1*b2 + (1:ℝ)*d*a2^2*b3 + ((149391:ℝ)/188125)*d*a2^2*b3^2 + ((1509:ℝ)/5000)*d*a2^2*b1 + ((4527:ℝ)/376250)*d*a2^2*b1*b3^2 + ((298782:ℝ)/188125)*d*a2^2*a3*b3 + ((4527:ℝ)/188125)*d*a2^2*a3*b1*b3 + ((4527:ℝ)/376250)*d*a2^2*a3^2*b1 + ((1509:ℝ)/10000)*d^2*b3^2 + (1:ℝ)*d^2*b2*b3 + ((1509:ℝ)/10000)*d^2*b2^2 + ((4527:ℝ)/752500)*d^2*b2^2*b3^2 + ((1509:ℝ)/5000)*d^2*a3*b3 + (1:ℝ)*d^2*a3*b2 + ((4527:ℝ)/376250)*d^2*a3*b2^2*b3 + ((4527:ℝ)/752500)*d^2*a3^2*b2^2 + (1:ℝ)*d^2*a2*b3 + ((1509:ℝ)/5000)*d^2*a2*b2 + ((4527:ℝ)/376250)*d^2*a2*b2*b3^2 + ((4527:ℝ)/188125)*d^2*a2*a3*b2*b3 + ((4527:ℝ)/376250)*d^2*a2*a3^2*b2 + ((4527:ℝ)/752500)*d^2*a2^2*b3^2 + ((4527:ℝ)/376250)*d^2*a2^2*a3*b3) := by
    unfold dq q; ring
  have hp : 0 < ((944823:ℝ)/100)*b3 + ((1643301:ℝ)/2500)*b3^2 + ((944823:ℝ)/100)*b2 + ((138303:ℝ)/3010)*b2*b3 + (66:ℝ)*b2*b3^2 + ((1643301:ℝ)/2500)*b2^2 + (66:ℝ)*b2^2*b3 + ((4929903:ℝ)/188125)*b2^2*b3^2 + ((49797:ℝ)/2500)*b1*b3^2 + (132:ℝ)*b1*b2*b3 + ((49797:ℝ)/2500)*b1*b2^2 + ((149391:ℝ)/188125)*b1*b2^2*b3^2 + ((1643301:ℝ)/1250)*a3*b3 + ((11383991:ℝ)/60200)*a3*b2 + (132:ℝ)*a3*b2*b3 + (66:ℝ)*a3*b2^2 + ((79332657:ℝ)/1505000)*a3*b2^2*b3 + ((28631:ℝ)/200)*a3*b1 + ((49797:ℝ)/1250)*a3*b1*b3 + ((401511:ℝ)/6020)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + ((298782:ℝ)/188125)*a3*b1*b2^2*b3 + ((1509:ℝ)/5000)*a3*b1^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((4527:ℝ)/376250)*a3*b1^2*b2^2*b3 + (66:ℝ)*a3^2*b2 + ((79332657:ℝ)/3010000)*a3^2*b2^2 + ((49797:ℝ)/2500)*a3^2*b1 + (1:ℝ)*a3^2*b1*b2 + ((149391:ℝ)/188125)*a3^2*b1*b2^2 + ((1509:ℝ)/10000)*a3^2*b1^2 + ((4527:ℝ)/752500)*a3^2*b1^2*b2^2 + ((11383991:ℝ)/60200)*a2*b3 + (66:ℝ)*a2*b3^2 + ((1643301:ℝ)/1250)*a2*b2 + (132:ℝ)*a2*b2*b3 + ((79332657:ℝ)/1505000)*a2*b2*b3^2 + ((28631:ℝ)/200)*a2*b1 + ((401511:ℝ)/6020)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + ((49797:ℝ)/1250)*a2*b1*b2 + (2:ℝ)*a2*b1*b2*b3 + ((298782:ℝ)/188125)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((1509:ℝ)/5000)*a2*b1^2*b2 + ((4527:ℝ)/376250)*a2*b1^2*b2*b3^2 + (132:ℝ)*a2*a3*b3 + (132:ℝ)*a2*a3*b2 + ((79332657:ℝ)/752500)*a2*a3*b2*b3 + ((401511:ℝ)/6020)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + ((597564:ℝ)/188125)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((4527:ℝ)/188125)*a2*a3*b1^2*b2*b3 + ((79332657:ℝ)/1505000)*a2*a3^2*b2 + (1:ℝ)*a2*a3^2*b1 + ((298782:ℝ)/188125)*a2*a3^2*b1*b2 + ((4527:ℝ)/376250)*a2*a3^2*b1^2*b2 + (66:ℝ)*a2^2*b3 + ((79332657:ℝ)/3010000)*a2^2*b3^2 + ((49797:ℝ)/2500)*a2^2*b1 + (1:ℝ)*a2^2*b1*b3 + ((149391:ℝ)/188125)*a2^2*b1*b3^2 + ((1509:ℝ)/10000)*a2^2*b1^2 + ((4527:ℝ)/752500)*a2^2*b1^2*b3^2 + ((79332657:ℝ)/1505000)*a2^2*a3*b3 + (1:ℝ)*a2^2*a3*b1 + ((298782:ℝ)/188125)*a2^2*a3*b1*b3 + ((4527:ℝ)/376250)*a2^2*a3*b1^2*b3 + ((149391:ℝ)/188125)*a2^2*a3^2*b1 + ((4527:ℝ)/752500)*a2^2*a3^2*b1^2 + ((28631:ℝ)/200)*d*b3 + ((49797:ℝ)/2500)*d*b3^2 + ((28631:ℝ)/200)*d*b2 + ((401511:ℝ)/6020)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + ((49797:ℝ)/2500)*d*b2^2 + (1:ℝ)*d*b2^2*b3 + ((149391:ℝ)/188125)*d*b2^2*b3^2 + ((1509:ℝ)/5000)*d*b1*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((1509:ℝ)/5000)*d*b1*b2^2 + ((4527:ℝ)/376250)*d*b1*b2^2*b3^2 + ((49797:ℝ)/1250)*d*a3*b3 + ((401511:ℝ)/6020)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + ((298782:ℝ)/188125)*d*a3*b2^2*b3 + ((1509:ℝ)/2500)*d*a3*b1*b3 + (2:ℝ)*d*a3*b1*b2 + ((4527:ℝ)/188125)*d*a3*b1*b2^2*b3 + (1:ℝ)*d*a3^2*b2 + ((149391:ℝ)/188125)*d*a3^2*b2^2 + ((1509:ℝ)/5000)*d*a3^2*b1 + ((4527:ℝ)/376250)*d*a3^2*b1*b2^2 + ((401511:ℝ)/6020)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + ((49797:ℝ)/1250)*d*a2*b2 + (2:ℝ)*d*a2*b2*b3 + ((298782:ℝ)/188125)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((1509:ℝ)/2500)*d*a2*b1*b2 + ((4527:ℝ)/188125)*d*a2*b1*b2*b3^2 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + ((597564:ℝ)/188125)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((9054:ℝ)/188125)*d*a2*a3*b1*b2*b3 + ((298782:ℝ)/188125)*d*a2*a3^2*b2 + ((4527:ℝ)/188125)*d*a2*a3^2*b1*b2 + (1:ℝ)*d*a2^2*b3 + ((149391:ℝ)/188125)*d*a2^2*b3^2 + ((1509:ℝ)/5000)*d*a2^2*b1 + ((4527:ℝ)/376250)*d*a2^2*b1*b3^2 + ((298782:ℝ)/188125)*d*a2^2*a3*b3 + ((4527:ℝ)/188125)*d*a2^2*a3*b1*b3 + ((4527:ℝ)/376250)*d*a2^2*a3^2*b1 + ((1509:ℝ)/10000)*d^2*b3^2 + (1:ℝ)*d^2*b2*b3 + ((1509:ℝ)/10000)*d^2*b2^2 + ((4527:ℝ)/752500)*d^2*b2^2*b3^2 + ((1509:ℝ)/5000)*d^2*a3*b3 + (1:ℝ)*d^2*a3*b2 + ((4527:ℝ)/376250)*d^2*a3*b2^2*b3 + ((4527:ℝ)/752500)*d^2*a3^2*b2^2 + (1:ℝ)*d^2*a2*b3 + ((1509:ℝ)/5000)*d^2*a2*b2 + ((4527:ℝ)/376250)*d^2*a2*b2*b3^2 + ((4527:ℝ)/188125)*d^2*a2*a3*b2*b3 + ((4527:ℝ)/376250)*d^2*a2*a3^2*b2 + ((4527:ℝ)/752500)*d^2*a2^2*b3^2 + ((4527:ℝ)/376250)*d^2*a2^2*a3*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 66 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 66 := ⟨a1 - 66, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 66`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 66 ≤ a1 ∨ 66 ≤ a2 ∨ 66 ≤ a3 ∨ 66 ≤ b1 ∨ 66 ≤ b2 ∨ 66 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 66`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 66 → a2 i ≤ 66 → a3 i ≤ 66 → b1 i ≤ 66 → b2 i ≤ 66 → b3 i ≤ 66 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 66 ∧ a2 i ≤ 66 ∧ a3 i ≤ 66 ∧ b1 i ≤ 66 ∧ b2 i ≤ 66 ∧ b3 i ≤ 66
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

end DesignT15Half

namespace DesignT31Quarter

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - (31/2)*x + (1265/16)

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '7160659/32000', '-834009/5000', '20786709/287500', '0', '0', '-1', '-913/5000', '0', '-498/71875']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((7160659:ℝ)/32000)*u3 + ((7160659:ℝ)/32000)*u2 + ((-834009:ℝ)/5000)*u2*u3 + ((-913:ℝ)/5000)*u2^2*u3^2 + ((7160659:ℝ)/32000)*u1 + ((-834009:ℝ)/5000)*u1*u3 + ((-834009:ℝ)/5000)*u1*u2 + ((20786709:ℝ)/287500)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + ((-913:ℝ)/5000)*u1^2*u3^2 + (-1:ℝ)*u1^2*u2*u3 + ((-913:ℝ)/5000)*u1^2*u2^2 + ((-498:ℝ)/71875)*u1^2*u2^2*u3^2

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * (((-913:ℝ)/5000)*u3^2 + (-1:ℝ)*u2*u3 + ((-913:ℝ)/5000)*u2^2 + ((-498:ℝ)/71875)*u2^2*u3^2) + g u2 * (((230989:ℝ)/16000) + ((913:ℝ)/2500)*u3^2 + ((-28303:ℝ)/10000)*u1 + (-1:ℝ)*u1*u3 + ((-7719:ℝ)/71875)*u1*u3^2) + g u3 * (((-230989:ℝ)/16000) + ((28303:ℝ)/5000)*u2 + ((28303:ℝ)/5000)*u1 + ((-383039:ℝ)/143750)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-248:ℝ)/3795)*u3 + ((16:ℝ)/3795)*u3^2 + ((-248:ℝ)/3795)*u2 + ((16:ℝ)/3795)*u2^2 + ((-248:ℝ)/3795)*u1 + ((16:ℝ)/3795)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((16:ℝ)/3795)) + g u2 * (((16:ℝ)/3795)) + g u3 * (((16:ℝ)/3795)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 73`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 73) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 73) a2 a3 b1 b2 b3 = -(((60882657:ℝ)/5000)*b3 + ((4865377:ℝ)/5000)*b3^2 + ((60882657:ℝ)/5000)*b2 + ((14657743:ℝ)/287500)*b2*b3 + (73:ℝ)*b2*b3^2 + ((4865377:ℝ)/5000)*b2^2 + (73:ℝ)*b2^2*b3 + ((2653842:ℝ)/71875)*b2^2*b3^2 + ((66649:ℝ)/2500)*b1*b3^2 + (146:ℝ)*b1*b2*b3 + ((66649:ℝ)/2500)*b1*b2^2 + ((72708:ℝ)/71875)*b1*b2^2*b3^2 + ((4865377:ℝ)/2500)*a3*b3 + ((125226521:ℝ)/575000)*a3*b2 + (146:ℝ)*a3*b2*b3 + (73:ℝ)*a3*b2^2 + ((21335731:ℝ)/287500)*a3*b2^2*b3 + ((834009:ℝ)/5000)*a3*b1 + ((66649:ℝ)/1250)*a3*b1*b3 + ((21188291:ℝ)/287500)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + ((145416:ℝ)/71875)*a3*b1*b2^2*b3 + ((913:ℝ)/2500)*a3*b1^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((996:ℝ)/71875)*a3*b1^2*b2^2*b3 + (73:ℝ)*a3^2*b2 + ((21335731:ℝ)/575000)*a3^2*b2^2 + ((66649:ℝ)/2500)*a3^2*b1 + (1:ℝ)*a3^2*b1*b2 + ((72708:ℝ)/71875)*a3^2*b1*b2^2 + ((913:ℝ)/5000)*a3^2*b1^2 + ((498:ℝ)/71875)*a3^2*b1^2*b2^2 + ((125226521:ℝ)/575000)*a2*b3 + (73:ℝ)*a2*b3^2 + ((4865377:ℝ)/2500)*a2*b2 + (146:ℝ)*a2*b2*b3 + ((21335731:ℝ)/287500)*a2*b2*b3^2 + ((834009:ℝ)/5000)*a2*b1 + ((21188291:ℝ)/287500)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + ((66649:ℝ)/1250)*a2*b1*b2 + (2:ℝ)*a2*b1*b2*b3 + ((145416:ℝ)/71875)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((913:ℝ)/2500)*a2*b1^2*b2 + ((996:ℝ)/71875)*a2*b1^2*b2*b3^2 + (146:ℝ)*a2*a3*b3 + (146:ℝ)*a2*a3*b2 + ((21335731:ℝ)/143750)*a2*a3*b2*b3 + ((21188291:ℝ)/287500)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + ((290832:ℝ)/71875)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((1992:ℝ)/71875)*a2*a3*b1^2*b2*b3 + ((21335731:ℝ)/287500)*a2*a3^2*b2 + (1:ℝ)*a2*a3^2*b1 + ((145416:ℝ)/71875)*a2*a3^2*b1*b2 + ((996:ℝ)/71875)*a2*a3^2*b1^2*b2 + (73:ℝ)*a2^2*b3 + ((21335731:ℝ)/575000)*a2^2*b3^2 + ((66649:ℝ)/2500)*a2^2*b1 + (1:ℝ)*a2^2*b1*b3 + ((72708:ℝ)/71875)*a2^2*b1*b3^2 + ((913:ℝ)/5000)*a2^2*b1^2 + ((498:ℝ)/71875)*a2^2*b1^2*b3^2 + ((21335731:ℝ)/287500)*a2^2*a3*b3 + (1:ℝ)*a2^2*a3*b1 + ((145416:ℝ)/71875)*a2^2*a3*b1*b3 + ((996:ℝ)/71875)*a2^2*a3*b1^2*b3 + ((72708:ℝ)/71875)*a2^2*a3^2*b1 + ((498:ℝ)/71875)*a2^2*a3^2*b1^2 + ((834009:ℝ)/5000)*d*b3 + ((66649:ℝ)/2500)*d*b3^2 + ((834009:ℝ)/5000)*d*b2 + ((21188291:ℝ)/287500)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + ((66649:ℝ)/2500)*d*b2^2 + (1:ℝ)*d*b2^2*b3 + ((72708:ℝ)/71875)*d*b2^2*b3^2 + ((913:ℝ)/2500)*d*b1*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((913:ℝ)/2500)*d*b1*b2^2 + ((996:ℝ)/71875)*d*b1*b2^2*b3^2 + ((66649:ℝ)/1250)*d*a3*b3 + ((21188291:ℝ)/287500)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + ((145416:ℝ)/71875)*d*a3*b2^2*b3 + ((913:ℝ)/1250)*d*a3*b1*b3 + (2:ℝ)*d*a3*b1*b2 + ((1992:ℝ)/71875)*d*a3*b1*b2^2*b3 + (1:ℝ)*d*a3^2*b2 + ((72708:ℝ)/71875)*d*a3^2*b2^2 + ((913:ℝ)/2500)*d*a3^2*b1 + ((996:ℝ)/71875)*d*a3^2*b1*b2^2 + ((21188291:ℝ)/287500)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + ((66649:ℝ)/1250)*d*a2*b2 + (2:ℝ)*d*a2*b2*b3 + ((145416:ℝ)/71875)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((913:ℝ)/1250)*d*a2*b1*b2 + ((1992:ℝ)/71875)*d*a2*b1*b2*b3^2 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + ((290832:ℝ)/71875)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((3984:ℝ)/71875)*d*a2*a3*b1*b2*b3 + ((145416:ℝ)/71875)*d*a2*a3^2*b2 + ((1992:ℝ)/71875)*d*a2*a3^2*b1*b2 + (1:ℝ)*d*a2^2*b3 + ((72708:ℝ)/71875)*d*a2^2*b3^2 + ((913:ℝ)/2500)*d*a2^2*b1 + ((996:ℝ)/71875)*d*a2^2*b1*b3^2 + ((145416:ℝ)/71875)*d*a2^2*a3*b3 + ((1992:ℝ)/71875)*d*a2^2*a3*b1*b3 + ((996:ℝ)/71875)*d*a2^2*a3^2*b1 + ((913:ℝ)/5000)*d^2*b3^2 + (1:ℝ)*d^2*b2*b3 + ((913:ℝ)/5000)*d^2*b2^2 + ((498:ℝ)/71875)*d^2*b2^2*b3^2 + ((913:ℝ)/2500)*d^2*a3*b3 + (1:ℝ)*d^2*a3*b2 + ((996:ℝ)/71875)*d^2*a3*b2^2*b3 + ((498:ℝ)/71875)*d^2*a3^2*b2^2 + (1:ℝ)*d^2*a2*b3 + ((913:ℝ)/2500)*d^2*a2*b2 + ((996:ℝ)/71875)*d^2*a2*b2*b3^2 + ((1992:ℝ)/71875)*d^2*a2*a3*b2*b3 + ((996:ℝ)/71875)*d^2*a2*a3^2*b2 + ((498:ℝ)/71875)*d^2*a2^2*b3^2 + ((996:ℝ)/71875)*d^2*a2^2*a3*b3) := by
    unfold dq q; ring
  have hp : 0 < ((60882657:ℝ)/5000)*b3 + ((4865377:ℝ)/5000)*b3^2 + ((60882657:ℝ)/5000)*b2 + ((14657743:ℝ)/287500)*b2*b3 + (73:ℝ)*b2*b3^2 + ((4865377:ℝ)/5000)*b2^2 + (73:ℝ)*b2^2*b3 + ((2653842:ℝ)/71875)*b2^2*b3^2 + ((66649:ℝ)/2500)*b1*b3^2 + (146:ℝ)*b1*b2*b3 + ((66649:ℝ)/2500)*b1*b2^2 + ((72708:ℝ)/71875)*b1*b2^2*b3^2 + ((4865377:ℝ)/2500)*a3*b3 + ((125226521:ℝ)/575000)*a3*b2 + (146:ℝ)*a3*b2*b3 + (73:ℝ)*a3*b2^2 + ((21335731:ℝ)/287500)*a3*b2^2*b3 + ((834009:ℝ)/5000)*a3*b1 + ((66649:ℝ)/1250)*a3*b1*b3 + ((21188291:ℝ)/287500)*a3*b1*b2 + (2:ℝ)*a3*b1*b2*b3 + (1:ℝ)*a3*b1*b2^2 + ((145416:ℝ)/71875)*a3*b1*b2^2*b3 + ((913:ℝ)/2500)*a3*b1^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((996:ℝ)/71875)*a3*b1^2*b2^2*b3 + (73:ℝ)*a3^2*b2 + ((21335731:ℝ)/575000)*a3^2*b2^2 + ((66649:ℝ)/2500)*a3^2*b1 + (1:ℝ)*a3^2*b1*b2 + ((72708:ℝ)/71875)*a3^2*b1*b2^2 + ((913:ℝ)/5000)*a3^2*b1^2 + ((498:ℝ)/71875)*a3^2*b1^2*b2^2 + ((125226521:ℝ)/575000)*a2*b3 + (73:ℝ)*a2*b3^2 + ((4865377:ℝ)/2500)*a2*b2 + (146:ℝ)*a2*b2*b3 + ((21335731:ℝ)/287500)*a2*b2*b3^2 + ((834009:ℝ)/5000)*a2*b1 + ((21188291:ℝ)/287500)*a2*b1*b3 + (1:ℝ)*a2*b1*b3^2 + ((66649:ℝ)/1250)*a2*b1*b2 + (2:ℝ)*a2*b1*b2*b3 + ((145416:ℝ)/71875)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((913:ℝ)/2500)*a2*b1^2*b2 + ((996:ℝ)/71875)*a2*b1^2*b2*b3^2 + (146:ℝ)*a2*a3*b3 + (146:ℝ)*a2*a3*b2 + ((21335731:ℝ)/143750)*a2*a3*b2*b3 + ((21188291:ℝ)/287500)*a2*a3*b1 + (2:ℝ)*a2*a3*b1*b3 + (2:ℝ)*a2*a3*b1*b2 + ((290832:ℝ)/71875)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((1992:ℝ)/71875)*a2*a3*b1^2*b2*b3 + ((21335731:ℝ)/287500)*a2*a3^2*b2 + (1:ℝ)*a2*a3^2*b1 + ((145416:ℝ)/71875)*a2*a3^2*b1*b2 + ((996:ℝ)/71875)*a2*a3^2*b1^2*b2 + (73:ℝ)*a2^2*b3 + ((21335731:ℝ)/575000)*a2^2*b3^2 + ((66649:ℝ)/2500)*a2^2*b1 + (1:ℝ)*a2^2*b1*b3 + ((72708:ℝ)/71875)*a2^2*b1*b3^2 + ((913:ℝ)/5000)*a2^2*b1^2 + ((498:ℝ)/71875)*a2^2*b1^2*b3^2 + ((21335731:ℝ)/287500)*a2^2*a3*b3 + (1:ℝ)*a2^2*a3*b1 + ((145416:ℝ)/71875)*a2^2*a3*b1*b3 + ((996:ℝ)/71875)*a2^2*a3*b1^2*b3 + ((72708:ℝ)/71875)*a2^2*a3^2*b1 + ((498:ℝ)/71875)*a2^2*a3^2*b1^2 + ((834009:ℝ)/5000)*d*b3 + ((66649:ℝ)/2500)*d*b3^2 + ((834009:ℝ)/5000)*d*b2 + ((21188291:ℝ)/287500)*d*b2*b3 + (1:ℝ)*d*b2*b3^2 + ((66649:ℝ)/2500)*d*b2^2 + (1:ℝ)*d*b2^2*b3 + ((72708:ℝ)/71875)*d*b2^2*b3^2 + ((913:ℝ)/2500)*d*b1*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((913:ℝ)/2500)*d*b1*b2^2 + ((996:ℝ)/71875)*d*b1*b2^2*b3^2 + ((66649:ℝ)/1250)*d*a3*b3 + ((21188291:ℝ)/287500)*d*a3*b2 + (2:ℝ)*d*a3*b2*b3 + (1:ℝ)*d*a3*b2^2 + ((145416:ℝ)/71875)*d*a3*b2^2*b3 + ((913:ℝ)/1250)*d*a3*b1*b3 + (2:ℝ)*d*a3*b1*b2 + ((1992:ℝ)/71875)*d*a3*b1*b2^2*b3 + (1:ℝ)*d*a3^2*b2 + ((72708:ℝ)/71875)*d*a3^2*b2^2 + ((913:ℝ)/2500)*d*a3^2*b1 + ((996:ℝ)/71875)*d*a3^2*b1*b2^2 + ((21188291:ℝ)/287500)*d*a2*b3 + (1:ℝ)*d*a2*b3^2 + ((66649:ℝ)/1250)*d*a2*b2 + (2:ℝ)*d*a2*b2*b3 + ((145416:ℝ)/71875)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((913:ℝ)/1250)*d*a2*b1*b2 + ((1992:ℝ)/71875)*d*a2*b1*b2*b3^2 + (2:ℝ)*d*a2*a3*b3 + (2:ℝ)*d*a2*a3*b2 + ((290832:ℝ)/71875)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((3984:ℝ)/71875)*d*a2*a3*b1*b2*b3 + ((145416:ℝ)/71875)*d*a2*a3^2*b2 + ((1992:ℝ)/71875)*d*a2*a3^2*b1*b2 + (1:ℝ)*d*a2^2*b3 + ((72708:ℝ)/71875)*d*a2^2*b3^2 + ((913:ℝ)/2500)*d*a2^2*b1 + ((996:ℝ)/71875)*d*a2^2*b1*b3^2 + ((145416:ℝ)/71875)*d*a2^2*a3*b3 + ((1992:ℝ)/71875)*d*a2^2*a3*b1*b3 + ((996:ℝ)/71875)*d*a2^2*a3^2*b1 + ((913:ℝ)/5000)*d^2*b3^2 + (1:ℝ)*d^2*b2*b3 + ((913:ℝ)/5000)*d^2*b2^2 + ((498:ℝ)/71875)*d^2*b2^2*b3^2 + ((913:ℝ)/2500)*d^2*a3*b3 + (1:ℝ)*d^2*a3*b2 + ((996:ℝ)/71875)*d^2*a3*b2^2*b3 + ((498:ℝ)/71875)*d^2*a3^2*b2^2 + (1:ℝ)*d^2*a2*b3 + ((913:ℝ)/2500)*d^2*a2*b2 + ((996:ℝ)/71875)*d^2*a2*b2*b3^2 + ((1992:ℝ)/71875)*d^2*a2*a3*b2*b3 + ((996:ℝ)/71875)*d^2*a2*a3^2*b2 + ((498:ℝ)/71875)*d^2*a2^2*b3^2 + ((996:ℝ)/71875)*d^2*a2^2*a3*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 73 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 73 := ⟨a1 - 73, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 73`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 73 ≤ a1 ∨ 73 ≤ a2 ∨ 73 ≤ a3 ∨ 73 ≤ b1 ∨ 73 ≤ b2 ∨ 73 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 73`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 73 → a2 i ≤ 73 → a3 i ≤ 73 → b1 i ≤ 73 → b2 i ≤ 73 → b3 i ≤ 73 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 73 ∧ a2 i ≤ 73 ∧ a3 i ≤ 73 ∧ b1 i ≤ 73 ∧ b2 i ≤ 73 ∧ b3 i ≤ 73
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

end DesignT31Quarter

namespace DesignT33Quarter

/-- `g(x) = (x − t)² + 19`; the eight points `(t ± i√19)³` are the common zeros of `g(u₁), g(u₂), g(u₃)`. -/
noncomputable def g (x : ℝ) : ℝ := x^2 - (33/2)*x + (1393/16)

/-- the symmetric test polynomial `q` (orbit coefficients ['0', '316293187/640000', '-10975447/40000', '1027521/10000', '0', '0', '-1', '0', '-163/2500', '0']). -/
noncomputable def q (u1 u2 u3 : ℝ) : ℝ := ((316293187:ℝ)/640000)*u3 + ((316293187:ℝ)/640000)*u2 + ((-10975447:ℝ)/40000)*u2*u3 + ((316293187:ℝ)/640000)*u1 + ((-10975447:ℝ)/40000)*u1*u3 + ((-10975447:ℝ)/40000)*u1*u2 + ((1027521:ℝ)/10000)*u1*u2*u3 + (-1:ℝ)*u1*u2*u3^2 + (-1:ℝ)*u1*u2^2*u3 + ((-163:ℝ)/2500)*u1*u2^2*u3^2 + (-1:ℝ)*u1^2*u2*u3 + ((-163:ℝ)/2500)*u1^2*u2*u3^2 + ((-163:ℝ)/2500)*u1^2*u2^2*u3

/-- `q ∈ T_t`: `q = Σ_j g(u_j)·h_j` with `h_j` of multidegree ≤ (2,2,2) minus `2e_j`. -/
theorem q_mem (u1 u2 u3 : ℝ) : q u1 u2 u3 =
    g u1 * ((-1:ℝ)*u2*u3 + ((-163:ℝ)/2500)*u2*u3^2 + ((-163:ℝ)/2500)*u2^2*u3) + g u2 * (((227059:ℝ)/40000)*u3 + ((-10379:ℝ)/5000)*u1*u3 + ((-163:ℝ)/2500)*u1*u3^2) + g u3 * (((227059:ℝ)/40000)*u2 + ((227059:ℝ)/40000)*u1 + ((-7879:ℝ)/2500)*u1*u2) := by
  unfold q g; ring

theorem q_zero : q 0 0 0 = 0 := by unfold q; norm_num

/-- a second element of `T_t` with value `1` at the origin. -/
noncomputable def p0 (u1 u2 u3 : ℝ) : ℝ := (1:ℝ) + ((-88:ℝ)/1393)*u3 + ((16:ℝ)/4179)*u3^2 + ((-88:ℝ)/1393)*u2 + ((16:ℝ)/4179)*u2^2 + ((-88:ℝ)/1393)*u1 + ((16:ℝ)/4179)*u1^2

theorem p0_mem (u1 u2 u3 : ℝ) : p0 u1 u2 u3 =
    g u1 * (((16:ℝ)/4179)) + g u2 * (((16:ℝ)/4179)) + g u3 * (((16:ℝ)/4179)) := by
  unfold p0 g; ring

theorem p0_zero : p0 0 0 0 = 1 := by unfold p0; norm_num

/-- second difference `Δ_{ab} q = q(a+b) − q(a) − q(b) + q(0)`. -/
noncomputable def dq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  q (a1 + b1) (a2 + b2) (a3 + b3) - q a1 a2 a3 - q b1 b2 b3 + q 0 0 0

noncomputable def dp0 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  p0 (a1 + b1) (a2 + b2) (a3 + b3) - p0 a1 a2 a3 - p0 b1 b2 b3 + p0 0 0 0

/-- outside the box, first slot: after `a₁ = d + 103`, `−Δq` is a polynomial with positive coefficients. -/
theorem dq_neg_shift (d a2 a3 b1 b2 b3 : ℝ) (hd : 0 ≤ d) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq (d + 103) a2 a3 b1 b2 b3 < 0 := by
  have key : dq (d + 103) a2 a3 b1 b2 b3 = -(((1130471041:ℝ)/40000)*b3 + ((1130471041:ℝ)/40000)*b2 + ((255337:ℝ)/10000)*b2*b3 + ((1986767:ℝ)/2500)*b2*b3^2 + ((1986767:ℝ)/2500)*b2^2*b3 + ((16789:ℝ)/2500)*b2^2*b3^2 + (206:ℝ)*b1*b2*b3 + ((16789:ℝ)/1250)*b1*b2*b3^2 + ((16789:ℝ)/1250)*b1*b2^2*b3 + ((2399359:ℝ)/8000)*a3*b2 + ((1986767:ℝ)/1250)*a3*b2*b3 + ((1986767:ℝ)/2500)*a3*b2^2 + ((16789:ℝ)/1250)*a3*b2^2*b3 + ((10975447:ℝ)/40000)*a3*b1 + ((1032479:ℝ)/10000)*a3*b1*b2 + ((18039:ℝ)/625)*a3*b1*b2*b3 + ((18039:ℝ)/1250)*a3*b1*b2^2 + ((163:ℝ)/1250)*a3*b1*b2^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((163:ℝ)/1250)*a3*b1^2*b2*b3 + ((163:ℝ)/2500)*a3*b1^2*b2^2 + ((1986767:ℝ)/2500)*a3^2*b2 + ((16789:ℝ)/2500)*a3^2*b2^2 + ((18039:ℝ)/1250)*a3^2*b1*b2 + ((163:ℝ)/2500)*a3^2*b1*b2^2 + ((163:ℝ)/2500)*a3^2*b1^2*b2 + ((2399359:ℝ)/8000)*a2*b3 + ((1986767:ℝ)/2500)*a2*b3^2 + ((1986767:ℝ)/1250)*a2*b2*b3 + ((16789:ℝ)/1250)*a2*b2*b3^2 + ((10975447:ℝ)/40000)*a2*b1 + ((1032479:ℝ)/10000)*a2*b1*b3 + ((18039:ℝ)/1250)*a2*b1*b3^2 + ((18039:ℝ)/625)*a2*b1*b2*b3 + ((163:ℝ)/1250)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((163:ℝ)/2500)*a2*b1^2*b3^2 + ((163:ℝ)/1250)*a2*b1^2*b2*b3 + ((1986767:ℝ)/1250)*a2*a3*b3 + ((1986767:ℝ)/1250)*a2*a3*b2 + ((16789:ℝ)/625)*a2*a3*b2*b3 + ((1032479:ℝ)/10000)*a2*a3*b1 + ((18039:ℝ)/625)*a2*a3*b1*b3 + ((18039:ℝ)/625)*a2*a3*b1*b2 + ((163:ℝ)/625)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((163:ℝ)/1250)*a2*a3*b1^2*b3 + ((163:ℝ)/1250)*a2*a3*b1^2*b2 + ((16789:ℝ)/1250)*a2*a3^2*b2 + ((18039:ℝ)/1250)*a2*a3^2*b1 + ((163:ℝ)/1250)*a2*a3^2*b1*b2 + ((163:ℝ)/2500)*a2*a3^2*b1^2 + ((1986767:ℝ)/2500)*a2^2*b3 + ((16789:ℝ)/2500)*a2^2*b3^2 + ((18039:ℝ)/1250)*a2^2*b1*b3 + ((163:ℝ)/2500)*a2^2*b1*b3^2 + ((163:ℝ)/2500)*a2^2*b1^2*b3 + ((16789:ℝ)/1250)*a2^2*a3*b3 + ((18039:ℝ)/1250)*a2^2*a3*b1 + ((163:ℝ)/1250)*a2^2*a3*b1*b3 + ((163:ℝ)/2500)*a2^2*a3*b1^2 + ((163:ℝ)/2500)*a2^2*a3^2*b1 + ((10975447:ℝ)/40000)*d*b3 + ((10975447:ℝ)/40000)*d*b2 + ((1032479:ℝ)/10000)*d*b2*b3 + ((18039:ℝ)/1250)*d*b2*b3^2 + ((18039:ℝ)/1250)*d*b2^2*b3 + ((163:ℝ)/2500)*d*b2^2*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((163:ℝ)/1250)*d*b1*b2*b3^2 + ((163:ℝ)/1250)*d*b1*b2^2*b3 + ((1032479:ℝ)/10000)*d*a3*b2 + ((18039:ℝ)/625)*d*a3*b2*b3 + ((18039:ℝ)/1250)*d*a3*b2^2 + ((163:ℝ)/1250)*d*a3*b2^2*b3 + (2:ℝ)*d*a3*b1*b2 + ((163:ℝ)/625)*d*a3*b1*b2*b3 + ((163:ℝ)/1250)*d*a3*b1*b2^2 + ((18039:ℝ)/1250)*d*a3^2*b2 + ((163:ℝ)/2500)*d*a3^2*b2^2 + ((163:ℝ)/1250)*d*a3^2*b1*b2 + ((1032479:ℝ)/10000)*d*a2*b3 + ((18039:ℝ)/1250)*d*a2*b3^2 + ((18039:ℝ)/625)*d*a2*b2*b3 + ((163:ℝ)/1250)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((163:ℝ)/1250)*d*a2*b1*b3^2 + ((163:ℝ)/625)*d*a2*b1*b2*b3 + ((18039:ℝ)/625)*d*a2*a3*b3 + ((18039:ℝ)/625)*d*a2*a3*b2 + ((163:ℝ)/625)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((163:ℝ)/625)*d*a2*a3*b1*b3 + ((163:ℝ)/625)*d*a2*a3*b1*b2 + ((163:ℝ)/1250)*d*a2*a3^2*b2 + ((163:ℝ)/1250)*d*a2*a3^2*b1 + ((18039:ℝ)/1250)*d*a2^2*b3 + ((163:ℝ)/2500)*d*a2^2*b3^2 + ((163:ℝ)/1250)*d*a2^2*b1*b3 + ((163:ℝ)/1250)*d*a2^2*a3*b3 + ((163:ℝ)/1250)*d*a2^2*a3*b1 + (1:ℝ)*d^2*b2*b3 + ((163:ℝ)/2500)*d^2*b2*b3^2 + ((163:ℝ)/2500)*d^2*b2^2*b3 + (1:ℝ)*d^2*a3*b2 + ((163:ℝ)/1250)*d^2*a3*b2*b3 + ((163:ℝ)/2500)*d^2*a3*b2^2 + ((163:ℝ)/2500)*d^2*a3^2*b2 + (1:ℝ)*d^2*a2*b3 + ((163:ℝ)/2500)*d^2*a2*b3^2 + ((163:ℝ)/1250)*d^2*a2*b2*b3 + ((163:ℝ)/1250)*d^2*a2*a3*b3 + ((163:ℝ)/1250)*d^2*a2*a3*b2 + ((163:ℝ)/2500)*d^2*a2^2*b3) := by
    unfold dq q; ring
  have hp : 0 < ((1130471041:ℝ)/40000)*b3 + ((1130471041:ℝ)/40000)*b2 + ((255337:ℝ)/10000)*b2*b3 + ((1986767:ℝ)/2500)*b2*b3^2 + ((1986767:ℝ)/2500)*b2^2*b3 + ((16789:ℝ)/2500)*b2^2*b3^2 + (206:ℝ)*b1*b2*b3 + ((16789:ℝ)/1250)*b1*b2*b3^2 + ((16789:ℝ)/1250)*b1*b2^2*b3 + ((2399359:ℝ)/8000)*a3*b2 + ((1986767:ℝ)/1250)*a3*b2*b3 + ((1986767:ℝ)/2500)*a3*b2^2 + ((16789:ℝ)/1250)*a3*b2^2*b3 + ((10975447:ℝ)/40000)*a3*b1 + ((1032479:ℝ)/10000)*a3*b1*b2 + ((18039:ℝ)/625)*a3*b1*b2*b3 + ((18039:ℝ)/1250)*a3*b1*b2^2 + ((163:ℝ)/1250)*a3*b1*b2^2*b3 + (1:ℝ)*a3*b1^2*b2 + ((163:ℝ)/1250)*a3*b1^2*b2*b3 + ((163:ℝ)/2500)*a3*b1^2*b2^2 + ((1986767:ℝ)/2500)*a3^2*b2 + ((16789:ℝ)/2500)*a3^2*b2^2 + ((18039:ℝ)/1250)*a3^2*b1*b2 + ((163:ℝ)/2500)*a3^2*b1*b2^2 + ((163:ℝ)/2500)*a3^2*b1^2*b2 + ((2399359:ℝ)/8000)*a2*b3 + ((1986767:ℝ)/2500)*a2*b3^2 + ((1986767:ℝ)/1250)*a2*b2*b3 + ((16789:ℝ)/1250)*a2*b2*b3^2 + ((10975447:ℝ)/40000)*a2*b1 + ((1032479:ℝ)/10000)*a2*b1*b3 + ((18039:ℝ)/1250)*a2*b1*b3^2 + ((18039:ℝ)/625)*a2*b1*b2*b3 + ((163:ℝ)/1250)*a2*b1*b2*b3^2 + (1:ℝ)*a2*b1^2*b3 + ((163:ℝ)/2500)*a2*b1^2*b3^2 + ((163:ℝ)/1250)*a2*b1^2*b2*b3 + ((1986767:ℝ)/1250)*a2*a3*b3 + ((1986767:ℝ)/1250)*a2*a3*b2 + ((16789:ℝ)/625)*a2*a3*b2*b3 + ((1032479:ℝ)/10000)*a2*a3*b1 + ((18039:ℝ)/625)*a2*a3*b1*b3 + ((18039:ℝ)/625)*a2*a3*b1*b2 + ((163:ℝ)/625)*a2*a3*b1*b2*b3 + (1:ℝ)*a2*a3*b1^2 + ((163:ℝ)/1250)*a2*a3*b1^2*b3 + ((163:ℝ)/1250)*a2*a3*b1^2*b2 + ((16789:ℝ)/1250)*a2*a3^2*b2 + ((18039:ℝ)/1250)*a2*a3^2*b1 + ((163:ℝ)/1250)*a2*a3^2*b1*b2 + ((163:ℝ)/2500)*a2*a3^2*b1^2 + ((1986767:ℝ)/2500)*a2^2*b3 + ((16789:ℝ)/2500)*a2^2*b3^2 + ((18039:ℝ)/1250)*a2^2*b1*b3 + ((163:ℝ)/2500)*a2^2*b1*b3^2 + ((163:ℝ)/2500)*a2^2*b1^2*b3 + ((16789:ℝ)/1250)*a2^2*a3*b3 + ((18039:ℝ)/1250)*a2^2*a3*b1 + ((163:ℝ)/1250)*a2^2*a3*b1*b3 + ((163:ℝ)/2500)*a2^2*a3*b1^2 + ((163:ℝ)/2500)*a2^2*a3^2*b1 + ((10975447:ℝ)/40000)*d*b3 + ((10975447:ℝ)/40000)*d*b2 + ((1032479:ℝ)/10000)*d*b2*b3 + ((18039:ℝ)/1250)*d*b2*b3^2 + ((18039:ℝ)/1250)*d*b2^2*b3 + ((163:ℝ)/2500)*d*b2^2*b3^2 + (2:ℝ)*d*b1*b2*b3 + ((163:ℝ)/1250)*d*b1*b2*b3^2 + ((163:ℝ)/1250)*d*b1*b2^2*b3 + ((1032479:ℝ)/10000)*d*a3*b2 + ((18039:ℝ)/625)*d*a3*b2*b3 + ((18039:ℝ)/1250)*d*a3*b2^2 + ((163:ℝ)/1250)*d*a3*b2^2*b3 + (2:ℝ)*d*a3*b1*b2 + ((163:ℝ)/625)*d*a3*b1*b2*b3 + ((163:ℝ)/1250)*d*a3*b1*b2^2 + ((18039:ℝ)/1250)*d*a3^2*b2 + ((163:ℝ)/2500)*d*a3^2*b2^2 + ((163:ℝ)/1250)*d*a3^2*b1*b2 + ((1032479:ℝ)/10000)*d*a2*b3 + ((18039:ℝ)/1250)*d*a2*b3^2 + ((18039:ℝ)/625)*d*a2*b2*b3 + ((163:ℝ)/1250)*d*a2*b2*b3^2 + (2:ℝ)*d*a2*b1*b3 + ((163:ℝ)/1250)*d*a2*b1*b3^2 + ((163:ℝ)/625)*d*a2*b1*b2*b3 + ((18039:ℝ)/625)*d*a2*a3*b3 + ((18039:ℝ)/625)*d*a2*a3*b2 + ((163:ℝ)/625)*d*a2*a3*b2*b3 + (2:ℝ)*d*a2*a3*b1 + ((163:ℝ)/625)*d*a2*a3*b1*b3 + ((163:ℝ)/625)*d*a2*a3*b1*b2 + ((163:ℝ)/1250)*d*a2*a3^2*b2 + ((163:ℝ)/1250)*d*a2*a3^2*b1 + ((18039:ℝ)/1250)*d*a2^2*b3 + ((163:ℝ)/2500)*d*a2^2*b3^2 + ((163:ℝ)/1250)*d*a2^2*b1*b3 + ((163:ℝ)/1250)*d*a2^2*a3*b3 + ((163:ℝ)/1250)*d*a2^2*a3*b1 + (1:ℝ)*d^2*b2*b3 + ((163:ℝ)/2500)*d^2*b2*b3^2 + ((163:ℝ)/2500)*d^2*b2^2*b3 + (1:ℝ)*d^2*a3*b2 + ((163:ℝ)/1250)*d^2*a3*b2*b3 + ((163:ℝ)/2500)*d^2*a3*b2^2 + ((163:ℝ)/2500)*d^2*a3^2*b2 + (1:ℝ)*d^2*a2*b3 + ((163:ℝ)/2500)*d^2*a2*b3^2 + ((163:ℝ)/1250)*d^2*a2*b2*b3 + ((163:ℝ)/1250)*d^2*a2*a3*b3 + ((163:ℝ)/1250)*d^2*a2*a3*b2 + ((163:ℝ)/2500)*d^2*a2^2*b3 := by positivity
  linarith

theorem dq_neg_of_a1_ge (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 103 ≤ a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (h4 : 0 < b1) (h5 : 0 < b2) (h6 : 0 < b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, a1 = d + 103 := ⟨a1 - 103, by ring⟩
  exact dq_neg_shift d a2 a3 b1 b2 b3 (by linarith) h2 h3 h4 h5 h6

theorem dq_perm12 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a2 a1 a3 b2 b1 b3 := by unfold dq q; ring
theorem dq_perm13 (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq a3 a2 a1 b3 b2 b1 := by unfold dq q; ring
theorem dq_swap (a1 a2 a3 b1 b2 b3 : ℝ) : dq a1 a2 a3 b1 b2 b3 = dq b1 b2 b3 a1 a2 a3 := by unfold dq q; ring

/-- (assumption: all six coordinates positive, one of them `≥ 103`) `Δq < 0`. -/
theorem dq_neg_of_some_coord_ge (a1 a2 a3 b1 b2 b3 : ℝ) (p1 : 0 < a1) (p2 : 0 < a2) (p3 : 0 < a3)
    (p4 : 0 < b1) (p5 : 0 < b2) (p6 : 0 < b3)
    (h : 103 ≤ a1 ∨ 103 ≤ a2 ∨ 103 ≤ a3 ∨ 103 ≤ b1 ∨ 103 ≤ b2 ∨ 103 ≤ b3) : dq a1 a2 a3 b1 b2 b3 < 0 := by
  rcases h with h | h | h | h | h | h
  · exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p3 p4 p5 p6
  · rw [dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p1 p3 p5 p4 p6
  · rw [dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p2 p1 p6 p5 p4
  · rw [dq_swap]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p6 p1 p2 p3
  · rw [dq_swap, dq_perm12]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p4 p6 p2 p1 p3
  · rw [dq_swap, dq_perm13]; exact dq_neg_of_a1_ge _ _ _ _ _ _ h p5 p4 p3 p2 p1

/-- **Farkas closure** (assumptions: the finite box table `hbox` — every piece with all six coordinates `≤ 103`
has `Δq < 0`, checked exactly outside Lean —, positive coordinates, nonnegative weights, and the two design
equations for `q, p0 ∈ T_t`): there is no design.  `q(0) = 0`, so the `q`-equation forces every weight to vanish. -/
theorem no_design_of_box_table {ι : Type*} (s : Finset ι) (a1 a2 a3 b1 b2 b3 n : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < a1 i ∧ 0 < a2 i ∧ 0 < a3 i ∧ 0 < b1 i ∧ 0 < b2 i ∧ 0 < b3 i)
    (hn : ∀ i ∈ s, 0 ≤ n i)
    (hbox : ∀ i ∈ s, a1 i ≤ 103 → a2 i ≤ 103 → a3 i ≤ 103 → b1 i ≤ 103 → b2 i ≤ 103 → b3 i ≤ 103 →
      dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0)
    (hq : ∑ i ∈ s, n i * dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = q 0 0 0)
    (hp : ∑ i ∈ s, n i * dp0 (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) = p0 0 0 0) : False := by
  have hneg : ∀ i ∈ s, dq (a1 i) (a2 i) (a3 i) (b1 i) (b2 i) (b3 i) < 0 := by
    intro i hi
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpos i hi
    by_cases hall : a1 i ≤ 103 ∧ a2 i ≤ 103 ∧ a3 i ≤ 103 ∧ b1 i ≤ 103 ∧ b2 i ≤ 103 ∧ b3 i ≤ 103
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

end DesignT33Quarter

-- axioms (every theorem of every namespace)
#print axioms DesignT8.q_mem
#print axioms DesignT8.q_zero
#print axioms DesignT8.p0_mem
#print axioms DesignT8.p0_zero
#print axioms DesignT8.dq_neg_shift
#print axioms DesignT8.dq_neg_of_a1_ge
#print axioms DesignT8.dq_perm12
#print axioms DesignT8.dq_perm13
#print axioms DesignT8.dq_swap
#print axioms DesignT8.dq_neg_of_some_coord_ge
#print axioms DesignT8.no_design_of_box_table
#print axioms DesignT3Control.q_mem
#print axioms DesignT3Control.q_zero
#print axioms DesignT3Control.p0_mem
#print axioms DesignT3Control.p0_zero
#print axioms DesignT3Control.dq_neg_shift
#print axioms DesignT3Control.dq_neg_of_a1_ge
#print axioms DesignT3Control.dq_perm12
#print axioms DesignT3Control.dq_perm13
#print axioms DesignT3Control.dq_swap
#print axioms DesignT3Control.dq_neg_of_some_coord_ge
#print axioms DesignT3Control.no_design_of_box_table
#print axioms DesignT4.q_mem
#print axioms DesignT4.q_zero
#print axioms DesignT4.p0_mem
#print axioms DesignT4.p0_zero
#print axioms DesignT4.dq_neg_shift
#print axioms DesignT4.dq_neg_of_a1_ge
#print axioms DesignT4.dq_perm12
#print axioms DesignT4.dq_perm13
#print axioms DesignT4.dq_swap
#print axioms DesignT4.dq_neg_of_some_coord_ge
#print axioms DesignT4.no_design_of_box_table
#print axioms DesignT5.q_mem
#print axioms DesignT5.q_zero
#print axioms DesignT5.p0_mem
#print axioms DesignT5.p0_zero
#print axioms DesignT5.dq_neg_shift
#print axioms DesignT5.dq_neg_of_a1_ge
#print axioms DesignT5.dq_perm12
#print axioms DesignT5.dq_perm13
#print axioms DesignT5.dq_swap
#print axioms DesignT5.dq_neg_of_some_coord_ge
#print axioms DesignT5.no_design_of_box_table
#print axioms DesignT6.q_mem
#print axioms DesignT6.q_zero
#print axioms DesignT6.p0_mem
#print axioms DesignT6.p0_zero
#print axioms DesignT6.dq_neg_shift
#print axioms DesignT6.dq_neg_of_a1_ge
#print axioms DesignT6.dq_perm12
#print axioms DesignT6.dq_perm13
#print axioms DesignT6.dq_swap
#print axioms DesignT6.dq_neg_of_some_coord_ge
#print axioms DesignT6.no_design_of_box_table
#print axioms DesignT13Half.q_mem
#print axioms DesignT13Half.q_zero
#print axioms DesignT13Half.p0_mem
#print axioms DesignT13Half.p0_zero
#print axioms DesignT13Half.dq_neg_shift
#print axioms DesignT13Half.dq_neg_of_a1_ge
#print axioms DesignT13Half.dq_perm12
#print axioms DesignT13Half.dq_perm13
#print axioms DesignT13Half.dq_swap
#print axioms DesignT13Half.dq_neg_of_some_coord_ge
#print axioms DesignT13Half.no_design_of_box_table
#print axioms DesignT7.q_mem
#print axioms DesignT7.q_zero
#print axioms DesignT7.p0_mem
#print axioms DesignT7.p0_zero
#print axioms DesignT7.dq_neg_shift
#print axioms DesignT7.dq_neg_of_a1_ge
#print axioms DesignT7.dq_perm12
#print axioms DesignT7.dq_perm13
#print axioms DesignT7.dq_swap
#print axioms DesignT7.dq_neg_of_some_coord_ge
#print axioms DesignT7.no_design_of_box_table
#print axioms DesignT15Half.q_mem
#print axioms DesignT15Half.q_zero
#print axioms DesignT15Half.p0_mem
#print axioms DesignT15Half.p0_zero
#print axioms DesignT15Half.dq_neg_shift
#print axioms DesignT15Half.dq_neg_of_a1_ge
#print axioms DesignT15Half.dq_perm12
#print axioms DesignT15Half.dq_perm13
#print axioms DesignT15Half.dq_swap
#print axioms DesignT15Half.dq_neg_of_some_coord_ge
#print axioms DesignT15Half.no_design_of_box_table
#print axioms DesignT31Quarter.q_mem
#print axioms DesignT31Quarter.q_zero
#print axioms DesignT31Quarter.p0_mem
#print axioms DesignT31Quarter.p0_zero
#print axioms DesignT31Quarter.dq_neg_shift
#print axioms DesignT31Quarter.dq_neg_of_a1_ge
#print axioms DesignT31Quarter.dq_perm12
#print axioms DesignT31Quarter.dq_perm13
#print axioms DesignT31Quarter.dq_swap
#print axioms DesignT31Quarter.dq_neg_of_some_coord_ge
#print axioms DesignT31Quarter.no_design_of_box_table
#print axioms DesignT33Quarter.q_mem
#print axioms DesignT33Quarter.q_zero
#print axioms DesignT33Quarter.p0_mem
#print axioms DesignT33Quarter.p0_zero
#print axioms DesignT33Quarter.dq_neg_shift
#print axioms DesignT33Quarter.dq_neg_of_a1_ge
#print axioms DesignT33Quarter.dq_perm12
#print axioms DesignT33Quarter.dq_perm13
#print axioms DesignT33Quarter.dq_swap
#print axioms DesignT33Quarter.dq_neg_of_some_coord_ge
#print axioms DesignT33Quarter.no_design_of_box_table
