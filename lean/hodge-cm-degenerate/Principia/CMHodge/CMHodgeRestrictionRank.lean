/-
  Finite-dimensional linear algebra and exact arithmetic behind the restriction test for
  the characteristic map of a torsion sheaf supported on a divisor.  No geometry, no
  sheaves, no Ext groups appear: the geometric inputs (compatibility with restriction to
  an open set, and the dimensions measured in a model) enter as hypotheses.  Nothing about
  the Hodge conjecture, algebraicity or semiregularity is asserted.

  Contents.
  1. Restriction: if two linear maps agree after composing with maps to a common target,
     the kernel of the first lies in the kernel of the composite of the second.
  2. Rank bounds: a kernel contained in a subspace of dimension 9 inside a space of
     dimension 66 forces rank at least 57; hence it cannot equal a kernel of dimension 12.
  3. Exact arithmetic of two rational pairs replacing a factor 2 (all factors at least 3),
     one of them filling the divisor class exactly (no residual component).
  4. The degree-ten / degree-twelve window for both pairs, with the glue values used.
-/
import Mathlib

namespace RestrictionRank

open Module

/-! ### 1. Restriction -/

variable {K : Type*} [Field K]

/-- If `rA ∘ evF = rB ∘ evE`, then `ker evF ≤ ker (rB ∘ evE)`. -/
theorem ker_le_ker_comp {H A B C : Type*}
    [AddCommGroup H] [Module K H] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (evF : H →ₗ[K] A) (evE : H →ₗ[K] B) (rA : A →ₗ[K] C) (rB : B →ₗ[K] C)
    (hc : rA.comp evF = rB.comp evE) :
    LinearMap.ker evF ≤ LinearMap.ker (rB.comp evE) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← hc, LinearMap.comp_apply, hx, map_zero]

/-- Combined with a second inclusion (the one coming from the Chern character), the
kernel lies in the meet. -/
theorem ker_le_inf {H A : Type*} [AddCommGroup H] [Module K H] [AddCommGroup A] [Module K A]
    (f : H →ₗ[K] A) (S T : Submodule K H) (hS : LinearMap.ker f ≤ S)
    (hT : LinearMap.ker f ≤ T) : LinearMap.ker f ≤ S ⊓ T :=
  le_inf hS hT

/-! ### 2. Rank bounds -/

/-- A kernel inside `S` gives `rank ≥ dim V − dim S`. -/
theorem rank_ge_of_ker_le {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : V →ₗ[K] W) (S : Submodule K V) (h : LinearMap.ker f ≤ S) :
    finrank K V - finrank K S ≤ finrank K (LinearMap.range f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_mono h
  omega

/-- The numeric instance: dimension 66, a subspace of dimension 9, rank at least 57. -/
theorem rank_ge_57 {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : V →ₗ[K] W) (S : Submodule K V) (h : LinearMap.ker f ≤ S)
    (hV : finrank K V = 66) (hS : finrank K S = 9) :
    57 ≤ finrank K (LinearMap.range f) := by
  have := rank_ge_of_ker_le f S h
  omega

/-- Such a kernel cannot equal a kernel of dimension 12. -/
theorem ker_ne_of_dim {V W U : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U] [FiniteDimensional K V]
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) (S : Submodule K V) (h : LinearMap.ker f ≤ S)
    (hS : finrank K S = 9) (hg : finrank K (LinearMap.ker g) = 12) :
    LinearMap.ker f ≠ LinearMap.ker g := by
  intro heq
  have := Submodule.finrank_mono (heq ▸ h : LinearMap.ker g ≤ S)
  omega

/-- The dimension count of `HT²` of an abelian sixfold, `15 + 36 + 15 = 66 = C(12,2)`,
and `66 − 9 = 57 > 54 = 66 − 12`. -/
theorem ht2_count : 15 + 36 + 15 = 66 ∧ Nat.choose 12 2 = 66 ∧ 66 - 9 = 57 ∧ 66 - 12 = 54 ∧
    54 < 57 := by
  refine ⟨rfl, by decide, rfl, rfl, by norm_num⟩

/-! ### 3. Exact arithmetic of the rational pairs -/

/-- The trace of `a + b t + c t²` in `Z[t]/(t³+t²−6t−7)`: `Tr 1 = 3`, `Tr t = −1`,
`Tr t² = 13`. -/
def tr3 (a b c : ℤ) : ℤ := 3*a - b + 13*c

theorem chosen_traces : tr3 119 (-11) (-9) = 251 ∧ tr3 12 4 2 = 58 ∧
    2 * tr3 119 (-11) (-9) = 502 ∧ 3 * tr3 12 4 2 = 174 := by
  unfold tr3; norm_num

/-- The coin value that the two rational triples must share (degree six unchanged). -/
def coinM : ℤ := 8033253626

/-- A pair with every factor at least 3 (the factor 2 of the earlier pair is gone). -/
theorem pair_s1 :
    5 + 80 + 7475 = (7560 : ℤ) ∧ 1098 + 1463 + 4999 = (7560 : ℤ) ∧
    5 * 80 * 7475 + 1098 * 1463 * 4999 = coinM ∧
    502 + 174 + 80 + 1098 + 6 = (1860 : ℤ) ∧ (1860 : ℤ) ≤ 7560 := by
  unfold coinM; norm_num

/-- A pair filling the class exactly: `502 + 174 + 2798 + 4083 + 3 = 7560`. -/
theorem pair_h2 :
    134 + 2798 + 4628 = (7560 : ℤ) ∧ 522 + 2955 + 4083 = (7560 : ℤ) ∧
    134 * 2798 * 4628 + 522 * 2955 * 4083 = coinM ∧
    502 + 174 + 2798 + 4083 + 3 = (7560 : ℤ) := by
  unfold coinM; norm_num

/-- The earlier pair, as a check of the coin value. -/
theorem pair_old : 678 * 3414 * 3468 + 413 * 7145 * 2 = coinM := by
  unfold coinM; norm_num

/-! ### 4. The window for both pairs -/

/-- The degree-ten budget `9 g⁵ − 144 g q²` at `g = 7560`, `q = 19`. -/
def budget : ℤ := 222254972880605400960

theorem budget_eq : budget = 9 * 7560^5 - 144 * 7560 * 19^2 := by
  unfold budget; norm_num

/-- The four conditions of the window, the class `[C'].Θ`, the point count, and a
non-negative representation `720 a + 796632 b` (with `b = 23`). -/
def WindowOK (cost glue cp n0 n a : ℤ) : Prop :=
  cost - budget ≤ 24 * glue ∧ 15121 * glue ≤ 2 * n0 ∧
  24 * cp = 24 * glue - (cost - budget) ∧ 0 ≤ cp ∧
  2 * n = 2 * n0 - 15121 * glue ∧ 0 ≤ n ∧
  720 * a + 796632 * 23 = cp ∧ 0 ≤ a

theorem window_s1 : WindowOK 363931751568603895488 6636257135593521408 733058023593584136
    112667325739674352411968 62493903666019533806784 1018136143854530 := by
  unfold WindowOK budget; norm_num

theorem window_h2 : WindowOK 352968621103145988288 9292539547525183488 3846137538252659016
    118791732342612557717568 48535487093548407956544 5341857691992134 := by
  unfold WindowOK budget; norm_num

/-- The earlier pair (reproduced numbers, as a control of the statement). -/
theorem window_old : WindowOK 339730415179989962688 6636257135593521408 1741447039785831336
    108872438127675098482368 58699016054020279877184 2418676444121540 := by
  unfold WindowOK budget; norm_num

end RestrictionRank

#print axioms RestrictionRank.ker_le_ker_comp
#print axioms RestrictionRank.ker_le_inf
#print axioms RestrictionRank.rank_ge_of_ker_le
#print axioms RestrictionRank.rank_ge_57
#print axioms RestrictionRank.ker_ne_of_dim
#print axioms RestrictionRank.ht2_count
#print axioms RestrictionRank.chosen_traces
#print axioms RestrictionRank.pair_s1
#print axioms RestrictionRank.pair_h2
#print axioms RestrictionRank.pair_old
#print axioms RestrictionRank.budget_eq
#print axioms RestrictionRank.window_s1
#print axioms RestrictionRank.window_h2
#print axioms RestrictionRank.window_old
