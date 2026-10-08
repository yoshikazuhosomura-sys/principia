/-
  Exact arithmetic and finite linear algebra behind a union-of-complete-intersections object
  `[O_X → ν_*O_Z̃] ⊗ O(A)` on an abelian variety, with `Z` a union of codimension-two
  intersections `D_a ∩ D_b` indexed by the edges of a graph.

  Nothing here is geometry: the Koszul / inclusion–exclusion formulas, the secant space and the
  vanishing of `H²` on a union of two affine opens enter only through the identities they produce.
-/
import Mathlib

namespace SecantGraph

/-! ### Fourfold calibration (cyclic graph, `n` translates of `Θ`, `d = 2n − 9`) -/

/-- Pairs of vertex-disjoint edges of the `n`-cycle whose four vertices are not consecutive,
times `Θ⁴ = 24`, written in `d = 2n − 9`: the `(d+9)(3d−3)` isolated points. -/
theorem isolated_points (n : ℤ) : 12 * n * (n - 5) = ((2*n - 9) + 9) * (3*(2*n - 9) - 3) := by
  ring

theorem unnormalised_points (d : ℤ) :
    (d + 9) * (3*d - 3) - (d + 9) * (2*d - 1) = (d + 9) * (d - 2) := by
  ring

/-- Degree three forces the twist `k = 3` (for a nonempty cycle). -/
theorem twist_three (k n : ℚ) (hn : n ≠ 0) :
    k^3/6 - k*n + 2*n = k*(k^2 - 2*n)/6 ↔ k = 3 := by
  constructor
  · intro h
    have h2 : n * (6 - 2*k) = 0 := by linarith [h]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hn
    · linarith
  · intro h; subst h; ring

/-- Degree four with `k = 3`, `n = (d+9)/2`: the number of unnormalised points needed. -/
theorem points_needed (d : ℚ) :
    24 * (d^2/24 - (27/8 - 7 * ((d + 9)/2) / 12)) = (d + 9) * (d - 2) := by
  ring

/-! ### One class: the lift to `B_2³` degenerates -/

/-- Degree four for a single class `s ∈ ℤ` on an `n`-cycle with the forced twist `t = 3s`. -/
theorem one_class (s n : ℤ) (h : s^2 * (2*n - 9) = 19) : (s = 1 ∨ s = -1) ∧ n = 14 := by
  have hpos : 0 < 2*n - 9 := by
    by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg s]
  have hs2 : s^2 ≤ 19 := by nlinarith
  have hb : -4 ≤ s ∧ s ≤ 4 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := hb
  interval_cases s <;> omega

/-- The degree-four identity behind (C2): the mixed second difference of the slot weight
`g(u) = (t−u)² + q` is `2ab`. -/
theorem second_difference_weight (t q a b : ℚ) :
    ((t - (a+b))^2 + q) - ((t - a)^2 + q) - ((t - b)^2 + q) + (t^2 + q) = 2*a*b := by
  ring

/-- Slot functional on an exponential: `ℓ_a(e^{xP}) = ((x+a)² + q)/2`. -/
theorem slot_on_exponential (a x q : ℚ) :
    x^2/2 + a*x + (a^2 + q)/2 = ((x + a)^2 + q)/2 := by
  ring

/-- Degree eight for one piece `D_s ∩ D_s'` of equal classes: the second difference of
`((t−u)²+q)u²` changes sign with the size of `s`. -/
theorem degree_eight_piece (t q s : ℚ) :
    ((t - 2*s)^2 + q) * (2*s)^2 - 2 * (((t - s)^2 + q) * s^2) + (t^2 + q) * 0^2
      = 2 * s^2 * ((t - 3*s)^2 + q - 2*s^2) := by
  ring

theorem degree_eight_sign_small : 2 * (1:ℚ)^2 * ((3 - 3*1)^2 + 19 - 2*1^2) > 0 := by norm_num
theorem degree_eight_sign_large : 2 * (4:ℚ)^2 * ((12 - 3*4)^2 + 19 - 2*4^2) < 0 := by norm_num

/-! ### A degree-≤6 design with twist `t = 9` -/

/-- (C2) for the design: three `Θ`-edges, three stars `K_{1,3}` with centre `Θ` and leaves in one
Galois orbit `θ², 4−θ, 9+θ−θ²`, one star `K_{1,4}` with centre `2Θ` and leaves `Θ`.
The identity holds in any commutative ring. -/
theorem c2_design_nine {R : Type*} [CommRing R] (θ : R) :
    3 * (1 * 1) + 3 * (1 * θ^2) + 3 * (1 * (4 - θ)) + 3 * (1 * (9 + θ - θ^2)) + 4 * (2 * 1)
      = (50 : R) := by
  ring

/-- and `(t² + q)/2 = 50` for `t = 9`, `q = 19`. -/
theorem c2_twist_nine : ((9:ℤ)^2 + 19) = 2 * 50 := by norm_num

theorem design_nine_counts :
    3 * 2 + 3 * (1 + 3) + (1 + 4) = 23 ∧ 3 * 1 + 3 * 3 + 4 = 16 ∧ (81 + 19) / 2 = 50 := by
  norm_num

/-! ### The B-field test is empty for a support containing `D_a ∩ D_b` -/

/-- If the restriction factors through a space all of whose elements vanish
(`H²` of the union of the two affine opens `X∖D_a`, `X∖D_b`), it is zero. -/
theorem factor_through_zero {K V W Y : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]
    (f : V →ₗ[K] W) (g : W →ₗ[K] Y) (hW : ∀ w : W, w = 0) : g ∘ₗ f = 0 := by
  ext v
  simp [hW (f v)]

/-- Removing one intersection keeps a pair `D_c ∩ D_c'` in the support as soon as the graph had
at least two edges, so the test stays empty. -/
theorem still_empty (e : ℕ) (he : 2 ≤ e) : 1 ≤ e - 1 := by omega

/-- Control with a non-ample `E = pr_i^*θ_0`: `H²(O_X)` has dimension `C(6,2) = 15`, the forms
touching the factor span `9`, the surviving part is `C(4,2) = 6`, and `3 + 9 = 12 ≤ 15`. -/
theorem nonample_control :
    Nat.choose 6 2 = 15 ∧ Nat.choose 6 2 - 9 = Nat.choose 4 2 ∧ 3 + 9 ≤ Nat.choose 6 2 := by
  decide

/-! ### Kernel dimension bookkeeping on `HT² = H²(O) ⊕ H¹(T) ⊕ H⁰(∧²T)` -/

theorem ht2_dim : Nat.choose 6 2 + 6 * 6 + Nat.choose 6 2 = 66 := by decide
theorem kernel_split : 12 = 9 + 3 ∧ 66 - 12 = 54 ∧ 66 - 36 = 30 := by decide

end SecantGraph

#print axioms SecantGraph.isolated_points
#print axioms SecantGraph.unnormalised_points
#print axioms SecantGraph.twist_three
#print axioms SecantGraph.points_needed
#print axioms SecantGraph.one_class
#print axioms SecantGraph.second_difference_weight
#print axioms SecantGraph.slot_on_exponential
#print axioms SecantGraph.degree_eight_piece
#print axioms SecantGraph.degree_eight_sign_small
#print axioms SecantGraph.degree_eight_sign_large
#print axioms SecantGraph.c2_design_nine
#print axioms SecantGraph.c2_twist_nine
#print axioms SecantGraph.design_nine_counts
#print axioms SecantGraph.factor_through_zero
#print axioms SecantGraph.still_empty
#print axioms SecantGraph.nonample_control
#print axioms SecantGraph.ht2_dim
#print axioms SecantGraph.kernel_split
