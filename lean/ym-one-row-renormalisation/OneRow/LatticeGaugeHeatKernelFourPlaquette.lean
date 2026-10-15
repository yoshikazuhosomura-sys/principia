import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Semigroup closure of the inner integral for four plaquettes in a row (finite-group version)

Convolution on a finite group `G` with values in a commutative semiring:
`(f ⋆ g)(u) = ∑_p f(p) g(p⁻¹ u)`.

* `conv_assoc` : convolution is associative.
* `conv_delta_left`, `conv_delta_right` : the point mass at `1` is a two-sided unit.
* `convPow_add` : `f^{⋆(m+n)} = f^{⋆m} ⋆ f^{⋆n}` (discrete-time semigroup), `convPow_two_mul`.
* `four_plaquette_of_semigroup` : for any family `p : T → G → R` over an additive monoid `T`
  with `p s ⋆ p t = p (s + t)`, the four-plaquette sum with both loops `W_a = P₁P₂P₃`,
  `W_b = P₂P₃P₄` fixed (after solving for `P₁`, `P₄`) equals
  `∑_U p(t+t)(U) · p t (W_a U⁻¹) · p t (U⁻¹ W_b)`: the inner integral closes to `p (2t)`.
* `four_plaquette_convPow` : the same with `p n = f^{⋆n}`.

The Haar-measure (compact Lie group) version and the heat kernel itself are not formalised.
-/

namespace LatticeGaugeHeatKernelFourPlaquette

open Finset

variable {G : Type*} [Group G] [Fintype G] {R : Type*} [CommSemiring R]

/-- Convolution on a finite group. -/
def conv (f g : G → R) : G → R := fun u => ∑ p : G, f p * g (p⁻¹ * u)

theorem conv_assoc (f g h : G → R) : conv (conv f g) h = conv f (conv g h) := by
  funext u
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine Fintype.sum_equiv (Equiv.mulLeft p⁻¹) _ _ (fun q => ?_)
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

/-- The point mass at the identity. -/
def delta [DecidableEq G] : G → R := fun u => if u = 1 then 1 else 0

theorem conv_delta_left [DecidableEq G] (f : G → R) : conv delta f = f := by
  funext u
  simp [conv, delta]

theorem conv_delta_right [DecidableEq G] (f : G → R) : conv f delta = f := by
  funext u
  simp only [conv, delta, mul_ite, mul_one, mul_zero]
  have h : ∀ p : G, (p⁻¹ * u = 1) ↔ (u = p) := by
    intro p; rw [inv_mul_eq_one]; exact eq_comm
  simp_rw [h]
  simp

/-- Convolution powers: `f^{⋆0} = δ`, `f^{⋆(n+1)} = f^{⋆n} ⋆ f`. -/
def convPow [DecidableEq G] (f : G → R) : ℕ → G → R
  | 0 => delta
  | n + 1 => conv (convPow f n) f

theorem convPow_add [DecidableEq G] (f : G → R) (m n : ℕ) :
    convPow f (m + n) = conv (convPow f m) (convPow f n) := by
  induction n with
  | zero => simp [convPow, conv_delta_right]
  | succ n ih =>
    rw [← add_assoc, convPow, ih, conv_assoc, convPow]

theorem convPow_two_mul [DecidableEq G] (f : G → R) (n : ℕ) :
    convPow f (2 * n) = conv (convPow f n) (convPow f n) := by
  rw [two_mul, convPow_add]

theorem sum_pair_reindex {M : Type*} [AddCommMonoid M] (F : G → G → M) :
    ∑ p2 : G, ∑ p3 : G, F p2 p3 = ∑ u : G, ∑ p2 : G, F p2 (p2⁻¹ * u) := by
  rw [Finset.sum_comm (f := fun u p2 => F p2 (p2⁻¹ * u))]
  refine Finset.sum_congr rfl (fun p2 _ => ?_)
  exact (Equiv.sum_comp (Equiv.mulLeft p2⁻¹) (fun p3 => F p2 p3)).symm

theorem four_plaquette_of_semigroup {T : Type*} [AddMonoid T] (p : T → G → R)
    (hp : ∀ s t : T, conv (p s) (p t) = p (s + t)) (t : T) (Wa Wb : G) :
    ∑ p2 : G, ∑ p3 : G, p t (Wa * (p2 * p3)⁻¹) * p t p2 * p t p3 * p t ((p2 * p3)⁻¹ * Wb)
      = ∑ u : G, p (t + t) u * p t (Wa * u⁻¹) * p t (u⁻¹ * Wb) := by
  rw [sum_pair_reindex]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← hp t t]
  simp only [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p2 _ => ?_)
  simp only [mul_inv_cancel_left]
  ring

theorem four_plaquette_convPow [DecidableEq G] (f : G → R) (n : ℕ) (Wa Wb : G) :
    ∑ p2 : G, ∑ p3 : G, convPow f n (Wa * (p2 * p3)⁻¹) * convPow f n p2 * convPow f n p3
        * convPow f n ((p2 * p3)⁻¹ * Wb)
      = ∑ u : G, convPow f (n + n) u * convPow f n (Wa * u⁻¹) * convPow f n (u⁻¹ * Wb) :=
  four_plaquette_of_semigroup (convPow f) (fun s t => (convPow_add f s t).symm) n Wa Wb

end LatticeGaugeHeatKernelFourPlaquette

#print axioms LatticeGaugeHeatKernelFourPlaquette.conv_assoc
#print axioms LatticeGaugeHeatKernelFourPlaquette.conv_delta_left
#print axioms LatticeGaugeHeatKernelFourPlaquette.conv_delta_right
#print axioms LatticeGaugeHeatKernelFourPlaquette.convPow_add
#print axioms LatticeGaugeHeatKernelFourPlaquette.convPow_two_mul
#print axioms LatticeGaugeHeatKernelFourPlaquette.sum_pair_reindex
#print axioms LatticeGaugeHeatKernelFourPlaquette.four_plaquette_of_semigroup
#print axioms LatticeGaugeHeatKernelFourPlaquette.four_plaquette_convPow
