import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Four plaquettes in a row with two overlapping 3×1 loops fixed

Plaquette holonomies `P₁, P₂, P₃, P₄` (independent), loops `W_a = P₁P₂P₃`, `W_b = P₂P₃P₄`.

* `sum_pair_reindex`, `four_plaquette_weight`, `four_plaquette_constrained` : finite-group version of
  the effective weight.  With arbitrary plaquette weights `φᵢ : G → R` on a finite group `G`,
  summing over `(P₁, …, P₄)` with both loops fixed equals
  `∑_U (φ₂ ⋆ φ₃)(U) · φ₁(W_a U⁻¹) · φ₄(U⁻¹ W_b)` where `(φ₂ ⋆ φ₃)(U) = ∑_{P₂} φ₂(P₂) φ₃(P₂⁻¹U)`.
  (For SU(2) and Wilson weights the convolution is `Z₁(β|1+U|)`; the Haar version is not formalised.)
* `tree_identity_four`, `tree_lower_four`, `tree_attained_four`, `shape_four` : the abelianised tree level.
  With `a = f₁+f₂+f₃`, `b = f₂+f₃+f₄`, `min ∑ fᵢ² = (3a²+3b²−4ab)/5 = ((a²+b²) + 2(a−b)²)/5`, i.e. single loops
  and the composite loop enter in the ratio `1 : 2`.
* `tree_identity_three`, `shape_three` : the same for three plaquettes (`a = f₁+f₂`, `b = f₂+f₃`):
  `min = (2a²+2b²−2ab)/3 = ((a²+b²) + (a−b)²)/3`, ratio `1 : 1`.
-/

namespace LatticeGaugeFourPlaquetteChain

open Finset

section Group

variable {G : Type*} [Group G] [Fintype G]

theorem sum_pair_reindex {M : Type*} [AddCommMonoid M] (F : G → G → M) :
    ∑ p2 : G, ∑ p3 : G, F p2 p3 = ∑ u : G, ∑ p2 : G, F p2 (p2⁻¹ * u) := by
  rw [Finset.sum_comm (f := fun u p2 => F p2 (p2⁻¹ * u))]
  refine Finset.sum_congr rfl (fun p2 _ => ?_)
  exact (Equiv.sum_comp (Equiv.mulLeft p2⁻¹) (fun p3 => F p2 p3)).symm

theorem four_plaquette_weight {R : Type*} [CommSemiring R] (φ₁ φ₂ φ₃ φ₄ : G → R) (Wa Wb : G) :
    ∑ p2 : G, ∑ p3 : G, φ₁ (Wa * (p2 * p3)⁻¹) * φ₂ p2 * φ₃ p3 * φ₄ ((p2 * p3)⁻¹ * Wb)
      = ∑ u : G, (∑ p2 : G, φ₂ p2 * φ₃ (p2⁻¹ * u)) * φ₁ (Wa * u⁻¹) * φ₄ (u⁻¹ * Wb) := by
  rw [sum_pair_reindex]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p2 _ => ?_)
  simp only [mul_inv_cancel_left]
  ring

theorem four_plaquette_constrained {R : Type*} [CommSemiring R] [DecidableEq G]
    (φ₁ φ₂ φ₃ φ₄ : G → R) (Wa Wb : G) :
    ∑ p2 : G, ∑ p3 : G, ∑ p1 : G, ∑ p4 : G,
        (if p1 * p2 * p3 = Wa ∧ p2 * p3 * p4 = Wb then φ₁ p1 * φ₂ p2 * φ₃ p3 * φ₄ p4 else 0)
      = ∑ u : G, (∑ p2 : G, φ₂ p2 * φ₃ (p2⁻¹ * u)) * φ₁ (Wa * u⁻¹) * φ₄ (u⁻¹ * Wb) := by
  rw [← four_plaquette_weight]
  refine Finset.sum_congr rfl (fun p2 _ => Finset.sum_congr rfl (fun p3 _ => ?_))
  have h1 : ∀ p1 : G, (p1 * p2 * p3 = Wa) ↔ (p1 = Wa * (p2 * p3)⁻¹) := by
    intro p1; rw [eq_mul_inv_iff_mul_eq, mul_assoc]
  have h4 : ∀ p4 : G, (p2 * p3 * p4 = Wb) ↔ (p4 = (p2 * p3)⁻¹ * Wb) := by
    intro p4; rw [eq_inv_mul_iff_mul_eq]
  simp_rw [h1, h4, ite_and]
  simp [Finset.sum_ite_eq']

end Group

section Tree

theorem tree_identity_four (a b s : ℝ) :
    (a - s) ^ 2 + (b - s) ^ 2 + s ^ 2 / 2
      = (3 * a ^ 2 + 3 * b ^ 2 - 4 * a * b) / 5 + 5 / 2 * (s - 2 * (a + b) / 5) ^ 2 := by
  ring

theorem split_two (f2 f3 : ℝ) : f2 ^ 2 + f3 ^ 2 = (f2 + f3) ^ 2 / 2 + (f2 - f3) ^ 2 / 2 := by
  ring

theorem tree_lower_four (f1 f2 f3 f4 : ℝ) :
    (3 * (f1 + f2 + f3) ^ 2 + 3 * (f2 + f3 + f4) ^ 2 - 4 * (f1 + f2 + f3) * (f2 + f3 + f4)) / 5
      ≤ f1 ^ 2 + f2 ^ 2 + f3 ^ 2 + f4 ^ 2 := by
  have h : f1 ^ 2 + f2 ^ 2 + f3 ^ 2 + f4 ^ 2
      - (3 * (f1 + f2 + f3) ^ 2 + 3 * (f2 + f3 + f4) ^ 2 - 4 * (f1 + f2 + f3) * (f2 + f3 + f4)) / 5
      = (f2 - f3) ^ 2 / 2
        + 5 / 2 * ((f2 + f3) - 2 * ((f1 + f2 + f3) + (f2 + f3 + f4)) / 5) ^ 2 := by
    ring
  have h0 : 0 ≤ (f2 - f3) ^ 2 / 2
        + 5 / 2 * ((f2 + f3) - 2 * ((f1 + f2 + f3) + (f2 + f3 + f4)) / 5) ^ 2 := by
    positivity
  linarith

theorem tree_attained_four (a b : ℝ) :
    let f2 := (a + b) / 5
    let f3 := (a + b) / 5
    let f1 := a - f2 - f3
    let f4 := b - f2 - f3
    f1 + f2 + f3 = a ∧ f2 + f3 + f4 = b ∧
      f1 ^ 2 + f2 ^ 2 + f3 ^ 2 + f4 ^ 2 = (3 * a ^ 2 + 3 * b ^ 2 - 4 * a * b) / 5 := by
  refine ⟨by ring, by ring, by ring⟩

theorem shape_four (a b : ℝ) :
    (3 * a ^ 2 + 3 * b ^ 2 - 4 * a * b) / 5 = (1 / 5) * (a ^ 2 + b ^ 2) + (2 / 5) * (a - b) ^ 2 := by
  ring

theorem tree_identity_three (a b s : ℝ) :
    (a - s) ^ 2 + (b - s) ^ 2 + s ^ 2
      = (2 * a ^ 2 + 2 * b ^ 2 - 2 * a * b) / 3 + 3 * (s - (a + b) / 3) ^ 2 := by
  ring

theorem shape_three (a b : ℝ) :
    (2 * a ^ 2 + 2 * b ^ 2 - 2 * a * b) / 3 = (1 / 3) * (a ^ 2 + b ^ 2) + (1 / 3) * (a - b) ^ 2 := by
  ring

end Tree

end LatticeGaugeFourPlaquetteChain

#print axioms LatticeGaugeFourPlaquetteChain.sum_pair_reindex
#print axioms LatticeGaugeFourPlaquetteChain.four_plaquette_weight
#print axioms LatticeGaugeFourPlaquetteChain.four_plaquette_constrained
#print axioms LatticeGaugeFourPlaquetteChain.tree_identity_four
#print axioms LatticeGaugeFourPlaquetteChain.tree_lower_four
#print axioms LatticeGaugeFourPlaquetteChain.tree_attained_four
#print axioms LatticeGaugeFourPlaquetteChain.shape_four
#print axioms LatticeGaugeFourPlaquetteChain.tree_identity_three
#print axioms LatticeGaugeFourPlaquetteChain.shape_three
