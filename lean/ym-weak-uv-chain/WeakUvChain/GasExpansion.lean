/-
Entry to premise 9: algebra of the large-field expansion. Single file; checks with `import Mathlib` only.

  For a finite set Pl of plaquettes, split each plaquette weight into a small-field part s(p) and a large-field part ℓ(p) (e.g. the
  indicator partition χ_small + χ_large = 1 multiplied by the action factor).
  §1 Expansion: Pl_{p∈Pl} (s p + ℓ p) = Σ_{X ⊆ Pl} (Pl_{p∈X} ℓ p)(Pl_{p∈Pl∖X} s p) (Mathlib's prod_add)
  §2 Decomposition into connected components: for a partition comp X of X (pairwise disjoint, union X),
     Pl_{p∈X} ℓ p = Pl_{C ∈ comp X} z(C), z(C) = Pl_{p∈C} ℓ p (the activity is a product of local factors on the support)
  §3 Combined polymer representation: Pl_{p∈Pl} (s p + ℓ p) = Σ_{X⊆Pl} (Pl_{C∈comp X} z(C))(Pl_{p∈Pl∖X} s p)
  §4 Partition of unity: if s + ℓ = 1 then 1 = Σ_X (Pl_X ℓ)(Pl_{Pl∖X} s)
  The choice of connected components (adjacency relation) and the counting ((eΔ)ⁿ) are premises from the literature.
-/
import Mathlib

namespace GasExpansion

open Finset

variable {P : Type*} [DecidableEq P]

/-- §1 Expansion. -/
theorem expand (Pl : Finset P) (s ℓ : P → ℝ) :
    ∏ p ∈ Pl, (ℓ p + s p) = ∑ X ∈ Pl.powerset, (∏ p ∈ X, ℓ p) * ∏ p ∈ Pl \ X, s p :=
  prod_add ℓ s Pl

/-- §2 Product decomposition along a partition: the activity is a product of local factors on the support. -/
theorem prod_over_components (X : Finset P) (comp : Finset (Finset P))
    (hdisj : Set.PairwiseDisjoint (comp : Set (Finset P)) id) (hunion : comp.biUnion id = X)
    (ℓ : P → ℝ) :
    ∏ p ∈ X, ℓ p = ∏ C ∈ comp, ∏ p ∈ C, ℓ p := by
  rw [← hunion, prod_biUnion hdisj]
  rfl

/-- §3 Polymer representation: given a partition `comp X` of each `X`, the total weight is a sum of products of polymer activities. -/
theorem polymer_representation (Pl : Finset P) (s ℓ : P → ℝ) (comp : Finset P → Finset (Finset P))
    (hdisj : ∀ X ∈ Pl.powerset, Set.PairwiseDisjoint (comp X : Set (Finset P)) id)
    (hunion : ∀ X ∈ Pl.powerset, (comp X).biUnion id = X) :
    ∏ p ∈ Pl, (ℓ p + s p) =
      ∑ X ∈ Pl.powerset, (∏ C ∈ comp X, ∏ p ∈ C, ℓ p) * ∏ p ∈ Pl \ X, s p := by
  rw [expand]
  refine sum_congr rfl fun X hX => ?_
  rw [prod_over_components X (comp X) (hdisj X hX) (hunion X hX)]

/-- §4 Partition of unity. -/
theorem partition_of_unity (Pl : Finset P) (s ℓ : P → ℝ) (h1 : ∀ p ∈ Pl, ℓ p + s p = 1) :
    (1 : ℝ) = ∑ X ∈ Pl.powerset, (∏ p ∈ X, ℓ p) * ∏ p ∈ Pl \ X, s p := by
  rw [← expand, prod_congr rfl h1, prod_const_one]

/-- Concrete locality: if the action factor is a product over plaquettes `e^{−S} = Pl_p w(p)`, split `w = w·χ_s + w·χ_ℓ` on each plaquette;
the activity of a connected component of the large-field part is `Pl_{p∈C} w(p) χ_ℓ(p)` (a product of local factors on the support). -/
theorem weight_split (Pl : Finset P) (w χs χl : P → ℝ) (hχ : ∀ p ∈ Pl, χs p + χl p = 1)
    (comp : Finset P → Finset (Finset P))
    (hdisj : ∀ X ∈ Pl.powerset, Set.PairwiseDisjoint (comp X : Set (Finset P)) id)
    (hunion : ∀ X ∈ Pl.powerset, (comp X).biUnion id = X) :
    ∏ p ∈ Pl, w p = ∑ X ∈ Pl.powerset,
      (∏ C ∈ comp X, ∏ p ∈ C, (w p * χl p)) * ∏ p ∈ Pl \ X, (w p * χs p) := by
  have h : ∀ p ∈ Pl, w p = w p * χl p + w p * χs p := by
    intro p hp; rw [← mul_add, add_comm, hχ p hp, mul_one]
  rw [prod_congr rfl h]
  exact polymer_representation Pl (fun p => w p * χs p) (fun p => w p * χl p) comp hdisj hunion

#print axioms expand
#print axioms prod_over_components
#print axioms polymer_representation
#print axioms partition_of_unity
#print axioms weight_split

end GasExpansion
