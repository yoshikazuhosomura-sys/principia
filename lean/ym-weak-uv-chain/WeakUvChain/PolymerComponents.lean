/-
Construction of connected components for premise 9. Single file; checks with `import Mathlib` only.

  Plaquette type P, adjacency relation adj (symmetric; *-adjacency or nearest neighbour, passed as an argument),
  finite set of plaquettes X.
  §1 Paths Conn adj X running only inside X; symmetry and transitivity
  §2 Connected component component adj X p = {q ∈ X | Conn adj X p q} and the family components adj X
  §3 The components partition X (pairwise disjoint, union X); each is nonempty and connected; plaquettes in different
     components are not adjacent (the compatibility form of the polymer gas)
  §4 This construction satisfies the "partition" hypothesis of GasExpansion: polymer representation and splitting of
     per-plaquette weights (copies of §1–§3 and weight_split of GasExpansion, with the component family plugged in)
  §5 The counting bound (number of connected sets of size n containing p ≤ (eΔ)ⁿ) is from the literature; stated only as a Prop
-/
import Mathlib

namespace PolymerComponents

open Finset

set_option linter.unusedSectionVars false

variable {P : Type*} [DecidableEq P]

/-! ## 1. Paths inside X -/

/-- There is a path staying inside `X`, moving one step at a time along `adj`. -/
def Conn (adj : P → P → Prop) (X : Finset P) : P → P → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ adj a b)

theorem conn_symm (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (X : Finset P) {p q : P}
    (h : Conn adj X p q) : Conn adj X q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hsymm _ _ hbc.2.2⟩ ih

theorem conn_trans (adj : P → P → Prop) (X : Finset P) {p q r : P}
    (h₁ : Conn adj X p q) (h₂ : Conn adj X q r) : Conn adj X p r :=
  Relation.ReflTransGen.trans h₁ h₂

/-- A path remains a path when the set is enlarged. -/
theorem conn_mono (adj : P → P → Prop) {X Y : Finset P} (hXY : X ⊆ Y) {p q : P}
    (h : Conn adj X p q) : Conn adj Y p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hXY hbc.1, hXY hbc.2.1, hbc.2.2⟩

/-- A set `C` is connected for `adj`: any two points of `C` are joined by a path inside `C`. -/
def IsConnectedSet (adj : P → P → Prop) (C : Finset P) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, Conn adj C a b

/-! ## 2. Connected components -/

open Classical in
/-- The connected component of `p` (points of `X` reachable from `p` by a path). -/
noncomputable def component (adj : P → P → Prop) (X : Finset P) (p : P) : Finset P :=
  X.filter (fun q => Conn adj X p q)

/-- The family of components. -/
noncomputable def components (adj : P → P → Prop) (X : Finset P) : Finset (Finset P) :=
  X.image (component adj X)

theorem mem_component (adj : P → P → Prop) (X : Finset P) (p q : P) :
    q ∈ component adj X p ↔ q ∈ X ∧ Conn adj X p q := by
  classical
  unfold component; rw [mem_filter]

theorem self_mem_component (adj : P → P → Prop) (X : Finset P) {p : P} (hp : p ∈ X) :
    p ∈ component adj X p :=
  (mem_component adj X p p).mpr ⟨hp, Relation.ReflTransGen.refl⟩

theorem component_subset (adj : P → P → Prop) (X : Finset P) (p : P) :
    component adj X p ⊆ X := fun _ hq => ((mem_component adj X p _).mp hq).1

/-- The component of a point in a component is that component. -/
theorem component_eq (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (X : Finset P) {p q : P}
    (hq : q ∈ component adj X p) : component adj X q = component adj X p := by
  have hpq := ((mem_component adj X p q).mp hq).2
  ext r
  rw [mem_component, mem_component]
  constructor
  · rintro ⟨hr, hqr⟩; exact ⟨hr, conn_trans adj X hpq hqr⟩
  · rintro ⟨hr, hpr⟩; exact ⟨hr, conn_trans adj X (conn_symm adj hsymm X hpq) hpr⟩

theorem mem_components (adj : P → P → Prop) (X : Finset P) (C : Finset P) :
    C ∈ components adj X ↔ ∃ p ∈ X, component adj X p = C := by
  unfold components; exact mem_image

/-! ## 3. The components form a partition -/

/-- Components are pairwise disjoint (the form of `hdisj` in GasExpansion). -/
theorem components_disjoint (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (X : Finset P) :
    Set.PairwiseDisjoint (components adj X : Set (Finset P)) id := by
  intro C hC C' hC' hne
  obtain ⟨p, _, rfl⟩ := (mem_components adj X C).mp hC
  obtain ⟨q, _, rfl⟩ := (mem_components adj X C').mp hC'
  change Disjoint (component adj X p) (component adj X q)
  rw [disjoint_left]
  intro r hrp hrq
  exact hne ((component_eq adj hsymm X hrp).symm.trans (component_eq adj hsymm X hrq))

/-- The union of the components is `X` (the form of `hunion` in GasExpansion). -/
theorem components_union (adj : P → P → Prop) (X : Finset P) :
    (components adj X).biUnion id = X := by
  ext q
  rw [mem_biUnion]
  constructor
  · rintro ⟨C, hC, hqC⟩
    obtain ⟨p, _, rfl⟩ := (mem_components adj X C).mp hC
    exact component_subset adj X p hqC
  · intro hq
    exact ⟨component adj X q, (mem_components adj X _).mpr ⟨q, hq, rfl⟩,
      self_mem_component adj X hq⟩

/-- Components are nonempty. -/
theorem components_nonempty (adj : P → P → Prop) (X : Finset P) {C : Finset P}
    (hC : C ∈ components adj X) : C.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := (mem_components adj X C).mp hC
  exact ⟨p, self_mem_component adj X hp⟩

/-- A path in `X` stays inside the component of its starting point. -/
theorem conn_within_component (adj : P → P → Prop) (X : Finset P) {p q : P}
    (h : Conn adj X p q) : Conn adj (component adj X p) p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hpb hbc ih =>
    have hb : b ∈ component adj X p := (mem_component adj X p b).mpr ⟨hbc.1, hpb⟩
    have hc : c ∈ component adj X p :=
      (mem_component adj X p c).mpr ⟨hbc.2.1, Relation.ReflTransGen.tail hpb hbc⟩
    exact Relation.ReflTransGen.tail ih ⟨hb, hc, hbc.2.2⟩

/-- Each component is a connected set. -/
theorem components_connected (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (X : Finset P)
    {C : Finset P} (hC : C ∈ components adj X) : IsConnectedSet adj C := by
  obtain ⟨p, _, rfl⟩ := (mem_components adj X C).mp hC
  intro a ha b hb
  have hpa := conn_within_component adj X ((mem_component adj X p a).mp ha).2
  have hpb := conn_within_component adj X ((mem_component adj X p b).mp hb).2
  exact conn_trans adj _ (conn_symm adj hsymm _ hpa) hpb

/-- Plaquettes in different components are not adjacent (if adjacent, same component). The compatibility form of the polymer gas. -/
theorem components_nonadjacent (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (X : Finset P)
    {C C' : Finset P} (hC : C ∈ components adj X) (hC' : C' ∈ components adj X)
    {a b : P} (ha : a ∈ C) (hb : b ∈ C') (hab : adj a b) : C = C' := by
  obtain ⟨p, _, rfl⟩ := (mem_components adj X C).mp hC
  obtain ⟨q, _, rfl⟩ := (mem_components adj X C').mp hC'
  have haX := component_subset adj X p ha
  have hbX := component_subset adj X q hb
  have hb' : b ∈ component adj X a :=
    (mem_component adj X a b).mpr ⟨hbX, Relation.ReflTransGen.single ⟨haX, hbX, hab⟩⟩
  rw [← component_eq adj hsymm X ha, ← component_eq adj hsymm X hb,
    component_eq adj hsymm X hb']

/-- The partition is unique: a family that is disjoint, has union `X`, has connected pieces and no adjacency between
pieces equals the component family (each piece `C` equals the component of any of its points `p`). -/
theorem component_of_piece (adj : P → P → Prop) (X : Finset P)
    (comp : Finset (Finset P))
    (hunion : comp.biUnion id = X)
    (hconn : ∀ C ∈ comp, IsConnectedSet adj C)
    (hsep : ∀ C ∈ comp, ∀ C' ∈ comp, ∀ a ∈ C, ∀ b ∈ C', adj a b → C = C')
    {C : Finset P} (hC : C ∈ comp) {p : P} (hp : p ∈ C) : component adj X p = C := by
  have hCX : C ⊆ X := by
    intro x hx; rw [← hunion]; exact mem_biUnion.mpr ⟨C, hC, hx⟩
  ext q
  rw [mem_component]
  constructor
  · rintro ⟨-, hpq⟩
    -- Stay in C along the path
    induction hpq with
    | refl => exact hp
    | @tail b c _ hbc ih =>
      have hcX := hbc.2.1
      rw [← hunion] at hcX
      obtain ⟨C', hC', hcC'⟩ := mem_biUnion.mp hcX
      have := hsep C hC C' hC' b ih c hcC' hbc.2.2
      rw [this]; exact hcC'
  · intro hq
    exact ⟨hCX hq, conn_mono adj hCX (hconn C hC p hp q hq)⟩

/-! ## 4. Satisfying the partition hypothesis of GasExpansion -/

/-- Copy of GasExpansion.expand. -/
theorem expand (Pl : Finset P) (s ℓ : P → ℝ) :
    ∏ p ∈ Pl, (ℓ p + s p) = ∑ X ∈ Pl.powerset, (∏ p ∈ X, ℓ p) * ∏ p ∈ Pl \ X, s p :=
  prod_add ℓ s Pl

/-- Copy of GasExpansion.prod_over_components. -/
theorem prod_over_components (X : Finset P) (comp : Finset (Finset P))
    (hdisj : Set.PairwiseDisjoint (comp : Set (Finset P)) id) (hunion : comp.biUnion id = X)
    (ℓ : P → ℝ) :
    ∏ p ∈ X, ℓ p = ∏ C ∈ comp, ∏ p ∈ C, ℓ p := by
  rw [← hunion, prod_biUnion hdisj]
  rfl

/-- Copy of GasExpansion.polymer_representation. -/
theorem polymer_representation (Pl : Finset P) (s ℓ : P → ℝ) (comp : Finset P → Finset (Finset P))
    (hdisj : ∀ X ∈ Pl.powerset, Set.PairwiseDisjoint (comp X : Set (Finset P)) id)
    (hunion : ∀ X ∈ Pl.powerset, (comp X).biUnion id = X) :
    ∏ p ∈ Pl, (ℓ p + s p) =
      ∑ X ∈ Pl.powerset, (∏ C ∈ comp X, ∏ p ∈ C, ℓ p) * ∏ p ∈ Pl \ X, s p := by
  rw [expand]
  refine sum_congr rfl fun X hX => ?_
  rw [prod_over_components X (comp X) (hdisj X hX) (hunion X hX)]

/-- Copy of GasExpansion.weight_split. -/
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

/-- Junction: the component family `components adj` satisfies the two hypotheses of GasExpansion. -/
theorem components_satisfy_gas (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (Pl : Finset P) :
    (∀ X ∈ Pl.powerset, Set.PairwiseDisjoint (components adj X : Set (Finset P)) id) ∧
    (∀ X ∈ Pl.powerset, (components adj X).biUnion id = X) :=
  ⟨fun X _ => components_disjoint adj hsymm X, fun X _ => components_union adj X⟩

/-- Polymer representation (by connected components): Π_p (ℓ p + s p) = Σ_X (Π_{C ∈ comp_adj X} Π_{p∈C} ℓ p)(Π_{Pl∖X} s).
No partition hypothesis remains. -/
theorem polymer_representation_components (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a)
    (Pl : Finset P) (s ℓ : P → ℝ) :
    ∏ p ∈ Pl, (ℓ p + s p) =
      ∑ X ∈ Pl.powerset, (∏ C ∈ components adj X, ∏ p ∈ C, ℓ p) * ∏ p ∈ Pl \ X, s p :=
  polymer_representation Pl s ℓ (components adj)
    (components_satisfy_gas adj hsymm Pl).1 (components_satisfy_gas adj hsymm Pl).2

/-- Splitting of per-plaquette weights (by connected components). -/
theorem weight_split_components (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a)
    (Pl : Finset P) (w χs χl : P → ℝ) (hχ : ∀ p ∈ Pl, χs p + χl p = 1) :
    ∏ p ∈ Pl, w p = ∑ X ∈ Pl.powerset,
      (∏ C ∈ components adj X, ∏ p ∈ C, (w p * χl p)) * ∏ p ∈ Pl \ X, (w p * χs p) :=
  weight_split Pl w χs χl hχ (components adj)
    (components_satisfy_gas adj hsymm Pl).1 (components_satisfy_gas adj hsymm Pl).2

/-- Gas form term by term: in each term `X`, the polymers are nonempty, connected, pairwise disjoint and pairwise non-adjacent. -/
theorem gas_term_structure (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (X : Finset P) :
    (∀ C ∈ components adj X, C.Nonempty ∧ IsConnectedSet adj C ∧ C ⊆ X) ∧
    Set.PairwiseDisjoint (components adj X : Set (Finset P)) id ∧
    (∀ C ∈ components adj X, ∀ C' ∈ components adj X, ∀ a ∈ C, ∀ b ∈ C', adj a b → C = C') := by
  refine ⟨fun C hC => ⟨components_nonempty adj X hC, components_connected adj hsymm X hC, ?_⟩,
    components_disjoint adj hsymm X, fun C hC C' hC' a ha b hb hab =>
      components_nonadjacent adj hsymm X hC hC' ha hb hab⟩
  obtain ⟨p, _, rfl⟩ := (mem_components adj X C).mp hC
  exact component_subset adj X p

/-! ## 5. Counting (from the literature; statement only) -/

/-- Adjacency degree ≤ Δ (for *-adjacency of plaquettes, the value of Δ is fixed by the lattice). -/
def BoundedDegree (adj : P → P → Prop) (Δ : ℝ) : Prop :=
  ∀ (U : Finset P) (p : P), by classical exact ((U.filter (adj p)).card : ℝ) ≤ Δ

/-- (from the literature) Counting connected sets: the number of connected sets of size `n` containing `p` is ≤ (eΔ)ⁿ.
No proof is given here (a literature result of Kotecký–Preiss / tree-counting type). -/
def ConnectedSetCount (adj : P → P → Prop) (Δ : ℝ) : Prop :=
  ∀ (U : Finset P) (p : P) (n : ℕ),
    by classical exact
      ((U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C)).card : ℝ) ≤
        (Real.exp 1 * Δ) ^ n

/-- Interface for the (from the literature) statement: the type of the literature result that the degree bound implies the counting bound. -/
def CountingFromDegree (adj : P → P → Prop) : Prop :=
  ∀ Δ : ℝ, 0 ≤ Δ → BoundedDegree adj Δ → ConnectedSetCount adj Δ

/-- If the counting bound holds, each polymer (component) of each term is among the counted objects (connected sets):
a component `C` with `p ∈ C` is an element of `{C | p ∈ C ∧ C.card = |C| ∧ connected}`. -/
theorem component_counted (adj : P → P → Prop) (hsymm : ∀ a b, adj a b → adj b a) (U X : Finset P)
    (hXU : X ⊆ U) {C : Finset P} (hC : C ∈ components adj X) {p : P} (hp : p ∈ C) :
    by classical exact
      C ∈ U.powerset.filter (fun C' => p ∈ C' ∧ C'.card = C.card ∧ IsConnectedSet adj C') := by
  classical
  obtain ⟨q, _, rfl⟩ := (mem_components adj X C).mp hC
  rw [mem_filter, mem_powerset]
  exact ⟨(component_subset adj X q).trans hXU, hp, rfl,
    components_connected adj hsymm X ((mem_components adj X _).mpr ⟨q, by assumption, rfl⟩)⟩

#print axioms conn_symm
#print axioms conn_trans
#print axioms conn_mono
#print axioms mem_component
#print axioms self_mem_component
#print axioms component_subset
#print axioms component_eq
#print axioms mem_components
#print axioms components_disjoint
#print axioms components_union
#print axioms components_nonempty
#print axioms conn_within_component
#print axioms components_connected
#print axioms components_nonadjacent
#print axioms component_of_piece
#print axioms expand
#print axioms prod_over_components
#print axioms polymer_representation
#print axioms weight_split
#print axioms components_satisfy_gas
#print axioms polymer_representation_components
#print axioms weight_split_components
#print axioms gas_term_structure
#print axioms component_counted

end PolymerComponents
