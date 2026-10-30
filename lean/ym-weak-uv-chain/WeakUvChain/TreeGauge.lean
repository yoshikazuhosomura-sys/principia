/-
Existence of a tree gauge (general form of axial gauge fixing). Single file; checks with `import Mathlib` only.

  Rooted tree: root r, parent map parent, depth depth (depth (parent v) < depth v at non-root points).
  A gauge transformation g acts on the link variable U v (in an arbitrary group G) of the tree edge v → parent v by
  U′ v = g v · U v · (g (parent v))⁻¹. There is g with U′ v = 1 on all tree edges, and its value at the root
  can be taken to be 1 (the remaining gauge freedom is the root alone).

Choosing a tree (e.g. along the axes) on the lattice points of a block gives a gauge making the tree links the identity.
That background bounds hold in this gauge is a separate premise.
-/
import Mathlib

namespace TreeGauge

variable {V G : Type*} [DecidableEq V] [Group G]

/-- Tree gauge: by recursion on depth, `g v = g (parent v) · (U v)⁻¹`, `g r = 1`. -/
noncomputable def treeGauge (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) : V → G
  | v => if h : v = r then 1 else treeGauge r parent depth hdepth U (parent v) * (U v)⁻¹
termination_by v => depth v
decreasing_by exact hdepth v h

theorem treeGauge_root (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) :
    treeGauge r parent depth hdepth U r = 1 := by
  rw [treeGauge]; simp

theorem treeGauge_step (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) (v : V) (hv : v ≠ r) :
    treeGauge r parent depth hdepth U v =
      treeGauge r parent depth hdepth U (parent v) * (U v)⁻¹ := by
  rw [treeGauge]; simp [hv]

/-- In the tree gauge, all tree-edge links become the identity. -/
theorem treeGauge_trivializes (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) (v : V) (hv : v ≠ r) :
    treeGauge r parent depth hdepth U v * U v *
      (treeGauge r parent depth hdepth U (parent v))⁻¹ = 1 := by
  rw [treeGauge_step r parent depth hdepth U v hv]
  group

/-- Existence: there is `g` with value 1 at the root and `g v · U v · (g (parent v))⁻¹ = 1` on all tree edges. -/
theorem exists_tree_gauge (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) :
    ∃ g : V → G, g r = 1 ∧ ∀ v, v ≠ r → g v * U v * (g (parent v))⁻¹ = 1 :=
  ⟨treeGauge r parent depth hdepth U, treeGauge_root r parent depth hdepth U,
    fun v hv => treeGauge_trivializes r parent depth hdepth U v hv⟩

/-- Uniqueness (with the root value fixed): two gauges with this property coincide. -/
theorem tree_gauge_unique (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) (g h : V → G)
    (hg0 : g r = 1) (hh0 : h r = 1)
    (hg : ∀ v, v ≠ r → g v * U v * (g (parent v))⁻¹ = 1)
    (hh : ∀ v, v ≠ r → h v * U v * (h (parent v))⁻¹ = 1) : ∀ v, g v = h v := by
  intro v
  induction hn : depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = r
    · subst hv; rw [hg0, hh0]
    · have hp := ih (depth (parent v)) (hn ▸ hdepth v hv) (parent v) rfl
      have e1 : g v = g (parent v) * (U v)⁻¹ := by
        have := hg v hv
        calc g v = g v * U v * (g (parent v))⁻¹ * (g (parent v) * (U v)⁻¹) := by group
          _ = g (parent v) * (U v)⁻¹ := by rw [this, one_mul]
      have e2 : h v = h (parent v) * (U v)⁻¹ := by
        have := hh v hv
        calc h v = h v * U v * (h (parent v))⁻¹ * (h (parent v) * (U v)⁻¹) := by group
          _ = h (parent v) * (U v)⁻¹ := by rw [this, one_mul]
      rw [e1, e2, hp]

#print axioms treeGauge_root
#print axioms treeGauge_step
#print axioms treeGauge_trivializes
#print axioms exists_tree_gauge
#print axioms tree_gauge_unique

end TreeGauge
