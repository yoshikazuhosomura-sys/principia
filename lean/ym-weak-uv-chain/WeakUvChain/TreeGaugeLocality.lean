/-
Statement part of premise 8: in the tree gauge the tree edges are the identity, so a gauge-invariant quantity
(the object of the background bounds) is determined by the values on non-tree edges.
Single file; checks with `import Mathlib` only.

  Points V, edges E (source src, target tgt), root r, parent, depth, tree edge treeEdge v (v → parent v, v ≠ r).
  Gauge action (g·U)(e) = g(src e) U(e) g(tgt e)⁻¹. Tree gauge gfix U for each U (same recursion as TreeGauge).
  (i) The configuration transformed by gfix U is the identity on all tree edges.
  (ii) For gauge-invariant F, if two configurations, transformed to the tree gauge, agree on non-tree edges,
       then their F-values are equal.
  So F is a function of "the values on non-tree edges in the tree gauge".
-/
import Mathlib

namespace TreeGaugeLocality

variable {V E G : Type*} [DecidableEq V] [Group G]

/-- Recursion of the tree gauge (same definition as in TreeGauge, placed in this file). -/
noncomputable def treeGauge (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) : V → G
  | v => if h : v = r then 1 else treeGauge r parent depth hdepth U (parent v) * (U v)⁻¹
termination_by v => depth v
decreasing_by exact hdepth v h

theorem treeGauge_step (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v) (U : V → G) (v : V) (hv : v ≠ r) :
    treeGauge r parent depth hdepth U v =
      treeGauge r parent depth hdepth U (parent v) * (U v)⁻¹ := by
  rw [treeGauge]; simp [hv]

/-- Gauge action. -/
def act (src tgt : E → V) (g : V → G) (U : E → G) : E → G :=
  fun e => g (src e) * U e * (g (tgt e))⁻¹

/-- Tree gauge for each configuration `U`: uses the value on the tree edge `treeEdge v` as transport to the parent. -/
noncomputable def gfix (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v)
    (treeEdge : ∀ v : V, v ≠ r → E) (U : E → G) : V → G :=
  treeGauge r parent depth hdepth (fun v => if h : v = r then 1 else U (treeEdge v h))

/-- (i) The configuration transformed by the tree gauge is the identity on every tree edge. -/
theorem gfix_tree_edge (src tgt : E → V) (r : V) (parent : V → V) (depth : V → ℕ)
    (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v)
    (treeEdge : ∀ v : V, v ≠ r → E)
    (hsrc : ∀ v hv, src (treeEdge v hv) = v) (htgt : ∀ v hv, tgt (treeEdge v hv) = parent v)
    (U : E → G) (v : V) (hv : v ≠ r) :
    act src tgt (gfix r parent depth hdepth treeEdge U) U (treeEdge v hv) = 1 := by
  unfold act gfix
  rw [hsrc, htgt, treeGauge_step r parent depth hdepth _ v hv]
  simp only [hv, dite_false]
  group

/-- (ii) Locality of the background: a gauge-invariant `F` is determined by the values on non-tree edges in the tree gauge. -/
theorem invariant_depends_on_nontree (src tgt : E → V) (r : V) (parent : V → V)
    (depth : V → ℕ) (hdepth : ∀ v, v ≠ r → depth (parent v) < depth v)
    (treeEdge : ∀ v : V, v ≠ r → E)
    (hsrc : ∀ v hv, src (treeEdge v hv) = v) (htgt : ∀ v hv, tgt (treeEdge v hv) = parent v)
    {R : Type*} (F : (E → G) → R) (hF : ∀ g U, F (act src tgt g U) = F U)
    (U U' : E → G)
    (hnon : ∀ e, (∀ v hv, treeEdge v hv ≠ e) →
      act src tgt (gfix r parent depth hdepth treeEdge U) U e =
        act src tgt (gfix r parent depth hdepth treeEdge U') U' e) :
    F U = F U' := by
  rw [← hF (gfix r parent depth hdepth treeEdge U) U,
    ← hF (gfix r parent depth hdepth treeEdge U') U']
  congr 1
  funext e
  by_cases h : ∃ v hv, treeEdge v hv = e
  · obtain ⟨v, hv, rfl⟩ := h
    rw [gfix_tree_edge src tgt r parent depth hdepth treeEdge hsrc htgt U v hv,
      gfix_tree_edge src tgt r parent depth hdepth treeEdge hsrc htgt U' v hv]
  · exact hnon e (fun v hv hve => h ⟨v, hv, hve⟩)

#print axioms treeGauge_step
#print axioms gfix_tree_edge
#print axioms invariant_depends_on_nontree

end TreeGaugeLocality
