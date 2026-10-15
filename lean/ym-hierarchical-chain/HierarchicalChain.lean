/-
  `HierarchicalChain` — root module of the bundle.

  The modules under `HierarchicalChain/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `HierarchicalChain.LatticeGaugeClassResidualTelescoping`
  * `HierarchicalChain.LatticeGaugeHierarchicalChainGeneral`
  * `HierarchicalChain.LatticeGaugeHierarchicalShapeFlow`
  * `HierarchicalChain.LatticeGaugeHierarchicalTubeChain`
  * `HierarchicalChain.LatticeGaugeHierarchicalUpperTube`
-/
