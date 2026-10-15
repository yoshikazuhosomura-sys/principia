/-
  `OneLink` — root module of the bundle.

  The seven modules under `OneLink/` each begin with `import Mathlib` and
  nothing else. Five of them use the namespace `PerfectFamily` and restate
  definitions and lemmas under the same names so that each file checks on its
  own. They cannot all be imported into one environment, so this root imports
  none of them; `lake build` builds every module through the glob in
  `lakefile.lean`.

  * `OneLink.LatticeGaugeOneLink` — namespaces `StarInequality`, `StapleCurve`,
    `OneLinkSeries`, `CompleteFamilyLattice`, `StaplePerturbation`,
    `WilsonOneLink`
  * `OneLink.PerfectFamily` — namespace `PerfectFamily` (the bound on `ℤ^d`)
  * `OneLink.PlaquetteCounting` — namespaces `PlaquettePacking`,
    `PlaquetteCounting`
  * `OneLink.PerfectFamilyConstruction`, `OneLink.PerfectFamilyBound`,
    `OneLink.PerfectFamilyPeriodic`, `OneLink.PerfectFamilyEdges` — namespace
    `PerfectFamily` (complete families of k-cells)
-/
