/-
  `CoarseChain` — root module of the bundle.

  The modules under `CoarseChain/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `CoarseChain.LatticeGaugeBlockPoincare`
  * `CoarseChain.LatticeGaugeCenterCovariance`
  * `CoarseChain.LatticeGaugeCoarseChainPoincare`
  * `CoarseChain.LatticeGaugeDoeblinPoincare`
  * `CoarseChain.LatticeGaugeDoubleWellTestbed`
  * `CoarseChain.LatticeGaugeHiddenConvexity`
  * `CoarseChain.LatticeGaugeInfluenceRecursion`
  * `CoarseChain.LatticeGaugeDobrushinIntervalTable` (version 2, 2026-10-17: table of intervals to windows)
  * `CoarseChain.LatticeGaugePinnedCoarseChain` (version 2, 2026-10-17: Proposition PIN, algebra)
-/
