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
-/
