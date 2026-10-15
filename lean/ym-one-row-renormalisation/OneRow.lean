/-
  `OneRow` — root module of the bundle.

  The modules under `OneRow/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `OneRow.LatticeGaugeClassResidualTelescoping`
  * `OneRow.LatticeGaugeFourPlaquetteChain`
  * `OneRow.LatticeGaugeFundAdjointRefit`
  * `OneRow.LatticeGaugeHeatKernelFourPlaquette`
  * `OneRow.LatticeGaugePrefactorFlowFixedPoint`
  * `OneRow.LatticeGaugeRatioTwoCriterion`
  * `OneRow.LatticeGaugeShapeRemainderUniform`
-/
