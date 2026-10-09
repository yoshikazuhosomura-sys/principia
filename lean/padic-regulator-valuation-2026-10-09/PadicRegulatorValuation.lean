/-
  `PadicRegulatorValuation` — root module of the bundle.

  The 31 modules under `PadicRegulatorValuation/` each begin with
  `import Mathlib` and nothing else, and some restate a lemma under the same
  name so that each file checks on its own. They cannot all be imported into
  one environment, so this root imports none of them; `lake build` builds
  every module through the glob in `lakefile.lean`.

  * `PadicRegulatorValuation.PadicHeightValuation`, `…2`, …, `…29`
  * `PadicRegulatorValuation.PadicHeightValuationCanonical`
  * `PadicRegulatorValuation.AnomalousEulerFactor` (companion note)
-/
