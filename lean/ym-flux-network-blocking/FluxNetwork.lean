/-
  `FluxNetwork` — root module of the bundle.

  The modules under `FluxNetwork/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `FluxNetwork.CoarseFaceFourTorusTags`
  * `FluxNetwork.CoarseFaceHodgeSplit`
  * `FluxNetwork.LatticeGaugeAllFacesBlocking`
  * `FluxNetwork.LatticeGaugeAveragedBlockFlowLedger`
  * `FluxNetwork.LatticeGaugeBlockCovarianceLedger`
  * `FluxNetwork.LatticeGaugeFluxNetwork`
  * `FluxNetwork.LatticeGaugeQuarticConeNormLedger`
  * `FluxNetwork.LatticeGaugeQuarticRowColumnBound`
  * `FluxNetwork.LatticeGaugeQuarticSplitTriangle`
  * `FluxNetwork.LatticeGaugeTailTypeClassification`
  * `FluxNetwork.LatticeGaugeToeplitzTailSplit`
  * `FluxNetwork.LatticeGaugeWeightedTailBound`
-/
