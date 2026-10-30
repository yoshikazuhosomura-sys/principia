/-
  `WeakUvChain` — root module of the bundle.

  The modules under `WeakUvChain/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `WeakUvChain.ActivityFixedInterval`
  * `WeakUvChain.AnalyticFloor`
  * `WeakUvChain.BackgroundConstants`
  * `WeakUvChain.BlockBoundaryCount`
  * `WeakUvChain.BlockGaussianStep`
  * `WeakUvChain.BoundaryRegulator`
  * `WeakUvChain.BoxConnectivity`
  * `WeakUvChain.BoxFiberSiteSum`
  * `WeakUvChain.BoxFromFace`
  * `WeakUvChain.BoxTwoColorKP`
  * `WeakUvChain.CThetaReadings`
  * `WeakUvChain.ChainEndToEnd`
  * `WeakUvChain.ChainEndToEndFineSupport`
  * `WeakUvChain.ChainMovingActivity`
  * `WeakUvChain.ClassSiteSum`
  * `WeakUvChain.ClassStepRemainder`
  * `WeakUvChain.DifferenceContinuity`
  * `WeakUvChain.EvenDifferenceCoupling`
  * `WeakUvChain.GasExpansion`
  * `WeakUvChain.GibbsContinuity`
  * `WeakUvChain.HessianGap`
  * `WeakUvChain.KPToDobrushin`
  * `WeakUvChain.KernelMarginNumbers`
  * `WeakUvChain.KernelMarginStages`
  * `WeakUvChain.KernelMarginWindow`
  * `WeakUvChain.KernelWindowTable`
  * `WeakUvChain.LargeFieldCoupling`
  * `WeakUvChain.LargeFieldStep`
  * `WeakUvChain.LargeFieldSupply`
  * `WeakUvChain.LargeSetRegulator`
  * `WeakUvChain.Lattice24KP`
  * `WeakUvChain.LatticeBlockReflection`
  * `WeakUvChain.LatticeTwoColorKP`
  * `WeakUvChain.MarginNumbers`
  * `WeakUvChain.MarginRatioTwo`
  * `WeakUvChain.MovingActivity`
  * `WeakUvChain.NontreeBackground`
  * `WeakUvChain.PolymerBlocking`
  * `WeakUvChain.PolymerComponents`
  * `WeakUvChain.PolymerGasDobrushin`
  * `WeakUvChain.PolymerGasFreeEnergy`
  * `WeakUvChain.PolymerGasKP`
  * `WeakUvChain.PolymerGeometry`
  * `WeakUvChain.PolymerMerge`
  * `WeakUvChain.PullbackOrbitLimit`
  * `WeakUvChain.ReflectionSupportScale`
  * `WeakUvChain.RegularityConstant`
  * `WeakUvChain.RegularityRadius`
  * `WeakUvChain.RegularityStep`
  * `WeakUvChain.SharpWindow`
  * `WeakUvChain.SizeSplitKP`
  * `WeakUvChain.SmallRemKernel`
  * `WeakUvChain.SupplyLedger`
  * `WeakUvChain.TreeGauge`
  * `WeakUvChain.TreeGaugeLocality`
  * `WeakUvChain.TwoColorEncoding`
  * `WeakUvChain.TwoColorPolymerSum`
  * `WeakUvChain.TwoStageSmallField`
  * `WeakUvChain.UltravioletAssembly`
  * `WeakUvChain.UltravioletChain`
  * `WeakUvChain.UltravioletGlue`
  * `WeakUvChain.VertexClassWindow`
  * `WeakUvChain.WeakUltravioletExistence`
  * `WeakUvChain.WeightRecursion`
-/
