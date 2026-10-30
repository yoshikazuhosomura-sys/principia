# lean/ym-weak-uv-chain

The Lean 4 development cited by the paper "A conditional theorem: weak ultraviolet existence of four-dimensional SU(2) lattice Yang–Mills theory in a small box, with a machine-checked chain from per-step hypotheses" (Yoshikazu Hosomura, with the assistance of Claude; 2026-10-30), kept under `papers/ym-weak-uv-chain` in this repository. The correspondence table of the paper matches its statements with the declarations below.

## Contents
- `WeakUvChain/<File>.lean` — 64 modules, each beginning with `import Mathlib` and checking on its own (no module imports another). Byte-identical to the files of the web bundle `principia-ym-weak-uv-chain-2026-10-30.tar.gz` (sha256 of the archive `69976db4756e390cff99afa8f0139f9588602f2291e19a154280f58a4db89ef8`); the sha256 of each file is listed below.
- `WeakUvChain.lean` — root module; imports nothing.
- `axioms.txt` — the bundle's `axioms-<File>.txt` for every file, concatenated: the full output of `lake env lean <File>.lean`, 1403 `#print axioms` lines in total.
- `lakefile.lean`, `lean-toolchain`, `lake-manifest.json` — the lake project, pinned to Lean 4 `v4.33.1` and Mathlib `v4.33.1` (commit `0df444a3`).

No `sorry`, no `axiom` declaration, no `native_decide`. Every `#print axioms` line prints `[propext, Classical.choice, Quot.sound]` or a subset of it (in files that `open Classical`, Lean prints `Classical.choice` as `choice`), or that the statement depends on no axioms.

## Main statements

| statement of the paper | file | declaration |
|---|---|---|
| Theorem 4.1 (implication) | `WeakUltravioletExistence.lean` | `WeakUltravioletExistence.weak_uv_skeleton`, `exists_bare_inverse_coupling` |
| Theorem 5.3 (the chain) | `ChainMovingActivity.lean` | `TwoStageSmallField.rarity_two_stage` composed with `ChainMoving.chain_end_to_end_moving` |
| §5.1 (reflection positivity from the fine support, composed with the chain in constant-coefficient form) | `ChainEndToEndFineSupport.lean` | `FineSupportReflection.chain_end_to_end_fine_support` |

## How to check
Lean 4 `v4.33.1`, Mathlib `v4.33.1` (commit `0df444a3`, pinned in `lake-manifest.json`).

    lake exe cache get
    LEAN_NUM_THREADS=1 lake env lean WeakUvChain/<File>.lean

for each file, and compare the output with the section of `axioms.txt` for that file. `lake build` builds every module through the glob in `lakefile.lean`, one module at a time with `LEAN_NUM_THREADS=1`.

## What lies outside Lean
Checked: the implication of Theorem 4.1 (from the hypotheses (H-β), (H-reg), (H-sf), (H-Cauchy) to the conclusion), the chain of Theorem 5.3 from per-step hypotheses to those hypotheses, and the composed statement of §5.1. Not checked: the premises themselves (Table 2 of the paper) — none of them is established in four dimensions, they enter as hypotheses — and the numbers of the appendices, which are floating-point, one-loop or free-field computations. Literal constants in the files are thresholds of sufficient conditions or hypotheses about computed values, not certificates of them. Some files place copies of other files side by side so that a seam is type-checked in one file (see the table below). Seven files print linter warnings about unused variables; the warnings are part of the recorded output.

## Files, statements, axioms and copies

"total" counts every `theorem` in the file. "own" counts the statements whose text, up to comments, does not occur in a file the given file copies from; copies placed in the file's own namespace are also subtracted, and statements restated with changed hypotheses count as own. Copies are placed side by side so that a seam is type-checked in one file; each agrees with its original up to comments, except that in `LargeFieldCoupling`, `PolymerGasFreeEnergy`, `PolymerGasKP`, `UltravioletAssembly` and `UltravioletGlue` the `#print axioms` lines of the copies are collected at the end of the file. Two sources are not part of this bundle: `LocProjectionAType` (copied into `UltravioletAssembly`; 33 statements, sha256 prefix `80161d20f7ff139c`) and `ConnectedSetCounting` (one statement copied into `TwoColorPolymerSum` and its descendants; 14 statements, sha256 prefix `5e36f8ce48757fd6`).

"printed" is the number of `#print axioms` lines; "axioms" splits them into those printing the standard three / a proper subset / no axioms. Statements without a line: four auxiliary lemmas of `PullbackOrbitLimit` (used by the printed statements of that file, whose axiom lists therefore cover them), and the copies of `WeakUltravioletExistence` in `ReflectionSupportScale` (7) and of `UltravioletAssembly` in `SharpWindow` (5), whose originals have lines.

| file | total | own | printed | axioms | copies of |
|---|---|---|---|---|---|
| `ActivityFixedInterval` | 1 | 1 | 1 | 1 / 0 / 0 | — |
| `AnalyticFloor` | 3 | 3 | 3 | 3 / 0 / 0 | — |
| `BackgroundConstants` | 9 | 2 | 9 | 9 / 0 / 0 | CThetaReadings |
| `BlockBoundaryCount` | 36 | 21 | 36 | 36 / 0 / 0 | WeightRecursion |
| `BlockGaussianStep` | 8 | 8 | 8 | 8 / 0 / 0 | — |
| `BoundaryRegulator` | 3 | 3 | 3 | 3 / 0 / 0 | — |
| `BoxConnectivity` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `BoxFiberSiteSum` | 4 | 4 | 4 | 4 / 0 / 0 | — |
| `BoxFromFace` | 100 | 19 | 100 | 99 / 1 / 0 | BoxTwoColorKP |
| `BoxTwoColorKP` | 71 | 20 | 71 | 70 / 1 / 0 | LatticeTwoColorKP |
| `CThetaReadings` | 7 | 7 | 7 | 7 / 0 / 0 | — |
| `ChainEndToEnd` | 66 | 2 | 66 | 66 / 0 / 0 | WeakUltravioletExistence, SmallRemKernel, TwoStageSmallField (each containing UltravioletChain) |
| `ChainEndToEndFineSupport` | 73 | 7 | 73 | 73 / 0 / 0 | ChainEndToEnd |
| `ChainMovingActivity` | 79 | 12 | 79 | 79 / 0 / 0 | ChainEndToEnd; ActivityFixedInterval (one statement) |
| `ClassSiteSum` | 4 | 4 | 4 | 4 / 0 / 0 | — |
| `ClassStepRemainder` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `DifferenceContinuity` | 4 | 1 | 4 | 4 / 0 / 0 | GibbsContinuity (three statements) |
| `EvenDifferenceCoupling` | 8 | 8 | 8 | 8 / 0 / 0 | — |
| `GasExpansion` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `GibbsContinuity` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `HessianGap` | 27 | 16 | 27 | 27 / 0 / 0 | RegularityStep, CThetaReadings |
| `KPToDobrushin` | 2 | 2 | 2 | 2 / 0 / 0 | — |
| `KernelMarginNumbers` | 39 | 6 | 39 | 39 / 0 / 0 | SmallRemKernel, MarginRatioTwo |
| `KernelMarginStages` | 33 | 22 | 33 | 33 / 0 / 0 | MarginRatioTwo |
| `KernelMarginWindow` | 47 | 8 | 47 | 47 / 0 / 0 | SmallRemKernel, MarginRatioTwo, KernelMarginNumbers |
| `KernelWindowTable` | 43 | 10 | 43 | 43 / 0 / 0 | MarginRatioTwo, KernelMarginStages |
| `LargeFieldCoupling` | 17 | 3 | 17 | 17 / 0 / 0 | PolymerGasDobrushin, KPToDobrushin, PolymerGasKP, PolymerGasFreeEnergy |
| `LargeFieldStep` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `LargeFieldSupply` | 6 | 6 | 6 | 6 / 0 / 0 | — |
| `LargeSetRegulator` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `Lattice24KP` | 73 | 20 | 73 | 73 / 0 / 0 | LatticeTwoColorKP |
| `LatticeBlockReflection` | 23 | 23 | 23 | 21 / 0 / 2 | — |
| `LatticeTwoColorKP` | 68 | 41 | 68 | 67 / 1 / 0 | TwoColorEncoding (neighbourhood hypothesis weakened in the restated statements) |
| `MarginNumbers` | 4 | 4 | 4 | 4 / 0 / 0 | — |
| `MarginRatioTwo` | 11 | 11 | 11 | 11 / 0 / 0 | — |
| `MovingActivity` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `NontreeBackground` | 18 | 6 | 18 | 16 / 2 / 0 | ClassStepRemainder, TreeGaugeLocality, RegularityStep |
| `PolymerBlocking` | 2 | 2 | 2 | 2 / 0 / 0 | — |
| `PolymerComponents` | 24 | 20 | 24 | 24 / 0 / 0 | GasExpansion (4 statements copied into its own namespace) |
| `PolymerGasDobrushin` | 8 | 8 | 8 | 8 / 0 / 0 | — |
| `PolymerGasFreeEnergy` | 14 | 3 | 14 | 14 / 0 / 0 | PolymerGasDobrushin, KPToDobrushin, PolymerGasKP |
| `PolymerGasKP` | 11 | 1 | 11 | 11 / 0 / 0 | PolymerGasDobrushin, KPToDobrushin |
| `PolymerGeometry` | 5 | 5 | 5 | 5 / 0 / 0 | — |
| `PolymerMerge` | 3 | 3 | 3 | 3 / 0 / 0 | — |
| `PullbackOrbitLimit` | 9 | 9 | 5 | 5 / 0 / 0 | — |
| `ReflectionSupportScale` | 23 | 16 | 16 | 13 / 2 / 1 | WeakUltravioletExistence (block-variable part) |
| `RegularityConstant` | 24 | 6 | 24 | 22 / 2 / 0 | ClassStepRemainder, TreeGaugeLocality, RegularityStep, NontreeBackground |
| `RegularityRadius` | 55 | 8 | 55 | 53 / 2 / 0 | TwoStageSmallField, ClassStepRemainder, TreeGaugeLocality, RegularityStep, NontreeBackground, RegularityConstant |
| `RegularityStep` | 4 | 4 | 4 | 4 / 0 / 0 | — |
| `SharpWindow` | 15 | 10 | 10 | 10 / 0 / 0 | UltravioletAssembly (section on two-sided orbits) |
| `SizeSplitKP` | 6 | 6 | 6 | 6 / 0 / 0 | — |
| `SmallRemKernel` | 22 | 11 | 22 | 22 / 0 / 0 | UltravioletChain |
| `SupplyLedger` | 44 | 8 | 44 | 44 / 0 / 0 | WeightRecursion, BlockBoundaryCount |
| `TreeGauge` | 5 | 5 | 5 | 0 / 5 / 0 | — |
| `TreeGaugeLocality` | 3 | 3 | 3 | 1 / 2 / 0 | — |
| `TwoColorEncoding` | 37 | 19 | 37 | 37 / 0 / 0 | TwoColorPolymerSum, KPToDobrushin |
| `TwoColorPolymerSum` | 18 | 17 | 18 | 18 / 0 / 0 | ConnectedSetCounting (not in the bundle; one statement) |
| `TwoStageSmallField` | 23 | 12 | 23 | 23 / 0 / 0 | UltravioletChain |
| `UltravioletAssembly` | 58 | 4 | 58 | 58 / 0 / 0 | LocProjectionAType (not in the bundle), ClassStepRemainder, LargeFieldStep, UltravioletChain |
| `UltravioletChain` | 11 | 11 | 11 | 11 / 0 / 0 | — |
| `UltravioletGlue` | 33 | 3 | 33 | 33 / 0 / 0 | WeakUltravioletExistence, UltravioletChain |
| `VertexClassWindow` | 6 | 6 | 6 | 6 / 0 / 0 | — |
| `WeakUltravioletExistence` | 19 | 19 | 19 | 19 / 0 / 0 | — |
| `WeightRecursion` | 15 | 13 | 15 | 15 / 0 / 0 | BoundaryRegulator (2 statements copied into its own namespace) |

## sha256 of the files

| file | sha256 |
|---|---|
| `WeakUvChain/ActivityFixedInterval.lean` | `18112a09cf171869c5294e1fafe544a854c9b37916f861a545645523901b46fb` |
| `WeakUvChain/AnalyticFloor.lean` | `3f065a0cc713e69ab746fc679711070b6835e986b7e641e415c5aa089a698cbd` |
| `WeakUvChain/BackgroundConstants.lean` | `8a6fa543c77ac449ec713cf4010e24c397d91e8d75b8a183a393b691527180cf` |
| `WeakUvChain/BlockBoundaryCount.lean` | `bb66da55acc8db416e23a701806e8a8e35d3f134d7a8507e8f62b7dde2b73191` |
| `WeakUvChain/BlockGaussianStep.lean` | `f81eb3f1d653aaad942a2a1abba6f1ee5ed42c8b677db05955a366b70b3a430d` |
| `WeakUvChain/BoundaryRegulator.lean` | `44cea5bb0a01678ad55234463f5ea08fd3e209bf26b8a6a8ae97ddb2d3ecc397` |
| `WeakUvChain/BoxConnectivity.lean` | `3a9e5cbd63f2135e0f7508dfdc16a8261e19c95fe38dca3c7ea921fb06ab4daa` |
| `WeakUvChain/BoxFiberSiteSum.lean` | `f9bcbb9a347dfb0f677005af7c6190b4e3c7a3b70b59488db7300621405914fd` |
| `WeakUvChain/BoxFromFace.lean` | `fbab4754f910061a4581d78c80dd35f05335e3c82abc0a296e6d027f12016f69` |
| `WeakUvChain/BoxTwoColorKP.lean` | `d523d5d9034312fc9390101698cc379e9a065a8746fabfe615a9416df56764d8` |
| `WeakUvChain/CThetaReadings.lean` | `3dc18a4053a8a23c4d19d99ea98f1e8f968b14bfae6e9dc3d803d370330f085c` |
| `WeakUvChain/ChainEndToEnd.lean` | `898658e1c4fbc8317709c2ca0cdb8854604475f38e93819cc753622d4915ec8d` |
| `WeakUvChain/ChainEndToEndFineSupport.lean` | `1e64010865298444ec85734c12ddfd166da0527692abd443b84505feb1ae9449` |
| `WeakUvChain/ChainMovingActivity.lean` | `85f1c901c05f1586ffc29b9381ea2bf2ce938bd48a661d7be6b99edea2a8946d` |
| `WeakUvChain/ClassSiteSum.lean` | `df14b923dc8c8c844646b6ffbfebb9eb0059f19cbbedfec69537eef512efbf58` |
| `WeakUvChain/ClassStepRemainder.lean` | `76c8f57109913cccf8853b2c30745fdef1a5ced8b2f67068e190088bc49d79af` |
| `WeakUvChain/DifferenceContinuity.lean` | `16fd63d123f2b127081dce6284f09bf87e4894f4e2eeec7916dfb16c475fa518` |
| `WeakUvChain/EvenDifferenceCoupling.lean` | `af6cc713277e7ede0397493262ce6aa24967bdb07660cc2a021c920aa0afd3bc` |
| `WeakUvChain/GasExpansion.lean` | `ee5803a89120223f2600e58e495cf95c78dcbd1e0a6dd1ab15ecf96ab181c434` |
| `WeakUvChain/GibbsContinuity.lean` | `c0d92e8f0c6d7ec3deda3bcc5ba6d4d8da8633f568b73c226e681ebd59f14ea9` |
| `WeakUvChain/HessianGap.lean` | `4b1442cf08396890419fd8837328bc21ae014510d6cdcec28ef9d18e3839d2ad` |
| `WeakUvChain/KPToDobrushin.lean` | `a68e7ef7c11c183f7da9819960be6f319a5392c4adac16d24507f7d62941d203` |
| `WeakUvChain/KernelMarginNumbers.lean` | `4b61d91962bffa2ae1177038d8bd93b5cf9c866d687693668160dda3a30c1395` |
| `WeakUvChain/KernelMarginStages.lean` | `66de450b7680df034ba0d807a8e812b1688aa276c32a215b13fa1c01fe37bd4e` |
| `WeakUvChain/KernelMarginWindow.lean` | `beca2da7853a7be749a5e90b180ecadbf114dd769a32c87c0fe53e161a87e192` |
| `WeakUvChain/KernelWindowTable.lean` | `85e94acbb03dafe9d2659c009d5da5343de7a3d8b9e50e8313d0289bc3c3fde9` |
| `WeakUvChain/LargeFieldCoupling.lean` | `45631c62c50a8c5d7349fe2a033ed3972f897b31c68f2a22e216c67c30427a90` |
| `WeakUvChain/LargeFieldStep.lean` | `bfe753f30bbe16a5e30b5352acdd27a0fda1c43a990bfdbeeebd131aff54f4ae` |
| `WeakUvChain/LargeFieldSupply.lean` | `ea92aca62c2e24ce183daa5618e6cefd653ee92be8ca98efc08480abf3bdb00f` |
| `WeakUvChain/LargeSetRegulator.lean` | `7ae9c8562e366fb7ab996c8eb8d03169696d63bbda6cc3c6eeb871044769e472` |
| `WeakUvChain/Lattice24KP.lean` | `3308006b2b7628513be28ca9673304b67a7f8360ba42422db0c6df37c8b98a52` |
| `WeakUvChain/LatticeBlockReflection.lean` | `88543f8c23004f438e62e9cbed7b6c5412b2fc8893ca78a120c7362db5c48102` |
| `WeakUvChain/LatticeTwoColorKP.lean` | `0f24fff2e02976f50574d54931cef829a1314fc54e2983b7e0931396dd6fa049` |
| `WeakUvChain/MarginNumbers.lean` | `e3a3a63be25fc9fe59365e3316c76b3adf93882dbd4700df0790122f54bceb1e` |
| `WeakUvChain/MarginRatioTwo.lean` | `43940da465d5c7df216f145bf78ab92998196b955761a98eca10be63c2d55ffb` |
| `WeakUvChain/MovingActivity.lean` | `0ab38482c5ca4000a3c7f7006f071932aa8632ab54273f9d6dcf62755a752180` |
| `WeakUvChain/NontreeBackground.lean` | `7c0f3b9d788bc4e80205764d53f0f4e10d1c71c49db5ae86a98e415f366e95c4` |
| `WeakUvChain/PolymerBlocking.lean` | `3c892a01c1e192d7577f55c833eff4a497e5a443a81abfbd59fe2e3d4f621756` |
| `WeakUvChain/PolymerComponents.lean` | `9a9404e5dd6a2137e6ca1f65dc73ed5e80b9e3cadc72ba151723573177cfa502` |
| `WeakUvChain/PolymerGasDobrushin.lean` | `8c86d14c352215bb73c36f758d7c26316869f6a78822d2effd574897ab118bc3` |
| `WeakUvChain/PolymerGasFreeEnergy.lean` | `ef533bd533c3e84f1ed972118b304073afcb16ee5196cafea56c2038470c9b71` |
| `WeakUvChain/PolymerGasKP.lean` | `29cee40c688e025baba99bef9784954fb9467fba1bb9d8d16da2e440ddff77c5` |
| `WeakUvChain/PolymerGeometry.lean` | `8788079fbcc4ccc345d7ab2786e3224fc12f640c06a67dbca23978cd309746bd` |
| `WeakUvChain/PolymerMerge.lean` | `214ad847123a8c7785539fcf546dab9cdb94cdfac06002a046d0281eb92aea4c` |
| `WeakUvChain/PullbackOrbitLimit.lean` | `57df8cb68053ee2ae11549babd55ee1f00f2334d3254833b881f93dad3c0b9a7` |
| `WeakUvChain/ReflectionSupportScale.lean` | `b5185ec712f7c53a55270d43550448ff8388614e1b019b165b736fd01b8d7313` |
| `WeakUvChain/RegularityConstant.lean` | `e1fe7a4c821e0b9fa5b6dcaed3b607029124c4732deb7333496d7ec2e6f92f2a` |
| `WeakUvChain/RegularityRadius.lean` | `cdc3e3d8b04b1b9c464ada344a7478cd34e914d2f9db1575728da4d6f8883a7c` |
| `WeakUvChain/RegularityStep.lean` | `0d6eb7e6a3e7511c14b0f08d30c64c185a8ca53d59c9a7239a5258c17aab5cb0` |
| `WeakUvChain/SharpWindow.lean` | `5f1d78d1dd29274e20c1b7547855a4af353d843829ffe1bc27b35fde827acdea` |
| `WeakUvChain/SizeSplitKP.lean` | `422d8034b0a78aad34fc9c56d0831aaec7d7f7e0acc6dfa7bdc166eda3fac903` |
| `WeakUvChain/SmallRemKernel.lean` | `d66c82a9d1b042b6ba089d8ebb5a4715f78dba90ab676e6ed985bfe793e53e03` |
| `WeakUvChain/SupplyLedger.lean` | `58334ab6b10d088dcd1bd04eba719b2d33a5189e9185e5f96a245f3fdd6fef52` |
| `WeakUvChain/TreeGauge.lean` | `7830edde18759d76e092bc88846036785675faa86220c865fdf5da945fb4ef36` |
| `WeakUvChain/TreeGaugeLocality.lean` | `9b792aba399aa9e01098e5e02a1d9a49678a886d7a85e3194a54973bc908d135` |
| `WeakUvChain/TwoColorEncoding.lean` | `f7a30c5ebbffb4db6ce08acbafc7c1ea83f7174901ed35c500a482f25adb4346` |
| `WeakUvChain/TwoColorPolymerSum.lean` | `9926b5045b8ebfdad3e677328f068924831703ec4281774ebbe87644a6f6b256` |
| `WeakUvChain/TwoStageSmallField.lean` | `45804cdeaf4b3f2cc28b2bd107802390d7068b363ba4107ca5389b2b2f4fa21d` |
| `WeakUvChain/UltravioletAssembly.lean` | `9ded158a87e4071ffa2b696ee57c67ab0199620d70ba2de5632eae9372d2d727` |
| `WeakUvChain/UltravioletChain.lean` | `d35c5262f8d08b45a8fec0377d022aff54cf8ada889cb63e6c5c31f41077e1f2` |
| `WeakUvChain/UltravioletGlue.lean` | `1535128d13025e080a5c49b1d4d3533b85f8db0dc088db7a80865296d89018bb` |
| `WeakUvChain/VertexClassWindow.lean` | `e282c42fe5c769898cc9fd1efcb45cc165608af27df2488206060bce11e3e0a2` |
| `WeakUvChain/WeakUltravioletExistence.lean` | `35cf9b9611cd4dd9575a94fe98f70c43e2d4a7eb28bf7cc8d3caffe391d0132d` |
| `WeakUvChain/WeightRecursion.lean` | `3f7dd5af1ec88366aa6ba927d4fa993787ee9f051a162552b065cc56fd9fd364` |
