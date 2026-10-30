/-
  `TwoColourPolymer` — root module of the bundle.

  The modules under `TwoColourPolymer/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `TwoColourPolymer.BoxConnectivity`
  * `TwoColourPolymer.BoxFromFace`
  * `TwoColourPolymer.BoxGasFromFaceSum`
  * `TwoColourPolymer.BoxTwoColorKP`
  * `TwoColourPolymer.ClassSiteSum`
  * `TwoColourPolymer.ConnectedSetCounting`
  * `TwoColourPolymer.KPToDobrushin`
  * `TwoColourPolymer.Lattice24KP`
  * `TwoColourPolymer.LatticeTwoColorKP`
  * `TwoColourPolymer.PolymerGasDobrushin`
  * `TwoColourPolymer.SizeSplitKP`
  * `TwoColourPolymer.TwoColorEncoding`
  * `TwoColourPolymer.TwoColorPolymerSum`
-/
