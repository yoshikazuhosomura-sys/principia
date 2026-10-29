/-
  `H1bMarginInterval` — root module of the bundle.

  The modules under `H1bMarginInterval/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `H1bMarginInterval.LatticeGaugeH1HbarInterval` (elementary inequalities of the hbar-interval step and the six final subtractions, 15 theorems)
-/
