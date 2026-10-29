/-
  `BoundaryMixedDerivative` — root module of the bundle.

  The modules under `BoundaryMixedDerivative/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `BoundaryMixedDerivative.StrongCouplingOneSidedTerm` (strong-coupling sign of h: arithmetic and inequalities, 9 theorems)
-/
