import Lake
open Lake DSL

/-- `boundarymixedderivative` — the Lean development cited by the paper "A boundary observable separating U(1) and SU(2) lattice gauge theory".
    1 module, depending on Mathlib only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package boundarymixedderivative where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩
  ]

-- Same revision as `lake-manifest.json` (the commit of the tag `v4.33.1`).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

@[default_target]
-- Each module checks on its own; the root module imports none of them, and the
-- glob builds every module under `BoundaryMixedDerivative` separately.
lean_lib BoundaryMixedDerivative where
  globs := #[.andSubmodules `BoundaryMixedDerivative]
