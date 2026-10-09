import Lake
open Lake DSL

/-- `euclideanpath` — algebraic skeleton of the gap/Poincaré lower bound.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package euclideanpath where
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
lean_lib EuclideanPath where
  globs := #[.andSubmodules `EuclideanPath]
