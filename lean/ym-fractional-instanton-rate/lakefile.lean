import Lake
open Lake DSL

/-- `fractionalinstanton` — the Lean development cited by the paper on the area-law rate on a twisted small torus.
    1 module, each depending on Mathlib only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package fractionalinstanton where
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
-- glob builds every module under `FractionalInstanton` separately.
lean_lib FractionalInstanton where
  globs := #[.andSubmodules `FractionalInstanton]
