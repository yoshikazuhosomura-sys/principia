import Lake
open Lake DSL

/-- `twocolourpolymer` — the Lean development cited by the paper "A machine-checked two-colour polymer gas on Z^4: encoding, adjacency degrees, the box stage, and the Kotecký–Preiss condition down to Dobrushin".
    13 modules, each depending on Mathlib only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package twocolourpolymer where
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
-- glob builds every module under `TwoColourPolymer` separately.
lean_lib TwoColourPolymer where
  globs := #[.andSubmodules `TwoColourPolymer]
