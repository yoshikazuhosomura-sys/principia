import Lake
open Lake DSL

/-- `h1bmargininterval` — the Lean development cited by the paper "An interval-arithmetic certificate for the (T1) margin of the one-dimensional double well".
    1 module, depending on Mathlib only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package h1bmargininterval where
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
-- glob builds every module under `H1bMarginInterval` separately.
lean_lib H1bMarginInterval where
  globs := #[.andSubmodules `H1bMarginInterval]
