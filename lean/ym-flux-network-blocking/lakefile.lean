import Lake
open Lake DSL

/-- `fluxnetwork` — the Lean development cited by the note on tree-level blocking as a flux network.
    12 modules, each depending on Mathlib only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package fluxnetwork where
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
-- glob builds every module under `FluxNetwork` separately.
lean_lib FluxNetwork where
  globs := #[.andSubmodules `FluxNetwork]
