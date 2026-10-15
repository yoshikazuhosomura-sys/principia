import Lake
open Lake DSL

/-- `hierarchicalchain` — the Lean development cited by the note on the hierarchical-model chain.
    5 modules, each depending on Mathlib only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package hierarchicalchain where
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
-- glob builds every module under `HierarchicalChain` separately.
lean_lib HierarchicalChain where
  globs := #[.andSubmodules `HierarchicalChain]
