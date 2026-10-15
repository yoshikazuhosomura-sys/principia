import Lake
open Lake DSL

/-- `onelink` — the Lean development cited by the note "One-link integration
    before Bakry–Émery for SU(2) lattice Yang–Mills": the one-link chain
    (star inequality, quaternionic bridge, series, geometry of I*, perturbation
    of staples, one-link integral) and the complete families of k-cells.
    Seven modules, each depending on `import Mathlib` only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package onelink where
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
-- The modules are independent of one another, and five of them use the
-- namespace `PerfectFamily` and restate definitions and lemmas under the same
-- names (so that each file checks on its own); the root module therefore
-- imports none of them, and the glob builds every module under `OneLink`
-- separately.
lean_lib OneLink where
  globs := #[.andSubmodules `OneLink]
