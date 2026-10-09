import Lake
open Lake DSL

/-- `padicregulatorvaluation` — the arithmetic layer of the valuation of the
    p-adic regulator at anomalous primes, and the companion note on the
    anomalous Euler factor. 31 modules, each depending on `import Mathlib` only.
    Builds with Lean 4 v4.33.1 and the Mathlib revision below. -/
package padicregulatorvaluation where
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
-- The modules are independent of one another, and some of them restate a
-- lemma under the same name (so that each file checks on its own); the root
-- module therefore imports none of them, and the glob builds every module
-- under `PadicRegulatorValuation` separately.
lean_lib PadicRegulatorValuation where
  globs := #[.andSubmodules `PadicRegulatorValuation]
