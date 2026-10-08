import Lake
open Lake DSL

/-- `principia` — 機械検証済みの数学の束。
    Lean 4 v4.33.1 ＋ Mathlib（下のリビジョン）で建つ。 -/
package principia where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩
  ]

-- `lake-manifest.json` と同じリビジョン（タグ `v4.33.1` の指す commit）。
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
-- 入口 `Principia.lean` が import しない本（同名の宣言を持つため）も建てるよう、
-- `Principia` の下の全モジュールを対象にする。
lean_lib Principia where
  globs := #[.andSubmodules `Principia]
