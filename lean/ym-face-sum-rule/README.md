# lean/ym-face-sum-rule

The Lean 4 development cited by the paper "A one-plaquette Schwinger–Dyson identity and a multi-level sum rule for the coarse stiffness in SU(2) lattice gauge theory, with machine-checked arithmetic" (Yoshikazu Hosomura, with the assistance of Claude; 2026-10-30), kept under `papers/ym-face-sum-rule` in this repository. The correspondence table of the paper matches its statements with the declarations below.

## Contents
- `FaceSum/<File>.lean` — 6 modules, each beginning with `import Mathlib` and checking on its own (no module imports another). Byte-identical to the files of the web bundle `principia-ym-face-sum-rule-2026-10-30.tar.gz` (sha256 of the archive `f7839e8d56d28c6209dc3ac2e28c2d887f085c1abf62cddc0312dc8a772519a9`); the sha256 of each file is listed below.
- `FaceSum.lean` — root module; imports nothing.
- `axioms.txt` — the bundle's `axioms-<File>.txt` for every file, concatenated: the full output of `lake env lean <File>.lean`, 64 `#print axioms` lines in total.
- `lakefile.lean`, `lean-toolchain`, `lake-manifest.json` — the lake project, pinned to Lean 4 `v4.33.1` and Mathlib `v4.33.1` (commit `0df444a3`).

No `sorry`, no `axiom` declaration, no `native_decide`. Every `#print axioms` line prints `[propext, Classical.choice, Quot.sound]` or a subset of it (in files that `open Classical`, Lean prints `Classical.choice` as `choice`), or that the statement depends on no axioms.

## Main statements

| statement of the paper | file | declaration |
|---|---|---|
| Lemma 3.3 (exact split of the coarse stiffness) | `CoarseFaceStiffness.lean` | `CoarseStiffness.decomposition`, `h_from_angle`, `h_nonneg`, `h_le_inv` |
| Lemma 3.4 (band bound) | `CoarseFaceStiffness.lean` | `CoarseStiffness.gamma_lower`, `gamma_lower_direct` |
| Theorem 4.1 (sum rule) | `FaceCorrelationSumRule.lean` | `FaceSumRule.sum_rule`, `sum_rule_split`, `normalized` |
| Proposition 4.2 (free field, every level; matrix steps) | `CoarseFaceStiffness.lean` | `CoarseStiffness.transpose_fix`, `free_force_pairing`, `free_ratio`, `four_dim_ratio` |
| Proposition 5.1 (moments determine the stiffness) | `FaceMomentStiffness.lean` | `FaceMoment.inverse`, `forward`, `kurtosis`, `cosine_only` |
| the constant `w₂` (interval) | `StiffnessLevelConstants.lean` | `LevelConstants.w2_value`, `w2_gap` |
| Table 1 (constants and thresholds) | `StiffnessLevelConstants.lean` | `LevelConstants.fine_constants`, `coarse_constants`, `thresholds` |

`CoarseStiffnessFirstOrder.lean` is an earlier bookkeeping of the same bound and is not used by the paper.

## How to check
Lean 4 `v4.33.1`, Mathlib `v4.33.1` (commit `0df444a3`, pinned in `lake-manifest.json`).

    lake exe cache get
    LEAN_NUM_THREADS=1 lake env lean FaceSum/<File>.lean

for each file, and compare the output with the section of `axioms.txt` for that file. `lake build` builds every module through the glob in `lakefile.lean`, one module at a time with `LEAN_NUM_THREADS=1`.

## What lies outside Lean
Lean checks the algebra and the arithmetic named in the paper. It does not check the integration by parts, Gaussian conditioning, the first-order expansion, the lattice integrals, the momentum sums or the Monte Carlo numbers; literal constants in the files (such as `1.1733`) are hypotheses about computed values, not certificates of them. `CoarseStiffnessFirstOrder.lean` is an earlier bookkeeping of the same bound and is not used by the paper.

## Files, statements and axioms

"printed" is the number of `#print axioms` lines; "axioms" splits them into those printing the standard three / a proper subset / no axioms.

| file | `theorem` declarations | printed | axioms (standard three / proper subset / none) | sha256 (first 16) |
|---|---|---|---|---|
| `FaceCorrelationSumRule` | 8 | 8 | 8 / 0 / 0 | `92fd028a48f97546` |
| `CoarseFaceStiffness` | 18 | 18 | 17 / 1 / 0 | `0a1735ff878b97c7` |
| `CoarseStiffnessFirstOrder` | 7 | 7 | 7 / 0 / 0 | `414e41000bb06d5c` |
| `FaceMomentStiffness` | 12 | 12 | 12 / 0 / 0 | `b36ec7e9b254ead0` |
| `StiffnessLevelConstants` | 11 | 11 | 11 / 0 / 0 | `7f9ce64a6189ae4f` |
| `SpectralFaceMoment` | 8 | 8 | 8 / 0 / 0 | `0041bf5e176a7797` |

## sha256 of the files

| file | sha256 |
|---|---|
| `FaceSum/CoarseFaceStiffness.lean` | `0a1735ff878b97c7979cb274e6b1f278f5c687b4fe31d343a39b88f12e80f159` |
| `FaceSum/CoarseStiffnessFirstOrder.lean` | `414e41000bb06d5ca920ad877357b1a42e76bf3e8d57bfc366f37b6d03a95393` |
| `FaceSum/FaceCorrelationSumRule.lean` | `92fd028a48f9754601edeed57c025504d0cc046559315acd91df98001324ef6d` |
| `FaceSum/FaceMomentStiffness.lean` | `b36ec7e9b254ead011725560a79b50a30754294a2e563fb260b85d4341159689` |
| `FaceSum/SpectralFaceMoment.lean` | `0041bf5e176a77979db9edcf49750d729c9ccdc1a5017151aea6d75d564a2195` |
| `FaceSum/StiffnessLevelConstants.lean` | `7f9ce64a6189ae4f77f0adefff3504670689b02a385c2af6af23d9d508e11d19` |
