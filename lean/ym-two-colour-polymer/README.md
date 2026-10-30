# lean/ym-two-colour-polymer

The Lean 4 development cited by the paper "A machine-checked two-colour polymer gas on ℤ⁴: encoding, adjacency degrees, the box stage, and the Kotecký–Preiss condition down to Dobrushin" (Yoshikazu Hosomura, with the assistance of Claude; 2026-10-30), kept under `papers/ym-two-colour-polymer` in this repository. The correspondence table of the paper matches its statements with the declarations below.

## Contents
- `TwoColourPolymer/<File>.lean` — 13 modules, each beginning with `import Mathlib` and checking on its own (no module imports another). Byte-identical to the files of the web bundle `principia-ym-two-colour-polymer-2026-10-30.tar.gz` (sha256 of the archive `d38990299a293d9a728cbdf0d709775448223d5e9708966519394b64617541e8`); the sha256 of each file is listed below.
- `TwoColourPolymer.lean` — root module; imports nothing.
- `axioms.txt` — the bundle's `axioms-<File>.txt` for every file, concatenated: the full output of `lake env lean <File>.lean`, 518 `#print axioms` lines in total.
- `lakefile.lean`, `lean-toolchain`, `lake-manifest.json` — the lake project, pinned to Lean 4 `v4.33.1` and Mathlib `v4.33.1` (commit `0df444a3`).

No `sorry`, no `axiom` declaration, no `native_decide`. Every `#print axioms` line prints `[propext, Classical.choice, Quot.sound]` or a subset of it (in files that `open Classical`, Lean prints `Classical.choice` as `choice`), or that the statement depends on no axioms.

## Main statements

| statement of the paper | file | declaration |
|---|---|---|
| Lemma 4.1 (encoding) | `LatticeTwoColorKP.lean` | `LatticeTwoColorKP.enc_connected`, `decode`, `enc_eq`, `card_le_enc`, `label_sum_le` |
| Proposition 4.2 (encoded sum) | `LatticeTwoColorKP.lean` | `LatticeTwoColorKP.encoded_sum_le` |
| Theorem 5.1 (plaquette stage on ℤ⁴) | `LatticeTwoColorKP.lean` | `LatticeTwoColorKP.lattice_kp_site`, `lattice_dobrushin` |
| Theorem 6.1 (box sum = plaquette-cluster sum) | `BoxFromFace.lean` | `BoxFromFace.box_hsite_eq_face_sum`, `box_hsite_of_face_sum` |
| Theorem 6.2 (bridge) | `BoxFromFace.lean` | `BoxFromFace.box_event_bridge` |
| Theorem 7.1 (KP ⇒ Dobrushin) | `KPToDobrushin.lean` | `KPToDobrushin.dobrushin_cond_of_kp` |
| Theorem 7.2 (partition function) | `PolymerGasDobrushin.lean` | `PolymerGasDobrushin.dobrushin`, `Z_ge_exp`, `log_Z_ge` |
| Theorem 7.3 ((H-sum) ⇒ Dobrushin and Z for the box gas, composed) | `BoxGasFromFaceSum.lean` | `BoxGasFromFaceSum.box_dobrushin_of_face_sum`, `box_gas_partition_of_face_sum` |

## How to check
Lean 4 `v4.33.1`, Mathlib `v4.33.1` (commit `0df444a3`, pinned in `lake-manifest.json`).

    lake exe cache get
    LEAN_NUM_THREADS=1 lake env lean TwoColourPolymer/<File>.lean

for each file, and compare the output with the section of `axioms.txt` for that file. `lake build` builds every module through the glob in `lakefile.lean`, one module at a time with `LEAN_NUM_THREADS=1`.

## What lies outside Lean
The activities of a gauge model are not treated: every bound on activities is a hypothesis of the theorems, either in product form or in the summed form (H-sum). Numerical constants in hypotheses are thresholds of sufficient conditions, not estimates of any activity. Finite counts on ℤ⁴ (`LatticeTwoColorKP`, `BoxTwoColorKP`, `Lattice24KP`, `BoxFromFace`, `BoxGasFromFaceSum`) are closed by `decide +kernel` inside Lean.

## Files, statements, axioms and copies

Copies are placed side by side so that each file is checked on its own; each copy agrees with its original. `TwoColorPolymerSum` §1 copies `ConnectedSetCounting`; `TwoColorEncoding` §§1–6 copy `TwoColorPolymerSum` and §10 copies `KPToDobrushin`; `LatticeTwoColorKP` §§1–10 copy `TwoColorEncoding` with the neighbourhood hypothesis weakened to `p ≠ q`; `BoxTwoColorKP` and `Lattice24KP` §§1–11 copy `LatticeTwoColorKP`; `BoxFromFace` §§1–12 copy `BoxTwoColorKP`; `BoxGasFromFaceSum` contains `BoxFromFace` and `PolymerGasDobrushin` whole, followed by four new statements. The paper's Table 1 counts copies and new statements per file (518 declarations, 163 distinct statements). `BoxConnectivity` is not used by the paper. The two `@[simp]` lemmas `tF_apply`, `tL_apply` (proved by `rfl`) have no `#print axioms` line and are counted below but not in the paper.

"printed" is the number of `#print axioms` lines; "axioms" splits them into those printing the standard three / a proper subset / no axioms.

| file | `theorem` declarations | printed | axioms (standard three / proper subset / none) | sha256 (first 16) |
|---|---|---|---|---|
| `ConnectedSetCounting` | 14 | 14 | 14 / 0 / 0 | `4fe5400c5133fe97` |
| `TwoColorPolymerSum` | 18 | 18 | 18 / 0 / 0 | `9926b5045b8ebfda` |
| `KPToDobrushin` | 2 | 2 | 2 / 0 / 0 | `a68e7ef7c11c183f` |
| `TwoColorEncoding` | 37 | 37 | 37 / 0 / 0 | `f7a30c5ebbffb4db` |
| `LatticeTwoColorKP` | 70 | 68 | 67 / 1 / 0 | `0f24fff2e02976f5` |
| `BoxTwoColorKP` | 73 | 71 | 70 / 1 / 0 | `d523d5d9034312fc` |
| `Lattice24KP` | 75 | 73 | 73 / 0 / 0 | `3308006b2b762851` |
| `BoxFromFace` | 102 | 100 | 99 / 1 / 0 | `fbab4754f910061a` |
| `PolymerGasDobrushin` | 8 | 8 | 8 / 0 / 0 | `8c86d14c352215bb` |
| `ClassSiteSum` | 4 | 4 | 4 / 0 / 0 | `df14b923dc8c8c84` |
| `SizeSplitKP` | 6 | 6 | 6 / 0 / 0 | `422d8034b0a78aad` |
| `BoxConnectivity` | 5 | 5 | 5 / 0 / 0 | `3a9e5cbd63f2135e` |
| `BoxGasFromFaceSum` | 114 | 112 | 111 / 1 / 0 | `f659c624ac9f43d2` |

## sha256 of the files

| file | sha256 |
|---|---|
| `TwoColourPolymer/BoxConnectivity.lean` | `3a9e5cbd63f2135e0f7508dfdc16a8261e19c95fe38dca3c7ea921fb06ab4daa` |
| `TwoColourPolymer/BoxFromFace.lean` | `fbab4754f910061a4581d78c80dd35f05335e3c82abc0a296e6d027f12016f69` |
| `TwoColourPolymer/BoxGasFromFaceSum.lean` | `f659c624ac9f43d2a5a2a5e4e751cb6399a10c3496781dcaf2258f78fbb12b3c` |
| `TwoColourPolymer/BoxTwoColorKP.lean` | `d523d5d9034312fc9390101698cc379e9a065a8746fabfe615a9416df56764d8` |
| `TwoColourPolymer/ClassSiteSum.lean` | `df14b923dc8c8c844646b6ffbfebb9eb0059f19cbbedfec69537eef512efbf58` |
| `TwoColourPolymer/ConnectedSetCounting.lean` | `4fe5400c5133fe9723297937321e526f49add7d6d36321b4ea28bde6ff17f6e0` |
| `TwoColourPolymer/KPToDobrushin.lean` | `a68e7ef7c11c183f7da9819960be6f319a5392c4adac16d24507f7d62941d203` |
| `TwoColourPolymer/Lattice24KP.lean` | `3308006b2b7628513be28ca9673304b67a7f8360ba42422db0c6df37c8b98a52` |
| `TwoColourPolymer/LatticeTwoColorKP.lean` | `0f24fff2e02976f50574d54931cef829a1314fc54e2983b7e0931396dd6fa049` |
| `TwoColourPolymer/PolymerGasDobrushin.lean` | `8c86d14c352215bb73c36f758d7c26316869f6a78822d2effd574897ab118bc3` |
| `TwoColourPolymer/SizeSplitKP.lean` | `422d8034b0a78aad34fc9c56d0831aaec7d7f7e0acc6dfa7bdc166eda3fac903` |
| `TwoColourPolymer/TwoColorEncoding.lean` | `f7a30c5ebbffb4db6ce08acbafc7c1ea83f7174901ed35c500a482f25adb4346` |
| `TwoColourPolymer/TwoColorPolymerSum.lean` | `9926b5045b8ebfdad3e677328f068924831703ec4281774ebbe87644a6f6b256` |
