# lean/ym-boundary-mixed-derivative

The Lean 4 development cited by the paper "A boundary observable separating U(1) and SU(2) lattice gauge theory: one loop, a strong-coupling sign and Monte Carlo" (Yoshikazu Hosomura, with the assistance of Claude; 2026-10-29), kept under `papers/ym-boundary-mixed-derivative` in this repository. Section 6 and the correspondence table of the paper match its statements with the declarations below.

## Contents
- `BoundaryMixedDerivative/StrongCouplingOneSidedTerm.lean` — namespace `StrongCouplingOneSided`, 9 theorems (`four_mul_le_sq`, `area_le_strip`, `strip_term_eq`, `strip_coeff_lower`, `tube_coeff_neg`, `tube_part_nonpos`, `h_main_term`, `h_neg`, `h_neg_on_interval`). Byte-identical to the file of the web bundle `principia-ym-boundary-mixed-derivative-2026-10-29.tar.gz`; sha256 `1fd998eea20a83e74212a2ccd61c124d8ff125ffe0f9f6e1f58a2136db4bafb2`.
- `BoundaryMixedDerivative.lean` — root module; imports nothing (the module imports Mathlib only and checks on its own).
- `axioms.txt` — `#print axioms` output, one line per theorem.

## How to check
Lean 4 `v4.33.1`, Mathlib `v4.33.1` (commit `0df444a3`, pinned in `lake-manifest.json`).

    lake exe cache get
    LEAN_NUM_THREADS=1 lake env lean BoundaryMixedDerivative/StrongCouplingOneSidedTerm.lean

The nine `#print axioms` lines at the end of the file must each print `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `axiom`, no `native_decide`.

## What lies outside Lean
Only the arithmetic and inequality steps of the strong-coupling sign (Proposition 4.1 of the paper) are checked. The Lean statements are about abstract real numbers; that their hypotheses hold for lattice gauge theory — the strong-coupling expansion, its hand-derived coefficients and the remainder bound (H), which is assumed — is not checked. The one-loop and Monte Carlo results are floating-point computations outside Lean.
