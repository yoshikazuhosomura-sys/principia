# lean/ym-h1b-margin-interval

The Lean 4 development cited by the paper "An interval-arithmetic certificate for the (T1) margin of the one-dimensional double well for ħ ∈ [0.00195, 0.005]" (Yoshikazu Hosomura, with the assistance of Claude; 2026-10-29), kept under `papers/ym-h1b-margin-interval` in this repository. Sections 7 and 9 of the paper match its statements with the declarations below.

## Contents
- `H1bMarginInterval/LatticeGaugeH1HbarInterval.lean` — namespace `LatticeGauge.H1HbarInterval`, 15 theorems (`cell_lower`, `cell_upper`, `sum_lower`, `sum_upper`, `rho_lower`, `pieces_min`, `margin_on_interval`, `margin_I1` … `margin_I6`, `threshold`, `margin_I1_coarse_fails`). Byte-identical to the file of the web bundle `principia-ym-h1b-margin-interval-2026-10-29.tar.gz`; sha256 `4231182160d4e4721de2aa299f819e24634121d7b2293e4cf0fb0b2ac5561530`.
- `H1bMarginInterval.lean` — root module; imports nothing (the module imports Mathlib only and checks on its own).
- `axioms.txt` — `#print axioms` output, one line per theorem.

## How to check
Lean 4 `v4.33.1`, Mathlib `v4.33.1` (commit `0df444a3`, pinned in `lake-manifest.json`).

    lake exe cache get
    LEAN_NUM_THREADS=1 lake env lean H1bMarginInterval/LatticeGaugeH1HbarInterval.lean

The fifteen `#print axioms` lines at the end of the file must each print `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `axiom`, no `native_decide`.

## What lies outside Lean
Checked: the elementary inequalities of the ħ-interval step (Lemma 3.1), the threshold arithmetic, the six final subtractions r_k − 2k_k ≥ 0.067 (each a `norm_num` check of the literal numbers of Table 1 of the paper, which does not certify those numbers), and the negative control on I₁. Not checked: the interval outputs r_k, k_k (they enter as hypotheses), the transfer-operator integrals, the Muckenhoupt and FKG inputs, the tail lemma, Lemmas TI, EM, TF and K2, and the floating-point premise (float64 with outward widths, correct IEEE rounding).
