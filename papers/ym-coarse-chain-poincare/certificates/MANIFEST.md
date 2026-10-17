# MANIFEST — files behind Table 1 of version 1 (Proposition 6.4 (b), double precision with outward margins). Version 2 (2026-10-17): the interval-arithmetic certificate is in `interval/` (see `interval/MANIFEST-interval.md`) and Proposition PIN in `pin/`.

Programs: `psi2.py` (inequality, point version) -> `psiP.py` (same inequality, hbar-interval form; with h1 = h2 it is the point version) -> `cellsF.py` (runs `psiP` on the cells listed in a spec file). Audit of rounding by a separate route: `audit3.py` (needs mpmath), output `audit3.log`.

| Table 1 rows | file | content |
|---|---|---|
| hbar = 1, 0.5, 0.3, 0.2, 0.15 | `p1.json` | all geometries, c1 = 0.02 |
| hbar = 0.1, 0.07, 0.05, 0.04, 0.035, 0.03 | `p2a.json` | c1 = 0.015 |
| hbar = 0.025, 0.02, 0.015, 0.01 | `p2b.json` | c1 = 0.015 |
| hbar = 0.007, 0.005, 0.003, 0.002, 0.001 | `p3.json` | c1 = 0.04 |
| hbar = 3e-4 | `p4.json` | c1 = 0.08 |
| hbar = 1e-4 | `p5.json` | c1 = 0.09 |
| hbar = 1e-5, interior (2047 cells) | `p6.json` | c1 = 0.2 |
| hbar = 1e-5, ends (1654 cells) | `e5A.json` (r = 0, spec `specA.txt`), `e5BD.json` (r = 0 and r = 2, spec `specBD.txt`), `e5C.json` (r = 1, 3..7, spec `specC.txt`) | end cells of b = beta |

In `e5C.json` the r = 2 entries are not used; the r = 2 end of Table 1 is taken from the r = 2 entries of `e5BD.json`.

Controls of the paragraph "Controls": `c_pos.json` (division every fourth site), `c_neg2.json` (Gaussian chain, V = 0, enclosure [0.061, 3.63]), `c_neg.json` (an earlier control on coarser cells, not quoted). Auxiliary runs at the same points, not used for Table 1: `j5.json`, `j6a.json` (same values as `p6.json`).

Not adopted (kept for the record, not used anywhere in the paper): `not-adopted/j4a.json`, `not-adopted/j6b.json`, `not-adopted/j6c.json`, `not-adopted/j6d.json` (trial runs).
