# MANIFEST (version 2, 2026-10-17) — files behind Table 1 of version 2 (Proposition 6.4 (b), interval arithmetic)

Programs (interval arithmetic; run with the environment variables of `run905_full.sh`: `IVX_WIDEN=rel IVX_POLY=fast M904_HFAST=1 M905_RB=4`, `OMP_NUM_THREADS=1`):

| file | content |
|---|---|
| `ivx.py` | outward-rounded interval primitives on IEEE doubles (nextafter widening), `exp` by table + Taylor + remainder, `erfcx` by an mpmath-interval table + complete monotonicity + asymptotic series with the DLMF 7.12(i) remainder, sums with the summation bound; `test_ivx.py` is its enclosure test |
| `gen_ivconst.py`, `ivconst.npz`, `gen_erfcx_table.py`, `erfcx_table.npz` | the constants and the erfcx table, generated with mpmath `iv` |
| `m759_psi2.py`, `m813_iv.py`, `m813_iv2.py`, `m813_band.py`, `m813_prod.py`, `m813_y.py` | the certificate inequality (cells of `u`, the influence recursion, the mixed grid, the end geometries) in the hbar-interval form |
| `m904_cert.py` | the interval version of the certificate (one interval of hbar, all geometries) |
| `m904_full.py` | the driver: reads the fixed table of 239 intervals from `table813/P*_out.json` (set `D813` to that directory), runs `m904_cert.one_interval` on every interval not yet in the state file, appends to the output file. Usage: `m904_full.py <state.json> <out.json> <cpu_budget_s> [max_intervals] [order]` |
| `run905_full.sh` | the main process (all intervals, large hbar first); `run_w2.sh`, `run_w3.sh`, `run_w4.sh` the three auxiliary processes on disjoint sets of intervals (small hbar first; `W3_keys.json`, `W4_keys.json` list their intervals); `finish_w4.sh` stops the main process at 228 intervals and merges; `merge_w4.py` merges the four outputs into `FULL_out.json`/`FULL_state.json` |
| `m904_audit.py` | the enclosure audit used for the negative controls |

Inputs: `table813/P1_out.json` ... `table813/P5b_out.json` — the table of 239 intervals of hbar (with c1 and the band of each interval), fixed before the run (produced by the double-precision certificate of version 1 on 2026-10-16; its `rho_up_sup` is the "v1 bound" column of Table 1).

Outputs: `FULL_out.json` (239 records: h1, h2, rho_up_sup, rho_low_sup, cells, cpu, worst geometry), `FULL_state.json` (239 records with settings and finishing times), logs `FULL.log`, `W2.log`, `W3.log`, `W4.log`, specs `spec_p5a.txt`, `spec_p5b.txt`. Started 2026-10-16 13:30:55, finished 2026-10-17 15:20:39 (JST), 119066 s of CPU in total. Every record carries the same settings. Checks on the merged output (performed independently): 239 distinct intervals equal to the table, cover [1e-5, 1] with no gap, max rho_up_sup = 0.199666 < 0.5, rho_up_sup >= rho_low_sup on every interval.

Note: after the run, the absolute paths of the local directories in the programs and shell scripts were replaced by relative paths (`.` and `./table813`) and one local `sys.path` line was neutralised; nothing else was changed. The hashes in `../SHA256SUMS` are of the distributed files.
