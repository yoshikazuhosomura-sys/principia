# Bundle of "An interval-arithmetic chain for the Migdal--Kadanoff flow of SU(2) plaquette weights" (version 2)

Everything needed to check the paper is in this directory; `SHA256SUMS` lists every file.

| path | content |
|---|---|
| `lean/` | Lean 4 archive of the five modules (`principia-ym-hierarchical-chain-2026-10-15.tar.gz`, unchanged from version 1, with its `.sha256`) and the complete `#print axioms` output |
| `certificates/` | interval certificates of Theorems 3.1 and 5.4 and Proposition 4.5 (CSV, one row per cell) with `SHA256SUMS` |
| `whalf/programs/` | programs of Proposition 5.2 (W-half(T)): `mk_tail_cert.py` (enclosure of the untruncated map, Lemma A.2, and the lower bound for kappa, Lemma A.3), `tube_cap4.py` (reference curve, Definition 5.1(a)), `envelope.py` (Lemma A.4), `tube_lift.py` (cell test, part (i)), `tube_be_lift.py` (part (ii)), `lift_cover.py` (coverage), `tube_lift_strong.py` (cell test with the decrease test against the lower end of the cell), `drop_check.py` (decrease of the cell index, one box per cell) |
| `whalf/logs/` | original output of the certificate: one line per cell (restarts included), `coverage_check.txt` and `belift.txt` (part (ii)); `cover_all.out` is the output of `../cover_all.py` on these logs |
| `whalf/rerun/` | output of the computations added for version 2: `drop_check.txt`, `strong_0.0144_0.06.txt`, `strong_0.06_0.11.txt`, `kappa_rerun.txt` |
| `whalf/curve/` | the reference curve recomputed for the joining computation (`gamma_S.txt`, `gamma_P.txt`, written by `recompute_gamma.py`) and its comparison with the curve of the certificate (`compare_gamma.py`, `compare_gamma.out`) |
| `whalf/run.sh` | runs the programs (they read each other from their own directory `whalf/programs/`; `lift_cover.py` reads `whalf/logs/`) |

Requirements for `whalf/`: Python 3 with mpmath, NumPy and SciPy (version 2 used mpmath 1.3.0, NumPy 2.5.2, SciPy 1.18.0).

Examples:

    bash whalf/run.sh lift   0.0144 0.06 0.005    # part (i), first range of the logs
    bash whalf/run.sh strong 0.0144 0.06 0.005    # the same with the decrease test against the cell
    bash whalf/run.sh drop   0.198  0.21 0.0025   # decrease of the cell index
    bash whalf/run.sh kappa  0.01658              # part (ii)
    bash whalf/run.sh cover                       # coverage of [0.0144, 0.198) (lift_cover.py)
    python3 whalf/cover_all.py whalf/logs         # coverage of [0.0144, 0.21) by the logged cells

The ranges of the original logs (including the restarts) are: [0.0144,0.06], [0.06,0.11], [0.11,0.163], [0.14836,0.163], [0.163,0.18], [0.16711,0.18], [0.18,0.198], [0.18639,0.198] with relative cell width 0.005, and [0.198,0.21], [0.20452,0.21] with 0.0025.

Lean: unpack the archive in `lean/`, run `lake exe cache get`, then `LEAN_NUM_THREADS=1 lake build` with the module names; the `#print axioms` lines at the end of each module should agree with the axiom log.
