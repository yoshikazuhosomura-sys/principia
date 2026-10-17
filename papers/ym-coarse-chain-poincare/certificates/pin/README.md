# Proposition PIN (version 2, 2026-10-17) — hbar <= 1e-5

`PROP-PIN.md`: the complete argument (in Japanese; the paper's §PIN is its summary). `pin3.py`: the floating-point table of the classical force D(u) (891 grid points, a reading). `pinI.py`: the interval-arithmetic lower bound D_0 = 0.023126 on [-x_c, -0.8] via the supersolution lemma (mpmath intervals, 80 bits). `pin2.py`: the same minimum over the end geometries. The exact rational constants (det H_0^(7) > 0, det H_0^(8) < 0, h_11, h_17, L_g) and the final inequality are in the Lean module `LatticeGauge.PinnedCoarseChain`.
