# 証明書（psiP と同じ不等式）を、ファイルに並べた (r, b_lo, b_hi) の細胞で回す。結論文は印字しない。
# 使い方：cellsF.py c1 h out.json specfile（各行 "r b_lo b_hi"、b_lo = inf は b → −∞ の固定の極限）
import sys, os, json, math, time, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from psiP import make_cells, backward, forward, vprime_range, EPS, XC
if __name__ == '__main__':
    c1, h, out, sf = float(sys.argv[1]), float(sys.argv[2]), sys.argv[3], sys.argv[4]
    t0 = time.process_time()
    t = make_cells(h, -XC, 0.0, c1, c2=20.0); n = len(t)-1; lam = 1.0/(EPS*h); chunk = max(8, int(4e5//n))
    P = {'lam0': lam, 'dl': (0.0, 0.0), 'lamr': (lam, lam), 'vr': vprime_range(t)}
    res = []
    for line in open(sf):
        if not line.strip(): continue
        r, bl, bh = line.split(); r = int(r); bl = None if bl == 'inf' else float(bl); bh = float(bh)
        if bh == -0.89: bh = -XC
        sites = backward(t, P, 8 + r, bl, bh, chunk); Fu, Fl = forward(t, P, sites, 8, chunk)
        res.append({'r': r, 'blo': bl, 'bhi': bh, 'rho_up': float(Fu.max()), 'rho_low': float(Fl.max()), 'n': n})
        json.dump(res, open(out, 'w'))
        print(f"cell h={h} c1={c1} n={n} r={r} b=[{bl},{bh}]: rho_up={Fu.max():.6g} rho_low={Fl.max():.6g} cpu={time.process_time()-t0:.1f}s", flush=True)
