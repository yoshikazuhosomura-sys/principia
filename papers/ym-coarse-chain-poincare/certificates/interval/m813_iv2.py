# 第813便・判定の本体（m813_iv の部品を使う）。b の細胞は TP2（第759便 補題 M (b)）で端の二本の鎖に分ける：
#   鎖(b_lo) の下の法則 ≤ P^{(b_lo)} ≤ P^{(b)} ≤ P^{(b_hi)} ≤ 鎖(b_hi) の上の法則（尤度比、各 λ で）。
# 各鎖は b を一点に固定し、λ ∈ [λ2,λ1] についてだけ挟む（中心形の角に M の両端が要るので、区間の版では各鎖で上下の両方を回す）。
# b_lo = None は b → −∞ の固定の極限（z_N = lo）。結論文は印字しない。
import sys, os, json, time, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m813_iv import Site, law_rows, cdf_mean, forward as _fw, make_cells, vprime_range, k_bounds, EPS, XC, U
from m813_y import forward_y
def chain(t, P, N, b, chunk, need_up, need_lo):
    n = len(t)-1; sites = [None]*N
    if b is None: sites[N-1] = Site(np.full(n, t[0]), np.full(n, t[0]), True)
    else: sites[N-1] = Site(np.full(n, b), np.full(n, b), False)
    for i in range(N-1, 0, -1):
        nx = sites[i]; mlo = np.full(n+1, np.nan); mup = np.full(n+1, np.nan)
        if nx.lo_delta: mlo[:] = t[0]; mup[:] = t[0]
        else:
            for r0 in range(0, n+1, chunk):
                r1 = min(n+1, r0+chunk); u = t[r0:r1]
                if need_up:
                    s, e = law_rows(P, t, nx, u, +1); _, _, _, up = cdf_mean(t, P['lam0'], u, s, e, 0.0); mup[r0:r1] = up
                if need_lo:
                    s, e = law_rows(P, t, nx, u, -1); _, _, lo_, _ = cdf_mean(t, P['lam0'], u, s, e, 0.0); mlo[r0:r1] = lo_
            if need_up and need_lo: assert np.all(mlo <= mup + 1e-12)
        sites[i-1] = Site(mlo[:-1], mup[1:])
    return sites
def forward2(t, P, slo, shi, c, chunk):
    n = len(t)-1; w = np.diff(t); dF = (4*n + 100)*U + 1e-11
    Fup = np.ones(n); Flow = np.ones(n)
    for i in range(c, 0, -1):
        a = slo[i-1]; bb = shi[i-1]; newu = np.empty(n); newl = np.empty(n)
        for r0 in range(0, n, chunk):
            r1 = min(n, r0+chunk)
            if a.lo_delta:
                Fh = np.ones((r1-r0, n+1)); Fh[:, 0] = 0.0
            else:
                u = t[r0:r1]; s, e = law_rows(P, t, a, u, -1); Fh, _, _, _ = cdf_mean(t, P['lam0'], u, s, e, dF, False)
            u = t[r0+1:r1+1]; s, e = law_rows(P, t, bb, u, +1); _, Fl, _, _ = cdf_mean(t, P['lam0'], u, s, e, dF, False)
            kp, km = k_bounds(w, Fh, Fl)
            newu[r0:r1] = (kp*(Fup*w)[None, :]).sum(1)*P['lamr'][0]*(1+1e-9)
            newl[r0:r1] = (km*(Flow*w)[None, :]).sum(1)*P['lamr'][1]*(1-1e-9)
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
C2 = 20.0
BG = [-XC, -0.6, -0.4, -0.25, -0.15, -0.08, -0.04, -0.02, -0.01, 0.0]
def endgrid(r, h):
    s = math.sqrt(EPS*h)
    if r <= 1: return [None] + [x for x in [-1.89, -1.4, -1.15, -1.02, -0.96, -0.93, -0.915, -0.9075] if x < -XC-6*s] + [-XC-6*s, -XC-3*s, -XC-1.5*s, -XC]
    if r == 2: return [None, -XC-6*s, -XC-3*s, -XC-1.5*s, -XC]
    return [None, -XC]
def parse_jobs(specs, h1, c):
    jobs = []
    for sp in specs:
        f = sp.split(':')
        if f[0] == 'intall':
            jobs += [(2*c-1, BG[k], BG[k+1], ['int', BG[k], BG[k+1]]) for k in range(len(BG)-1)]
        elif f[0] == 'endall':
            for r in range(8 if c == 8 else 4):
                be = endgrid(r, h1); jobs += [(c+r, be[k], be[k+1], ['end', r, be[k], be[k+1]]) for k in range(len(be)-1)]
        elif f[0] == 'int':
            jobs.append((2*c-1, float(f[1]), float(f[2]), ['int', float(f[1]), float(f[2])]))
        elif f[0] == 'end':
            r = int(f[1]); bl = None if f[2] == 'inf' else float(f[2]); bh = -XC if f[3] == 'xc' else float(f[3])
            jobs.append((c+r, bl, bh, ['end', r, bl, bh]))
        elif f[0] == 'file':
            for line in open(f[1]):
                if not line.strip(): continue
                r, bl, bh = line.split(); r = int(r); bl = None if bl == 'inf' else float(bl); bh = float(bh)
                if bh == -0.89: bh = -XC
                jobs.append((c+r, bl, bh, ['end', r, bl, bh]))
    return jobs
def run(h1, h2, c1, specs, mode='center', c=8, lo=-XC, hi=0.0, dw=True, out=None, ncut=None, fwd='z', bf='both', K=4.0):
    t0 = time.process_time()
    t = make_cells(h1, lo, hi, c1, c2=C2) if dw else np.linspace(lo, hi, int(math.ceil((hi-lo)/(c1*math.sqrt(EPS*h1))))+1)
    n = len(t)-1; chunk = max(8, int(4e5//n))
    lam1 = 1.0/(EPS*h1); lam2 = 1.0/(EPS*h2); lam0 = math.sqrt(lam1*lam2)
    vr = vprime_range(t) if dw else (np.zeros(n), np.zeros(n))
    P = {'lam0': lam0, 'dl': (lam2 - lam0, lam1 - lam0), 'lamr': (lam1, lam2), 'vr': vr, 'mode': mode, 'dw': dw, 'K': K}
    iv = h2 > h1
    Ppt = dict(P); Ppt['lam0'] = lam1; Ppt['dl'] = (0.0, 0.0); Ppt['lamr'] = (lam1, lam1)   # 診断用：λ を λ1 に固定
    Pb = Ppt if bf == 'fwdonly' else P; Pf = Ppt if bf == 'backonly' else P
    ac = np.where((t[:-1] >= -XC-1e-15) & (t[1:] <= 1e-15))[0]   # a ∈ [−x_c, 0]（陰性対照の広い箱でも第759便と同じ範囲）
    res = {'h1': h1, 'h2': h2, 'c1': c1, 'n': n, 'mode': mode, 'fwd': fwd, 'c': c, 'cells': []}
    for N, blo, bhi, tag in parse_jobs(specs, h1, c):
        tj = time.process_time()
        if fwd == 'y':
            slo = chain(t, Pb, N, blo, chunk, True, True); shi = chain(t, Pb, N, bhi, chunk, True, True)
            Fu, Fl = forward_y(t, Pf, slo, shi, c, chunk)
        else:
            slo = chain(t, Pb, N, blo, chunk, True, True); shi = chain(t, Pb, N, bhi, chunk, True, True)
            Fu, Fl = forward2(t, Pf, slo, shi, c, chunk)
        up = float(Fu[ac].max()); lw = float(Fl[ac].max())
        res['cells'].append({'tag': tag, 'rho_up': up, 'rho_low': lw, 'cpu': time.process_time() - tj})
        res['rho_up_sup'] = max(x['rho_up'] for x in res['cells']); res['rho_low_sup'] = max(x['rho_low'] for x in res['cells'])
        res['cpu'] = time.process_time() - t0
        if out: json.dump(res, open(out, 'w'))
        print(f"h=[{h1:.6g},{h2:.6g}] mode={mode} n={n} {tag}: rho_up={up:.6g} rho_low={lw:.6g} cpu={time.process_time()-tj:.1f}s", flush=True)
    return res
if __name__ == '__main__':
    # 使い方：m813_iv2.py <mode> <c1> <out.json> <h1:h2> <spec>...（spec：intall・endall・int:lo:hi・end:r:lo:hi・file:path）
    mode, c1, out, hs = sys.argv[1], float(sys.argv[2]), sys.argv[3], sys.argv[4]
    h1, h2 = (float(x) for x in hs.split(':'))
    if mode in ('center', 'split'): r = run(h1, h2, c1, sys.argv[5:], mode=mode, out=out)
    elif mode == 'y': r = run(h1, h2, c1, sys.argv[5:], mode='center', out=out, fwd='y')
    elif mode == 'pos': r = run(h1, h2, c1, sys.argv[5:], mode='center', c=4, out=out, fwd='y')
    elif mode == 'neg': r = run(h1, h2, c1, sys.argv[5:], mode='center', c=8, lo=-XC-0.6, hi=0.6, dw=False, out=out, fwd='y')
    print(f"DONE h=[{h1:.6g},{h2:.6g}] mode={mode} c1={c1} n={r['n']} rho_up_sup={r['rho_up_sup']:.6g} rho_low_sup={r['rho_low_sup']:.6g} cpu={r['cpu']:.1f}s", flush=True)
