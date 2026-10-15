# 判定（証明書・ħ の区間版）：ħ ∈ [h1,h2] の全てで一様に ρ を上から押さえる。
# 一歩の法則 P_i(u,dw) ∝ exp(λuw − λw² + χ_i(w))、χ_i′ = −ε²λV′ + λ m_{i+1}(w)（i<N）、χ_N′ = −ε²λV′ + λb。
# 基準 λ0 のガウスの部分 exp(λ0uw − λ0w²) は erf で正確に、残り (λ−λ0)(uw − w²) + χ_i の傾き
#   (λ−λ0)(u − 2w + M) + λ0 M − ε²λV′（M = m_{i+1}(w) または b）を、行 u と細胞ごとに λ ∈ [λ2,λ1]・w・M の範囲で挟む。
# h1 = h2 なら psi2 と同じ傾き。浮動小数＋外向きの余裕（条件は本文 (A4)）。結論文は印字しない。
import sys, json, time, math, numpy as np
from psi2 import make_cells, vprime_range, log_erf_diff, hfun, k_bounds, EPS, XC, U
def slopes_rows(t, u, Mlo, Mhi, lam0, dl, lamr, vr, sign):
    # 行 u（列ベクトル）、細胞 j：傾きの下界（sign=−1）または上界（sign=+1）
    u = u[:, None]; tj = t[None, :-1]; tj1 = t[None, 1:]
    Xlo = u - 2*tj1 + Mlo[None, :]; Xhi = u - 2*tj + Mhi[None, :]
    c = np.stack([dl[0]*Xlo, dl[0]*Xhi, dl[1]*Xlo, dl[1]*Xhi])
    p1 = c.max(0) if sign > 0 else c.min(0)
    p2 = lam0*(Mhi if sign > 0 else Mlo)[None, :]
    p3 = (-EPS*EPS*lamr[1]*vr[0] if sign > 0 else -EPS*EPS*lamr[0]*vr[1])[None, :]
    s = p1 + p2 + p3
    return s + sign*(1e-9*(np.abs(p1) + np.abs(p2) + np.abs(p3)) + 1e-6)
def ell_rows(t, s, sign):
    w = np.diff(t)[None, :]; sw = s*w
    C = np.hstack([np.zeros((s.shape[0], 1)), np.cumsum(sw, 1)])
    M = np.abs(C).max(1)[:, None]
    d = 8*U*(M + np.abs(sw)) + 1e-300
    N = np.hstack([np.zeros((s.shape[0], 1)), np.cumsum(d, 1)])
    return C + sign*N*(1 + 1e-6)
def cells(t, lam0, u, s, ell):
    SQ = math.sqrt(lam0); w = np.diff(t)[None, :]; u = u[:, None]; tj = t[None, :-1]
    E0 = lam0*u*tj - lam0*tj*tj + ell[:, :-1]
    beta = lam0*u - 2*lam0*tj + s
    mu = beta/(2*lam0)
    a = -SQ*mu; b = SQ*(w - mu)
    lI = E0 + lam0*mu*mu + math.log(math.sqrt(math.pi)/(2*SQ)) + log_erf_diff(a, b)
    mrg = 64*U*(np.abs(lam0*u*tj) + lam0*tj*tj + np.abs(ell[:, :-1]) + lam0*mu*mu + np.abs(beta)*w + 50.0) + 1e-9
    assert np.all(b - a >= 1e-7)
    dlo = w*hfun((beta - 2*lam0*w)*w); dhi = w*hfun(beta*w)
    return lI - mrg, lI + mrg, np.maximum(0.0, dlo*(1-1e-12)), np.minimum(np.broadcast_to(w, dhi.shape), dhi*(1+1e-12))
def cdf_mean(t, lam0, u, s, ell, dF, want_mean=True):
    lIm, lIp, dlo, dhi = cells(t, lam0, u, s, ell)
    sh = lIp.max(1)[:, None]; Ip = np.exp(lIp - sh); Im = np.exp(lIm - sh)
    z = np.zeros((Ip.shape[0], 1))
    Ap = np.hstack([z, np.cumsum(Ip, 1)]); Am = np.hstack([z, np.cumsum(Im, 1)])
    Bp = np.hstack([np.cumsum(Ip[:, ::-1], 1)[:, ::-1], z]); Bm = np.hstack([np.cumsum(Im[:, ::-1], 1)[:, ::-1], z])
    with np.errstate(invalid='ignore', divide='ignore'):
        Fh = Ap/(Ap + Bm); Fl = Am/(Am + Bp)
    Fh = np.where(np.isfinite(Fh), Fh, 1.0); Fl = np.where(np.isfinite(Fl), Fl, 0.0)
    Fh = np.minimum(1.0, Fh + dF); Fl = np.maximum(0.0, Fl - dF); Fh[:, 0] = 0.0; Fl[:, 0] = 0.0; Fh[:, -1] = 1.0; Fl[:, -1] = 1.0
    if not want_mean: return Fh, Fl, None, None
    x0 = (t[:-1] - t[0])[None, :]
    mup = ((x0 + dhi)*Ip).sum(1)/Im.sum(1)*(1+1e-9) + t[0]
    mlo = ((x0 + dlo)*Im).sum(1)/Ip.sum(1)*(1-1e-9) + t[0]
    return Fh, Fl, mlo, mup
class Site:
    # サイト i の挟み込みの材料：M の範囲（細胞ごと）。lo_delta：下の法則が δ_lo（b → −∞）。
    def __init__(s, Mlo, Mhi, lo_delta=False): s.Mlo = Mlo; s.Mhi = Mhi; s.lo_delta = lo_delta
def law_rows(P, t, site, u, sign):
    s = slopes_rows(t, u, site.Mlo, site.Mhi, P['lam0'], P['dl'], P['lamr'], P['vr'], sign)
    return s, ell_rows(t, s, sign)
def backward(t, P, N, blo, bhi, chunk):
    n = len(t)-1; sites = [None]*N
    sites[N-1] = Site(np.full(n, -1e300 if blo is None else blo), np.full(n, bhi), blo is None)
    if blo is None: sites[N-1].Mlo = np.full(n, bhi)    # 下の法則は使わない（δ_lo）。値は形だけ。
    for i in range(N-1, 0, -1):
        nx = sites[i]; mlo = np.empty(n+1); mup = np.empty(n+1)
        for r0 in range(0, n+1, chunk):
            r1 = min(n+1, r0+chunk); u = t[r0:r1]
            s, e = law_rows(P, t, nx, u, +1); _, _, _, up = cdf_mean(t, P['lam0'], u, s, e, 0.0); mup[r0:r1] = up
            if nx.lo_delta: mlo[r0:r1] = t[0]
            else:
                s, e = law_rows(P, t, nx, u, -1); _, _, lo_, _ = cdf_mean(t, P['lam0'], u, s, e, 0.0); mlo[r0:r1] = lo_
        assert np.all(mlo <= mup + 1e-12)
        sites[i-1] = Site(mlo[:-1], mup[1:])
    return sites
def forward(t, P, sites, c, chunk):
    n = len(t)-1; w = np.diff(t); dF = (4*n + 100)*U + 1e-11
    Fup = np.ones(n); Flow = np.ones(n)
    for i in range(c, 0, -1):
        st = sites[i-1]; newu = np.empty(n); newl = np.empty(n)
        for r0 in range(0, n, chunk):
            r1 = min(n, r0+chunk)
            if st.lo_delta:
                Fh = np.ones((r1-r0, n+1)); Fh[:, 0] = 0.0
            else:
                u = t[r0:r1]; s, e = law_rows(P, t, st, u, -1); Fh, _, _, _ = cdf_mean(t, P['lam0'], u, s, e, dF, False)
            u = t[r0+1:r1+1]; s, e = law_rows(P, t, st, u, +1); _, Fl, _, _ = cdf_mean(t, P['lam0'], u, s, e, dF, False)
            kp, km = k_bounds(w, Fh, Fl)
            newu[r0:r1] = (kp*(Fup*w)[None, :]).sum(1)*P['lamr'][0]*(1+1e-9)
            newl[r0:r1] = (km*(Flow*w)[None, :]).sum(1)*P['lamr'][1]*(1-1e-9)
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
def run(h1, h2, c1, geoms, c=8, lo=-XC, hi=0.0, dw=True, arange=(-XC, 0.0), bgrid=None):
    t0 = time.process_time()
    t = make_cells(h1, lo, hi, c1, c2=C2) if dw else np.linspace(lo, hi, int(math.ceil((hi-lo)/(c1*math.sqrt(EPS*h1))))+1)
    n = len(t)-1; chunk = max(8, int(4e5//n))
    lam1 = 1.0/(EPS*h1); lam2 = 1.0/(EPS*h2); lam0 = math.sqrt(lam1*lam2)
    vr = vprime_range(t) if dw else (np.zeros(n), np.zeros(n))
    P = {'lam0': lam0, 'dl': (lam2 - lam0, lam1 - lam0), 'lamr': (lam1, lam2), 'vr': vr}
    ac = np.where((t[:-1] >= arange[0]-1e-15) & (t[1:] <= arange[1]+1e-15))[0]
    res = {'h1': h1, 'h2': h2, 'c1': c1, 'n': n, 'cells': []}
    for g in geoms:
        if g == 'int':
            bs = list(bgrid)
            jobs = [(c+c-1, bs[k], bs[k+1], ('int', float(bs[k]), float(bs[k+1]))) for k in range(len(bs)-1)]
        else:
            r = int(g); be = endgrid(r, h1)
            jobs = [(c+r, be[k], be[k+1], ('end', r, be[k+1])) for k in range(len(be)-1)]
        for N, blo, bhi, tag in jobs:
            sites = backward(t, P, N, blo, bhi, chunk)
            Fu, Fl = forward(t, P, sites, c, chunk)
            up = float(Fu[ac].max()); la = int(ac[np.argmax(Fu[ac])]); lw = float(Fl[ac].max())
            res['cells'].append({'tag': tag, 'rho_up': up, 'arg_a': [float(t[la]), float(t[la+1])], 'rho_low': lw})
    res['rho_up_sup'] = max(x['rho_up'] for x in res['cells']); res['rho_low_sup'] = max(x['rho_low'] for x in res['cells'])
    w = max(res['cells'], key=lambda x: x['rho_up']); res['worst'] = w['tag']
    res['cpu'] = time.process_time() - t0
    return res
C2 = 20.0
BG = [-XC, -0.6, -0.4, -0.25, -0.15, -0.08, -0.04, -0.02, -0.01, 0.0]
def endgrid(r, h):
    s = math.sqrt(EPS*h)
    if r <= 1: return [None] + [x for x in [-1.89, -1.4, -1.15, -1.02, -0.96, -0.93, -0.915, -0.9075] if x < -XC-6*s] + [-XC-6*s, -XC-3*s, -XC-1.5*s, -XC]
    if r == 2: return [None, -XC-6*s, -XC-3*s, -XC-1.5*s, -XC]
    return [None, -XC]
    g = [None, -XC-1.0, -XC-0.3, -XC-0.1]; d = 0.05
    while d > 0.5*math.sqrt(EPS*h):
        g.append(-XC-d); d = d/2
    return g + [-XC]
if __name__ == '__main__':
    # 使い方：psiP.py <mode> <c1> <out.json> h1:h2 ...（h1:h1 なら点）
    mode, c1, out = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    allres = []
    for hs in sys.argv[4:]:
        h1, h2 = (float(x) for x in hs.split(':'))
        if mode == 'main': r = run(h1, h2, c1, ['int'] + [str(k) for k in range(8)], c=8, bgrid=BG)
        elif mode == 'mainint': r = run(h1, h2, c1, ['int'], c=8, bgrid=BG)
        elif mode == 'end01': r = run(h1, h2, c1, ['0', '1'], c=8, bgrid=BG)
        elif mode == 'mainend': r = run(h1, h2, c1, [str(k) for k in range(8)], c=8, bgrid=BG)
        elif mode == 'pos': r = run(h1, h2, c1, ['int'] + [str(k) for k in range(4)], c=4, bgrid=BG)
        elif mode == 'neg': r = run(h1, h2, c1, ['int'], c=8, lo=-XC-0.6, hi=0.6, dw=False, bgrid=[-XC, -XC/2, 0.0])
        allres.append(r); json.dump(allres, open(out, 'w'))
        print(f"DONE mode={mode} h=[{h1:.6g},{h2:.6g}] c1={c1} rho_up_sup={r['rho_up_sup']:.6g} worst={r['worst']} rho_low_sup={r['rho_low_sup']:.6g} n={r['n']} cpu={r['cpu']:.1f}s", flush=True)
