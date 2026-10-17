# 第759便・判定（証明書・第二版）：傾きの挟み込み（MLR）＋ガウスの部分は erf で正確に。
# 浮動小数（倍精度）＋外向きの余裕。結論文は印字しない。数だけ。
# 一歩の法則 P_i(u,dw) ∝ exp(λuw − λw² + χ_i(w))、λ = 1/(εħ)、χ_i = −εV/ħ + Φ_i、Φ_i′(v) = λ m_{i+1}(v)（m は P_{i+1}(v,·) の平均、v について増加）、
# Φ_N′ = λb。χ_i′ を細胞ごとの傾き [s⁻_j, s⁺_j] で挟み、ℓ^±（区分一次）に置き換えた法則 L^± は P を確率順序（尤度比）で挟む。
# 影響の漸化 f′_{i−1}(u) = λ∫ f_i′(t) k_i(t;u) dt（k = F̄∫F + F∫F̄）は第一版と同じ。
import sys, json, time, math, numpy as np
from scipy.special import erf, erfcx
EPS = 0.5; XC = 0.89; U = 2.0**-53
def make_cells(h, lo, hi, c1, mu=0.04625775, c2=4.0, grow=1/20):
    hc = c1*math.sqrt(EPS*h); hf = min(hc, h/mu/c2); ys = [0.0]; y = 0.0; W = hi-lo
    while y < W:
        y = y + min(hc, hf + y*grow); ys.append(min(y, W))
    t = lo + np.array(ys); t[0] = lo; t[-1] = hi
    if t[-1]-t[-2] < 1e-3*hc: t = np.delete(t, -2)
    assert np.all(np.diff(t) > 0)
    return t
def Vp(z): return z*(z*z-1.0)/2.0
def vprime_range(t):
    a = Vp(t[:-1]); b = Vp(t[1:]); lo = np.minimum(a, b); hi = np.maximum(a, b)
    zc = -1/math.sqrt(3); inside = (t[:-1] < zc) & (t[1:] > zc)
    hi = np.where(inside, Vp(zc), hi)
    return lo - 1e-14, hi + 1e-14
def log_erf_diff(a, b):
    # log(erf(b) − erf(a))、a < b（配列）
    out = np.empty(a.shape)
    m1 = a >= 0; m2 = b <= 0; m3 = ~(m1 | m2)
    if m1.any():
        A = a[m1]; B = b[m1]
        out[m1] = -A*A + np.log(erfcx(A) - erfcx(B)*np.exp((A-B)*(A+B)))
    if m2.any():
        A = -b[m2]; B = -a[m2]
        out[m2] = -A*A + np.log(erfcx(A) - erfcx(B)*np.exp((A-B)*(A+B)))
    if m3.any():
        out[m3] = np.log(erf(b[m3]) - erf(a[m3]))
    return out
def hfun(y):
    # 区間 [0,1] の上の密度 ∝ e^{y x} の平均（y の増加関数）
    out = np.empty(y.shape); sm = np.abs(y) < 1e-3
    ys = y[sm]; out[sm] = 0.5 + ys/12.0
    yl = y[~sm]; out[~sm] = 1.0/(-np.expm1(-yl)) - 1.0/yl
    return out
class Law:
    # 傾き s（n）と節点の値 ℓ（n+1）を持つ区分一次の ℓ。点 u での細胞の質量の log の上下と、細胞の中の平均のずれの上下。
    def __init__(s, t, lam, slopes, sign):
        s.t = t; s.lam = lam; s.s = slopes; w = np.diff(t)
        ell = np.zeros(len(t))
        for j in range(len(w)):
            v = ell[j] + slopes[j]*w[j]
            ell[j+1] = v + sign*(8*U*(abs(ell[j]) + abs(slopes[j]*w[j])) + 1e-300)
        s.ell = ell
    def cells(s, u):
        t = s.t; lam = s.lam; SQ = math.sqrt(lam); w = np.diff(t)[None, :]
        u = np.asarray(u, float)[:, None]
        tj = t[None, :-1]
        E0 = lam*u*tj - lam*tj*tj + s.ell[None, :-1]            # 指数の左端の値
        beta = lam*u - 2*lam*tj + s.s[None, :]                   # 左端の傾き
        mu = beta/(2*lam)
        a = -SQ*mu; b = SQ*(w - mu)
        lI = E0 + lam*mu*mu + math.log(math.sqrt(math.pi)/(2*SQ)) + log_erf_diff(a, b)
        mag = np.abs(E0) + lam*mu*mu + 50.0
        mrg = 16*U*mag + 1e-11
        assert np.all(b - a >= 1e-7)
        dlo = w*hfun((beta - 2*lam*w)*w); dhi = w*hfun(beta*w)
        return lI - mrg, lI + mrg, np.maximum(0.0, dlo*(1-1e-12) - 1e-300), np.minimum(w, dhi*(1+1e-12))
def cdf_mean(law, u, dF, want_mean=True):
    lIm, lIp, dlo, dhi = law.cells(u)
    sh = lIp.max(1)[:, None]; Ip = np.exp(lIp - sh); Im = np.exp(lIm - sh)
    z = np.zeros((Ip.shape[0], 1))
    Ap = np.hstack([z, np.cumsum(Ip, 1)]); Am = np.hstack([z, np.cumsum(Im, 1)])
    Bp = np.hstack([np.cumsum(Ip[:, ::-1], 1)[:, ::-1], z]); Bm = np.hstack([np.cumsum(Im[:, ::-1], 1)[:, ::-1], z])
    with np.errstate(invalid='ignore', divide='ignore'):
        Fh = Ap/(Ap + Bm); Fl = Am/(Am + Bp)
    Fh = np.where(np.isfinite(Fh), Fh, 1.0); Fl = np.where(np.isfinite(Fl), Fl, 0.0)
    Fh[:, 0] = 0.0; Fl[:, 0] = 0.0; Fh[:, -1] = 1.0; Fl[:, -1] = 1.0
    Fh = np.minimum(1.0, Fh + dF); Fl = np.maximum(0.0, Fl - dF); Fh[:, 0] = 0.0; Fl[:, -1] = 1.0
    if not want_mean: return Fh, Fl, None, None
    x0 = (law.t[:-1] - law.t[0])[None, :]
    mup = ((x0 + dhi)*Ip).sum(1)/Im.sum(1)*(1+1e-9) + law.t[0]
    mlo = ((x0 + dlo)*Im).sum(1)/Ip.sum(1)*(1-1e-9) + law.t[0]
    return Fh, Fl, mlo, mup
def k_bounds(w, Fh, Fl):
    IFu = np.cumsum(w[None, :]*Fh[:, 1:], 1)
    IFbu = np.cumsum((w[None, :]*(1.0-Fl[:, :-1]))[:, ::-1], 1)[:, ::-1]
    kp = (1.0-Fl[:, :-1])*IFu + Fh[:, 1:]*IFbu
    z = np.zeros((Fh.shape[0], 1))
    IFl = np.hstack([z, np.cumsum(w[None, :]*Fl[:, :-1], 1)])[:, :-1]
    t2 = w[None, :]*(1.0-Fh[:, 1:])
    IFbl = np.hstack([np.cumsum(t2[:, ::-1], 1)[:, ::-1][:, 1:], z])
    km = (1.0-Fh[:, 1:])*IFl + Fl[:, :-1]*IFbl
    return kp*(1+1e-9), np.maximum(km*(1-1e-9), 0.0)
def backward(t, h, N, blo, bhi, chunk, dw=True):
    # 戻り値：laws[i-1] = (L⁻_i, L⁺_i)、i=1..N。L⁻_N が None なら一点 δ_lo（b → −∞ の極限）。
    lam = 1.0/(EPS*h); n = len(t)-1
    vlo, vhi = vprime_range(t) if dw else (np.zeros(n), np.zeros(n))
    sp = -EPS*vlo/h + lam*bhi; sp = sp + 1e-9*np.abs(sp) + 1e-6
    laws = [None]*N
    if blo is None: Lm = None
    else:
        sm = -EPS*vhi/h + lam*blo; sm = sm - 1e-9*np.abs(sm) - 1e-6; Lm = Law(t, lam, sm, -1.0)
    laws[N-1] = (Lm, Law(t, lam, sp, +1.0))
    for i in range(N-1, 0, -1):
        Lm_, Lp_ = laws[i]
        mlo = np.empty(n+1); mup = np.empty(n+1)
        for r0 in range(0, n+1, chunk):
            r1 = min(n+1, r0+chunk); u = t[r0:r1]
            _, _, _, up = cdf_mean(Lp_, u, 0.0); mup[r0:r1] = up
            if Lm_ is None: mlo[r0:r1] = t[0]
            else:
                _, _, lo_, _ = cdf_mean(Lm_, u, 0.0); mlo[r0:r1] = lo_
        assert np.all(mlo <= mup + 1e-12)
        sp = -EPS*vlo/h + lam*mup[1:]; sp = sp + 1e-9*np.abs(sp) + 1e-6
        sm = -EPS*vhi/h + lam*mlo[:-1]; sm = sm - 1e-9*np.abs(sm) - 1e-6
        laws[i-1] = (Law(t, lam, sm, -1.0), Law(t, lam, sp, +1.0))
    return laws
def forward(t, h, laws, c, chunk):
    lam = 1.0/(EPS*h); n = len(t)-1; w = np.diff(t); dF = (4*n + 100)*U + 1e-11
    Fup = np.ones(n); Flow = np.ones(n)
    for i in range(c, 0, -1):
        Lm, Lp = laws[i-1]; newu = np.empty(n); newl = np.empty(n)
        for r0 in range(0, n, chunk):
            r1 = min(n, r0+chunk)
            if Lm is None:
                Fh = np.ones((r1-r0, n+1)); Fh[:, 0] = 0.0
            else:
                Fh, _, _, _ = cdf_mean(Lm, t[r0:r1], dF, False)      # 確率順序で小さい法則・u の左端 ⇒ CDF の上界
            _, Fl, _, _ = cdf_mean(Lp, t[r0+1:r1+1], dF, False)      # 大きい法則・u の右端 ⇒ CDF の下界
            kp, km = k_bounds(w, Fh, Fl)
            newu[r0:r1] = (kp*(Fup*w)[None, :]).sum(1)*lam*(1+1e-9)
            newl[r0:r1] = (km*(Flow*w)[None, :]).sum(1)*lam*(1-1e-9)
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
def run(h, c1, geoms, Nb, c=8, lo=-XC, hi=0.0, dw=True, arange=(-XC, 0.0), bgrid=None, c2=4.0):
    t0 = time.process_time()
    t = make_cells(h, lo, hi, c1, c2=c2) if dw else np.linspace(lo, hi, int(math.ceil((hi-lo)/(c1*math.sqrt(EPS*h))))+1)
    n = len(t)-1; chunk = max(8, int(1.0e6//n))
    ac = np.where((t[:-1] >= arange[0]-1e-15) & (t[1:] <= arange[1]+1e-15))[0]
    res = {'h': h, 'c1': c1, 'n': n, 'cells': []}
    for g in geoms:
        if g == 'int':
            bs = list(bgrid) if bgrid is not None else list(np.linspace(-XC, 0.0, Nb+1))
            jobs = [(c+c-1, bs[k], bs[k+1], ('int', float(bs[k]), float(bs[k+1]))) for k in range(len(bs)-1)]
        else:
            r = int(g); be = [None, -XC-1.0, -XC-0.3, -XC-0.1, -XC] if r == 0 else [None, -XC]; jobs = [(c+r, be[k], be[k+1], ('end', r, be[k+1])) for k in range(len(be)-1)]
        for N, blo, bhi, tag in jobs:
            laws = backward(t, h, N, blo, bhi, chunk, dw)
            Fu, Fl = forward(t, h, laws, c, chunk)
            up = float(Fu[ac].max()); la = int(ac[np.argmax(Fu[ac])]); lw = float(Fl[ac].max())
            res['cells'].append({'tag': tag, 'rho_up': up, 'arg_a': [float(t[la]), float(t[la+1])], 'rho_low': lw})
            print(f"h={h:.6g} n={n} c={c} {tag}: rho_up={up:.6g} at a in [{t[la]:.5f},{t[la+1]:.5f}] rho_low={lw:.6g} cpu={time.process_time()-t0:.1f}s", flush=True)
    res['rho_up_sup'] = max(x['rho_up'] for x in res['cells']); res['rho_low_sup'] = max(x['rho_low'] for x in res['cells'])
    res['cpu'] = time.process_time() - t0
    return res
if __name__ == '__main__':
    mode, c1, Nb, out = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    allres = []
    for hs in sys.argv[5:]:
        h = float(hs)
        if mode == 'main': r = run(h, c1, ['int'] + [str(k) for k in range(8)], Nb, c=8)
        elif mode == 'mainint': r = run(h, c1, ['int'], Nb, c=8)
        elif mode == 'pos': r = run(h, c1, ['int'] + [str(k) for k in range(4)], Nb, c=4)
        elif mode == 'neg':
            lo, hi = ((-XC-0.6, 0.6) if h >= 1e-3 else (-1.2, 0.3))
            r = run(h, c1, ['int'], Nb, c=8, lo=lo, hi=hi, dw=False)
        allres.append(r); json.dump(allres, open(out, 'w'))
        print(f"DONE h={h:.6g} rho_up_sup={r['rho_up_sup']:.6g} rho_low_sup={r['rho_low_sup']:.6g} n={r['n']} cpu={r['cpu']:.1f}s", flush=True)
