# 第813便・判定（証明書・ħ の区間版、中心形）。第759便 m759_psiP と同じ不等式の組み立てで、傾きの挟み方だけを替えられる。
# 一歩の法則 P_i(u,dw) ∝ exp(λ(uw − w²) + χ_i(w))、χ_i′ = λ(M − ε²V′)（M = m_{i+1}(w) または b）。全体の傾き = λ·G、G := u − 2w + M − ε²V′。
# 基準 λ0 = √(λ1λ2) のガウス λ0(uw − w²) を erf で正確に積分し、残りの傾き
#   mode='center'：(λ−λ0)·G + λ0·(M − ε²V′)（中心形：G は法則の中心で 0）
#   mode='split' ：(λ−λ0)(u − 2w + M) + λ0·M − ε²λV′（第759便の版）
# を λ ∈ [λ2,λ1]・w・M の範囲で挟む。h1 = h2 なら両方とも点の版と同じ。浮動小数＋外向きの余裕（第759便 (A4) と同じ）。結論文は印字しない。
import sys, os, json, time, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m759_psi2 import make_cells, vprime_range, log_erf_diff, hfun, k_bounds, EPS, XC, U
E2 = EPS*EPS
def slopes_rows(t, u, Mlo, Mhi, P, sign):
    lam0 = P['lam0']; dl = P['dl']; lamr = P['lamr']; vr = P['vr']
    u = u[:, None]; tj = t[None, :-1]; tj1 = t[None, 1:]
    if P['mode'] == 'center':
        Glo = u - 2*tj1 + Mlo[None, :] - E2*vr[1][None, :]; Ghi = u - 2*tj + Mhi[None, :] - E2*vr[0][None, :]
        c = np.stack([dl[0]*Glo, dl[0]*Ghi, dl[1]*Glo, dl[1]*Ghi])
        p1 = c.max(0) if sign > 0 else c.min(0)
        p2 = lam0*((Mhi - E2*vr[0]) if sign > 0 else (Mlo - E2*vr[1]))[None, :]
        p3 = 0.0*p2
        a2 = lam0*((np.abs(Mhi) + E2*np.abs(vr[0])) if sign > 0 else (np.abs(Mlo) + E2*np.abs(vr[1])))[None, :]   # 打ち消しの前の大きさ
    else:
        Xlo = u - 2*tj1 + Mlo[None, :]; Xhi = u - 2*tj + Mhi[None, :]
        c = np.stack([dl[0]*Xlo, dl[0]*Xhi, dl[1]*Xlo, dl[1]*Xhi])
        p1 = c.max(0) if sign > 0 else c.min(0)
        p2 = lam0*(Mhi if sign > 0 else Mlo)[None, :]
        p3 = (-E2*lamr[1]*vr[0] if sign > 0 else -E2*lamr[0]*vr[1])[None, :]
        a2 = np.abs(p2)
    if dl[0] == 0.0 and dl[1] == 0.0: p1 = np.zeros_like(p2)   # 点の版：角の項は無い（片側の M だけを使う）
    s = p1 + p2 + p3
    return s + sign*(1e-9*(np.abs(p1) + a2 + np.abs(p3)) + 1e-6)
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
    def __init__(s, Mlo, Mhi, lo_delta=False): s.Mlo = Mlo; s.Mhi = Mhi; s.lo_delta = lo_delta
def law_rows(P, t, site, u, sign):
    s = slopes_rows(t, u, site.Mlo, site.Mhi, P, sign)
    return s, ell_rows(t, s, sign)
def backward(t, P, N, blo, bhi, chunk):
    n = len(t)-1; sites = [None]*N
    sites[N-1] = Site(np.full(n, bhi if blo is None else blo), np.full(n, bhi), blo is None)
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
