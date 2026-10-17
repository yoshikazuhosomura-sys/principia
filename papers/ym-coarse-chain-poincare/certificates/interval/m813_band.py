# 第813便・行の塊ごとの混合の格子（小さい ħ の計算量を下げる）。補題 M (c)（傾きの挟み込み ⇒ 尤度比の挟み込み）は任意の細胞の分割で
# 成り立つので、行の塊ごとに「法則の質量のある窓は元の細かい細胞、窓の外は G 個ずつまとめた粗い細胞」を使う。粗い細胞の材料は
# 中の細かい細胞の M の最小・最大、V′ の最小・最大、前向きの Φ の最大（下界は最小）。正しさは窓の取り方に依らない（窓は締まり具合だけに効く）。
# 結論文は印字しない。
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m813_iv import Site, law_rows, cdf_mean, EPS, XC, U
from m759_psi2 import k_bounds, Vp
E2 = EPS*EPS
def centers_rows(t, urows, Mlo, Mhi, dw=True):
    wm = 0.5*(t[:-1] + t[1:]); Mm = 0.5*(Mlo + Mhi)
    G = urows[:, None] - 2*wm[None, :] + Mm[None, :] - (E2*Vp(wm)[None, :] if dw else 0.0)
    neg = G < 0; first = np.where(neg.any(1), neg.argmax(1), len(wm) - 1)
    return wm[first]
def view(t, jL, jR, G):
    # 混合の格子の節点の添字（細かい格子の節点の部分集合）：[0, jL] は G 刻み、[jL, jR] は全て、[jR, n] は G 刻み。
    n = len(t) - 1
    left = list(range(0, jL, G)); right = list(range(jR, n, G))[1:] if jR < n else []
    idx = np.array(sorted(set(left + list(range(jL, jR + 1)) + right + [n])), dtype=int)
    return idx
def seg(arr, idx, f):
    # 混合の細胞 k（細かい細胞 idx[k]..idx[k+1]-1）の上の f（最小・最大）
    return f.reduceat(arr, idx[:-1])
def mixed(t, idx, site, P):
    tm = t[idx]
    Mlo = None if site.Mlo is None else seg(site.Mlo, idx, np.minimum)
    Mhi = None if site.Mhi is None else seg(site.Mhi, idx, np.maximum)
    vr = (seg(P['vr'][0], idx, np.minimum), seg(P['vr'][1], idx, np.maximum))
    Pm = dict(P); Pm['vr'] = vr
    return tm, Site(Mlo, Mhi, site.lo_delta), Pm
def window(t, P, u0, u1, Mlo, Mhi, W):
    c = centers_rows(t, np.array([u0, u1]), Mlo, Mhi, P['dw'])
    a = min(c) - W; b = max(c) + W
    jL = max(0, int(np.searchsorted(t, a, 'right')) - 1); jR = min(len(t) - 1, int(np.searchsorted(t, b, 'left')))
    return jL, max(jR, jL + 1)
def chain_b(t, P, N, b, R, G, W):
    n = len(t)-1; sites = [None]*N
    if b is None: sites[N-1] = Site(np.full(n, t[0]), np.full(n, t[0]), True)
    else: sites[N-1] = Site(np.full(n, b), np.full(n, b), False)
    for i in range(N-1, 0, -1):
        nx = sites[i]; mlo = np.empty(n+1); mup = np.empty(n+1)
        if nx.lo_delta: mlo[:] = t[0]; mup[:] = t[0]
        else:
            for r0 in range(0, n+1, R):
                r1 = min(n+1, r0+R); u = t[r0:r1]
                jL, jR = window(t, P, u[0], u[-1], nx.Mlo, nx.Mhi, W)
                idx = view(t, jL, jR, G); tm, sm, Pm = mixed(t, idx, nx, P)
                s, e = law_rows(Pm, tm, sm, u, +1); _, _, _, up = cdf_mean(tm, P['lam0'], u, s, e, 0.0); mup[r0:r1] = up
                s, e = law_rows(Pm, tm, sm, u, -1); _, _, lo_, _ = cdf_mean(tm, P['lam0'], u, s, e, 0.0); mlo[r0:r1] = lo_
            assert np.all(mlo <= mup + 1e-12)
        sites[i-1] = Site(mlo[:-1], mup[1:])
    return sites
def forward_b(t, P, slo, shi, c, R, G, W):
    n = len(t)-1; dF = (4*n + 100)*U + 1e-11
    Fup = np.ones(n); Flow = np.ones(n)
    for i in range(c, 0, -1):
        a = slo[i-1]; bb = shi[i-1]; newu = np.empty(n); newl = np.empty(n)
        for r0 in range(0, n, R):
            r1 = min(n, r0+R)
            jL, jR = window(t, P, t[r0], t[r1], bb.Mlo, bb.Mhi, W)
            if not a.lo_delta:
                jL2, jR2 = window(t, P, t[r0], t[r1], a.Mlo, a.Mhi, W); jL = min(jL, jL2); jR = max(jR, jR2)
            idx = view(t, jL, jR, G); tm = t[idx]; wm = np.diff(tm); m = len(tm) - 1
            if a.lo_delta:
                Fh = np.ones((r1-r0, m+1)); Fh[:, 0] = 0.0
            else:
                _, sa, Pm = mixed(t, idx, a, P); u = t[r0:r1]
                s, e = law_rows(Pm, tm, sa, u, -1); Fh, _, _, _ = cdf_mean(tm, P['lam0'], u, s, e, dF, False)
            _, sb, Pm = mixed(t, idx, bb, P); u = t[r0+1:r1+1]
            s, e = law_rows(Pm, tm, sb, u, +1); _, Fl, _, _ = cdf_mean(tm, P['lam0'], u, s, e, dF, False)
            kp, km = k_bounds(wm, Fh, Fl)
            PhU = seg(Fup, idx, np.maximum); PhL = seg(Flow, idx, np.minimum)
            newu[r0:r1] = (kp*(PhU*wm)[None, :]).sum(1)*P['lamr'][0]*(1+1e-9)
            newl[r0:r1] = (km*(PhL*wm)[None, :]).sum(1)*P['lamr'][1]*(1-1e-9)
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
