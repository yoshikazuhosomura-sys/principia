# 第813便・前向きの一歩を「行ごとの拡大座標」で：u の細胞 l ごとに中心 c_l を取り、Y = c_l + s(Z − c_l)、s = √(λ/λ1) ∈ [s_min, 1]、
# s_min = √(λ2/λ1)。恒等式 λ∫Φ(t)k_Z(t)dt = λ1∫Φ(c+(τ−c)/s)k_Y(τ)dτ（s² = λ/λ1）により漸化の係数は λ1 に固定され、
# ガウスの部分 λ1(uy − y²) は全ての λ で正確。残りの傾き R = λ1[(r−1)H + M − ε²V′]（r = √(λ/λ1)、H = u − 2c + M − ε²V′、
# M と V′ は z = c + (y−c)/s で、y の細胞の z の像の包 Z_j の上で挟む）。Y の箱 [c+s(lo−c), c+s(hi−c)] の動きは、
# 下の法則を [lo, t_k]（t_k ≤ c+s_min(hi−c)）、上の法則を [t_m, hi]（t_m ≥ c+s_min(lo−c)）に切って尤度比の順序で受ける。
# Φ は Z_j の上の最大（下界は最小）。後ろ向き（平均の帯）は m813_iv の中心形のまま。結論文は印字しない。
import sys, os, json, time, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m813_iv import ell_rows, cells, EPS, XC, U
from m759_psi2 import k_bounds, Vp
E2 = EPS*EPS; ZC = -1/math.sqrt(3)
def vrange(za, zb):
    a = Vp(za); b = Vp(zb); lo = np.minimum(a, b); hi = np.maximum(a, b)
    hi = np.where((za < ZC) & (zb > ZC), Vp(ZC), hi)
    return lo - 1e-14, hi + 1e-14
class RangeMax:
    # 疎な表：区間 [j1, j2] の最大（mode=+1）／最小（mode=−1）
    def __init__(s, x, mode):
        s.mode = mode; s.tab = [np.asarray(x, float)]; k = 1
        while 2*k <= len(x):
            p = s.tab[-1]; f = np.maximum if mode > 0 else np.minimum
            s.tab.append(f(p[:-k], p[k:])); k *= 2
    def q(s, j1, j2):
        L = j2 - j1 + 1; lev = np.floor(np.log2(np.maximum(L, 1))).astype(int)
        out = np.empty(j1.shape)
        for l in np.unique(lev):
            m = lev == l; T = s.tab[l]; k = 1 << l
            A = T[j1[m]]; B = T[j2[m] - k + 1]
            out[m] = np.maximum(A, B) if s.mode > 0 else np.minimum(A, B)
        return out
def zhull(t, c, smin, lo, hi):
    # y の細胞 [t_j, t_{j+1}] の z の像の包（s ∈ [smin,1]）。c は行ごと（列ベクトル）。
    tj = t[None, :-1]; tj1 = t[None, 1:]
    za = np.where(tj >= c, tj, c + (tj - c)/smin); zb = np.where(tj1 >= c, c + (tj1 - c)/smin, tj1)
    return np.clip(za, lo, hi), np.clip(zb, lo, hi)
def zcells(t, za, zb):
    n = len(t) - 1
    j1 = np.clip(np.searchsorted(t, za, 'right') - 1, 0, n-1); j2 = np.clip(np.searchsorted(t, zb, 'left') - 1, 0, n-1)
    return j1, np.maximum(j1, j2)
def slopes_y(t, u, c, smin, site, lam1, sign, za, zb, j1, j2, mins, maxs, dw=True):
    Mlo = mins.q(j1, j2); Mhi = maxs.q(j1, j2)
    vlo, vhi = vrange(za, zb) if dw else (np.zeros(za.shape), np.zeros(za.shape))
    u = u[:, None]
    Hlo = u - 2*c + Mlo - E2*vhi; Hhi = u - 2*c + Mhi - E2*vlo
    if sign > 0:
        p1 = np.maximum(0.0, (smin - 1.0)*Hlo); p2 = Mhi - E2*vlo
    else:
        p1 = np.minimum(0.0, (smin - 1.0)*Hhi); p2 = Mlo - E2*vhi
    s = lam1*(p1 + p2)
    mag = lam1*(np.abs(p1) + np.abs(Mhi if sign > 0 else Mlo) + E2*np.abs(vlo if sign > 0 else vhi))
    return s + sign*(1e-9*mag + 1e-6)
def cdf_masked(t, lam1, u, s, ell, keep, dF):
    lIm, lIp, _, _ = cells(t, lam1, u, s, ell)
    lIp = np.where(keep, lIp, -np.inf); lIm = np.where(keep, lIm, -np.inf)
    sh = lIp.max(1)[:, None]; Ip = np.exp(lIp - sh); Im = np.exp(lIm - sh)
    z = np.zeros((Ip.shape[0], 1))
    Ap = np.hstack([z, np.cumsum(Ip, 1)]); Am = np.hstack([z, np.cumsum(Im, 1)])
    Bp = np.hstack([np.cumsum(Ip[:, ::-1], 1)[:, ::-1], z]); Bm = np.hstack([np.cumsum(Im[:, ::-1], 1)[:, ::-1], z])
    with np.errstate(invalid='ignore', divide='ignore'):
        Fh = Ap/(Ap + Bm); Fl = Am/(Am + Bp)
    Fh = np.where(np.isfinite(Fh), Fh, 1.0); Fl = np.where(np.isfinite(Fl), Fl, 0.0)
    Fh = np.minimum(1.0, Fh + dF); Fl = np.maximum(0.0, Fl - dF); Fh[:, 0] = 0.0; Fl[:, 0] = 0.0; Fh[:, -1] = 1.0; Fl[:, -1] = 1.0
    return Fh, Fl
def centers(t, umid, site, dw=True, sig=0.0, K=4.0):
    # 行ごとの中心：G(w) = u − 2w + M − ε²V′(w)（M は帯の中点）が負に変わる最初の細胞の中点。数値の選び方は結論の正しさに効かない。
    wm = 0.5*(t[:-1] + t[1:]); Mm = 0.5*(site.Mlo + site.Mhi)
    G = umid[:, None] - 2*wm[None, :] + Mm[None, :] - (E2*Vp(wm)[None, :] if dw else 0.0)
    neg = G < 0; first = np.where(neg.any(1), neg.argmax(1), len(wm) - 1)
    c = wm[first]; c = np.where(neg[:, 0], t[0], c); c = np.where(~neg.any(1), t[-1], c)
    c = np.where(c - t[0] <= K*sig, t[0], c); c = np.where(t[-1] - c <= K*sig, t[-1], c)   # 壁の近くの法則は壁を中心に（箱の切り落としを無くす）
    return c[:, None]
def forward_y(t, P, slo, shi, cc, chunk):
    n = len(t)-1; w = np.diff(t); dF = (4*n + 100)*U + 1e-11
    lam1, lam2 = P['lamr']; lo, hi = t[0], t[-1]; pt = (lam1 == lam2)
    smin = 1.0 if pt else math.sqrt(lam2/lam1)*(1 - 1e-12)     # 外向き（小さく＝像の包を広く）
    sig = 1.0/math.sqrt(2*lam1)
    Fup = np.ones(n); Flow = np.ones(n)
    for i in range(cc, 0, -1):
        a = slo[i-1]; bb = shi[i-1]; newu = np.empty(n); newl = np.empty(n)
        RU = RangeMax(Fup, +1); RL = RangeMax(Flow, -1)
        amin = None if a.lo_delta else RangeMax(a.Mlo, -1)
        amax = None if a.lo_delta else RangeMax(a.Mhi, +1)
        bmin = RangeMax(bb.Mlo, -1); bmax = RangeMax(bb.Mhi, +1)
        for r0 in range(0, n, chunk):
            r1 = min(n, r0+chunk)
            c = centers(t, 0.5*(t[r0:r1] + t[r0+1:r1+1]), bb, P['dw'], sig, P.get('K', 4.0))
            za, zb = zhull(t, c, smin, lo, hi); j1, j2 = zcells(t, za, zb)
            if pt: Bmin = np.full(c.shape, np.inf); Amax = np.full(c.shape, -np.inf)
            else:
                Bmin = np.where(c == hi, hi, c + smin*(hi - c) - 1e-12); Amax = np.where(c == lo, lo, c + smin*(lo - c) + 1e-12)
            if a.lo_delta:
                Fh = np.ones((r1-r0, n+1)); Fh[:, 0] = 0.0
            else:
                u = t[r0:r1]; s = slopes_y(t, u, c, smin, a, lam1, -1, za, zb, j1, j2, amin, amax, P['dw'])
                keep = t[None, 1:] <= Bmin
                Fh, _ = cdf_masked(t, lam1, u, s, ell_rows(t, s, -1), keep, dF)
            u = t[r0+1:r1+1]; s = slopes_y(t, u, c, smin, bb, lam1, +1, za, zb, j1, j2, bmin, bmax, P['dw'])
            keep = t[None, :-1] >= Amax
            _, Fl = cdf_masked(t, lam1, u, s, ell_rows(t, s, +1), keep, dF)
            kp, km = k_bounds(w, Fh, Fl)
            PhU = RU.q(j1, j2); PhL = RL.q(j1, j2)
            newu[r0:r1] = (kp*PhU*w[None, :]).sum(1)*lam1*(1+1e-9)
            newl[r0:r1] = (km*PhL*w[None, :]).sum(1)*lam1*(1-1e-9)
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
