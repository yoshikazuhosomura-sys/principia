# 第904便：第813便の区間の証明書（m813_iv・m813_iv2・m813_band・m813_prod）を外向きの丸めの区間演算（ivx）に載せ替えたもの。
# 数学の組み立て（中心形の傾き・b の二本の鎖・混合の格子・補題 R/M）は第813便と同じ。変えたのは数の持ち方だけ：
#   - 法則 L^± の傾きは点（float）に固定し、区間の上端（L⁺）／下端（L⁻）を採る。その法則の ℓ・細胞の質量・CDF・平均を区間で囲む。
#   - 細胞の質量は log を経ずに e^{core − sh}·(√π/(2√λ0))·D、D = erfcx(A) − erfcx(B)e^{−(B²−A²)}（または小さい引数の erf の差）。
#   - 第759便 (A4) の余裕（64u·…、(4n+100)u、10⁻⁹、10⁻⁶）は全て外し、向きつきの丸めだけにした。
# 結論文は印字しない。数だけ。
import sys, os, json, time, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ivx
from ivx import dn, up, add, sub, mul, mul_ip, mul_iz, mul_pos, div_ip, div_pos, add_pp, sub_pp, mul_pp, div_pp, sqrt_pos, pt
from ivx import sum_nn, cumsum_nn, cumsum_signed, exp_iv, erfcx_dec, erf_any, hfun_iv
from m759_psi2 import make_cells, EPS, XC
from m813_band import view, centers_rows
from m813_iv2 import endgrid, BG, C2
assert EPS == 0.5
# V′(z) = z(z²−1)/2 の臨界点 −1/√3 と V′(−1/√3) = 1/(3√3)（mpmath の iv から外向きに）
pass  # (a local site-packages path was appended here when run)
from mpmath import iv
from gen_ivconst import outward
iv.prec = 200
ZC = outward(-1/iv.sqrt(iv.mpf(3))); VZC = outward(1/(3*iv.sqrt(iv.mpf(3))))
def vp_iv(z):
    z2 = mul_pp(z, z); a = (dn(z2[0] - 1.0), up(z2[1] - 1.0)); b = mul_ip(a, z)
    return dn(b[0]*0.5), up(b[1]*0.5)
def vprime_range(t):
    a = vp_iv(t[:-1]); b = vp_iv(t[1:])
    lo = np.minimum(a[0], b[0]); hi = np.maximum(a[1], b[1])
    inside = (t[:-1] <= ZC[1]) & (t[1:] >= ZC[0])
    hi = np.where(inside, np.maximum(hi, VZC[1]), hi)
    return lo, hi
class Site:
    def __init__(s, Mlo, Mhi, lo_delta=False): s.Mlo = Mlo; s.Mhi = Mhi; s.lo_delta = lo_delta
HFAST = os.environ.get('M904_HFAST', '0') == '1'
# 第905便：混合の格子で行の塊を RB 個ずつ束ねる（塊は R·RB 行、窓は束ねた塊の両端の行の中心から取る。締まり具合は窓に依るが、正しさは依らない）。
# 分割の選び方は正しさに効かない（補題 M (c)）。RB = 1 が第904便と同じ。
RB = int(os.environ.get('M905_RB', '1'))
DROP_CORNERS = False      # 陰性対照用（誤った式）：λ の区間の角の項を落とす
def slopes(t, u, Mlo, Mhi, P, sign):
    lam0 = P['lam0']; vlo, vhi = P['vr']; dl0, dl1 = P['dl0'], P['dl1']
    u = u[:, None]; tj = t[None, :-1]; tj1 = t[None, 1:]
    q = 0.25
    Glo = dn(dn(dn(u - 2*tj1) + Mlo[None, :]) - up(q*vhi)[None, :])
    Ghi = up(up(up(u - 2*tj) + Mhi[None, :]) - dn(q*vlo)[None, :])
    if sign > 0:
        c = np.maximum(np.maximum(up(dl0[0]*Glo), up(dl0[0]*Ghi)), np.maximum(up(dl1[1]*Glo), up(dl1[1]*Ghi)))
        p2 = up(lam0*up(Mhi - dn(q*vlo)))[None, :]
        if DROP_CORNERS: c = 0.0*c
        return up(c + p2)
    else:
        c = np.minimum(np.minimum(dn(dl0[0]*Glo), dn(dl0[0]*Ghi)), np.minimum(dn(dl1[1]*Glo), dn(dl1[1]*Ghi)))
        p2 = dn(lam0*dn(Mlo - up(q*vhi)))[None, :]
        if DROP_CORNERS: c = 0.0*c
        return dn(c + p2)
def ell_of(wI, s):
    sw = mul_ip((wI[0][None, :], wI[1][None, :]), s)
    z = np.zeros((s.shape[0], 1))
    return np.hstack([z, cumsum_signed(sw[0], 1, -1)]), np.hstack([z, cumsum_signed(sw[1], 1, +1)])
def masses(t, wI, P, u, s, ell, want_mean):
    lam0 = P['lam0']; SQ = P['SQ']; tj = t[:-1]
    A1 = mul_pp(lam0, tj)
    B1 = sub_pp(u[:, None], tj[None, :])
    E0 = add(mul((A1[0][None, :], A1[1][None, :]), B1), (ell[0][:, :-1], ell[1][:, :-1]))
    C1 = sub_pp(u[:, None], 2*tj[None, :])
    beta = add(mul_ip(C1, lam0), pt(s))
    mu = div_ip(beta, 2*lam0)
    W = (wI[0][None, :], wI[1][None, :])
    a = mul_iz(mu, SQ); a = (-a[1], -a[0])
    b = mul_iz(sub(W, mu), SQ)
    assert np.all(dn(SQ[0]*wI[0]) >= 1e-7)
    m1 = a[0] >= 0; m2 = (~m1) & (b[1] <= 0); m3 = ~(m1 | m2)
    lw = mul_pp(lam0, wI[0]), mul_pp(lam0, wI[1])
    LW = (lw[0][0][None, :], lw[1][1][None, :])                      # λ0·w の区間
    Ilo = np.zeros(s.shape); Ihi = np.zeros(s.shape)
    K = div_pos(ivx.SQRTPI, (dn(2*SQ[0]), up(2*SQ[1])))
    # 指数の基準 core：m1 は E0（左の節点）、m2 は E0 + w(β − λ0 w)（右の節点）、m3 は E0 + λ0μ²（頂上）
    Er = add(E0, mul_iz(sub(beta, LW), W))
    E3 = add(E0, mul_ip(mul(mu, mu), lam0))
    core = (np.where(m1, E0[0], np.where(m2, Er[0], E3[0])), np.where(m1, E0[1], np.where(m2, Er[1], E3[1])))
    sh = core[1].max(1)[:, None]                                       # 行の基準（任意の数でよい：比だけが効く）
    ec = exp_iv((dn(core[0] - sh), up(core[1] - sh)))
    D_lo = np.zeros(s.shape); D_hi = np.zeros(s.shape)
    m12 = m1 | m2
    if m12.any():
        # m1：A = a、B = b、B² − A² = λ0 w (w − 2μ)。m2：A = −b、B = −a、B² − A² = λ0 w (2μ − w)。
        X1 = mul_iz(sub(W, (2*mu[0], 2*mu[1])), LW)
        sel = lambda x, y: (np.where(m1, x[0], y[0])[m12], np.where(m1, x[1], y[1])[m12])
        AA = sel(a, (-b[1], -b[0])); BB = sel(b, (-a[1], -a[0])); XX = sel(X1, (-X1[1], -X1[0]))
        eA = erfcx_dec(AA); eB = erfcx_dec(BB); ex = exp_iv((-XX[1], -XX[0]))
        D = sub(eA, mul_pos(eB, ex))
        D_lo[m12] = np.maximum(D[0], 0.0); D_hi[m12] = D[1]
    if m3.any():
        D = sub(erf_any((b[0][m3], b[1][m3])), erf_any((a[0][m3], a[1][m3])))
        D_lo[m3] = np.maximum(D[0], 0.0); D_hi[m3] = D[1]
    v = mul_pos(mul_pos(ec, K), (D_lo, D_hi))
    Ilo, Ihi = v
    if not want_mean: return Ilo, Ihi, None, None
    y1 = mul_iz(sub(beta, (dn(2*LW[0]), up(2*LW[1]))), W); y2 = mul_iz(beta, W)
    hf = ivx.hfun_fast if HFAST else hfun_iv
    h1 = hf(y1); h2 = hf(y2)
    dlo = np.maximum(0.0, dn(wI[0][None, :]*h1[0])); dhi = np.minimum(wI[1][None, :], up(wI[1][None, :]*h2[1]))
    return Ilo, Ihi, dlo, dhi
def cdf_mean(t, wI, P, u, s, ell, want_mean=True):
    Im, Ip, dlo, dhi = masses(t, wI, P, u, s, ell, want_mean)
    z = np.zeros((Ip.shape[0], 1))
    Ap = np.hstack([z, cumsum_nn(Ip, 1, +1)]); Am = np.hstack([z, cumsum_nn(Im, 1, -1)])
    Bp = np.hstack([cumsum_nn(Ip[:, ::-1], 1, +1)[:, ::-1], z]); Bm = np.hstack([cumsum_nn(Im[:, ::-1], 1, -1)[:, ::-1], z])
    with np.errstate(invalid='ignore', divide='ignore'):
        dh = dn(Ap + Bm); Fh = np.where(dh > 0, up(Ap/dh), 1.0)
        dl = up(Am + Bp); Fl = np.where(dl > 0, dn(Am/dl), 0.0)
    Fh = np.minimum(1.0, np.where(np.isfinite(Fh), Fh, 1.0)); Fl = np.maximum(0.0, np.where(np.isfinite(Fl), Fl, 0.0))
    Fh[:, 0] = 0.0; Fl[:, 0] = 0.0; Fh[:, -1] = 1.0; Fl[:, -1] = 1.0
    if not want_mean: return Fh, Fl, None, None
    t0 = t[0]; x0 = sub_pp(t[:-1], t0)
    num = sum_nn(up(up(x0[1][None, :] + dhi)*Ip), 1, +1); den = sum_nn(Im, 1, -1)
    mup = up(t0 + up(num/den))
    num = sum_nn(dn(dn(x0[0][None, :] + dlo)*Im), 1, -1); den = sum_nn(Ip, 1, +1)
    mlo = dn(t0 + dn(num/den))
    return Fh, Fl, mlo, mup
def law(P, t, wI, site, u, sign):
    s = slopes(t, u, site.Mlo, site.Mhi, P, sign)
    return s, ell_of(wI, s)
def k_bounds(wI, Fh, Fl):
    one_m_Fl = up(1.0 - Fl[:, :-1]); one_m_Fh = np.maximum(0.0, dn(1.0 - Fh[:, 1:]))
    IFu = cumsum_nn(up(wI[1][None, :]*Fh[:, 1:]), 1, +1)
    IFbu = cumsum_nn(up(wI[1][None, :]*one_m_Fl)[:, ::-1], 1, +1)[:, ::-1]
    kp = up(up(one_m_Fl*IFu) + up(Fh[:, 1:]*IFbu))
    z = np.zeros((Fh.shape[0], 1))
    IFl = np.hstack([z, cumsum_nn(dn(wI[0][None, :]*Fl[:, :-1]), 1, -1)])[:, :-1]
    t2 = dn(wI[0][None, :]*one_m_Fh)
    IFbl = np.hstack([cumsum_nn(t2[:, ::-1], 1, -1)[:, ::-1][:, 1:], z])
    km = np.maximum(0.0, dn(dn(one_m_Fh*IFl) + dn(Fl[:, :-1]*IFbl)))
    return kp, km
def wof(t): return sub_pp(t[1:], t[:-1])
# ---- 細かい格子のままの鎖と前向き（m813_iv2.chain・forward2 に対応） ----
def chain(t, P, N, b, chunk):
    n = len(t)-1; wI = wof(t); sites = [None]*N
    if b is None: sites[N-1] = Site(np.full(n, t[0]), np.full(n, t[0]), True)
    else: sites[N-1] = Site(np.full(n, b), np.full(n, b), False)
    for i in range(N-1, 0, -1):
        nx = sites[i]; mlo = np.empty(n+1); mup = np.empty(n+1)
        if nx.lo_delta: mlo[:] = t[0]; mup[:] = t[0]
        else:
            for r0 in range(0, n+1, chunk):
                r1 = min(n+1, r0+chunk); u = t[r0:r1]
                s, e = law(P, t, wI, nx, u, +1); mup[r0:r1] = cdf_mean(t, wI, P, u, s, e)[3]
                s, e = law(P, t, wI, nx, u, -1); mlo[r0:r1] = cdf_mean(t, wI, P, u, s, e)[2]
            assert np.all(mlo <= mup)
        sites[i-1] = Site(mlo[:-1], mup[1:])
    return sites
def forward2(t, P, slo, shi, c, chunk):
    n = len(t)-1; wI = wof(t); Fup = np.ones(n); Flow = np.ones(n)
    for i in range(c, 0, -1):
        a = slo[i-1]; bb = shi[i-1]; newu = np.empty(n); newl = np.empty(n)
        for r0 in range(0, n, chunk):
            r1 = min(n, r0+chunk)
            if a.lo_delta:
                Fh = np.ones((r1-r0, n+1)); Fh[:, 0] = 0.0
            else:
                u = t[r0:r1]; s, e = law(P, t, wI, a, u, -1); Fh = cdf_mean(t, wI, P, u, s, e, False)[0]
            u = t[r0+1:r1+1]; s, e = law(P, t, wI, bb, u, +1); Fl = cdf_mean(t, wI, P, u, s, e, False)[1]
            kp, km = k_bounds(wI, Fh, Fl)
            newu[r0:r1] = up(P['lam1'][1]*sum_nn(up(kp*up(Fup*wI[1])[None, :]), 1, +1))
            newl[r0:r1] = dn(P['lam2'][0]*sum_nn(dn(km*dn(Flow*wI[0])[None, :]), 1, -1))
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
# ---- 混合の格子（m813_band に対応。窓の取り方は浮動のままでよい：正しさは分割に依らない） ----
def seg(arr, idx, f): return f.reduceat(arr, idx[:-1])
def mixed(t, idx, site, P):
    tm = t[idx]
    Mlo = seg(site.Mlo, idx, np.minimum); Mhi = seg(site.Mhi, idx, np.maximum)
    Pm = dict(P); Pm['vr'] = (seg(P['vr'][0], idx, np.minimum), seg(P['vr'][1], idx, np.maximum))
    return tm, Site(Mlo, Mhi, site.lo_delta), Pm
def window(t, P, u0, u1, Mlo, Mhi, W):
    c = centers_rows(t, np.array([u0, u1]), Mlo, Mhi, True)
    a = min(c) - W; b = max(c) + W
    jL = max(0, int(np.searchsorted(t, a, 'right')) - 1); jR = min(len(t) - 1, int(np.searchsorted(t, b, 'left')))
    return jL, max(jR, jL + 1)
def chain_b(t, P, N, b, R, G, W):
    R = R*RB
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
                idx = view(t, jL, jR, G); tm, sm, Pm = mixed(t, idx, nx, P); wm = wof(tm)
                s, e = law(Pm, tm, wm, sm, u, +1); mup[r0:r1] = cdf_mean(tm, wm, Pm, u, s, e)[3]
                s, e = law(Pm, tm, wm, sm, u, -1); mlo[r0:r1] = cdf_mean(tm, wm, Pm, u, s, e)[2]
            assert np.all(mlo <= mup)
        sites[i-1] = Site(mlo[:-1], mup[1:])
    return sites
def forward_b(t, P, slo, shi, c, R, G, W):
    R = R*RB
    n = len(t)-1; Fup = np.ones(n); Flow = np.ones(n)
    for i in range(c, 0, -1):
        a = slo[i-1]; bb = shi[i-1]; newu = np.empty(n); newl = np.empty(n)
        for r0 in range(0, n, R):
            r1 = min(n, r0+R)
            jL, jR = window(t, P, t[r0], t[r1], bb.Mlo, bb.Mhi, W)
            if not a.lo_delta:
                jL2, jR2 = window(t, P, t[r0], t[r1], a.Mlo, a.Mhi, W); jL = min(jL, jL2); jR = max(jR, jR2)
            idx = view(t, jL, jR, G); tm = t[idx]; wm = wof(tm); m = len(tm) - 1
            if a.lo_delta:
                Fh = np.ones((r1-r0, m+1)); Fh[:, 0] = 0.0
            else:
                _, sa, Pm = mixed(t, idx, a, P); u = t[r0:r1]
                s, e = law(Pm, tm, wm, sa, u, -1); Fh = cdf_mean(tm, wm, Pm, u, s, e, False)[0]
            _, sb, Pm = mixed(t, idx, bb, P); u = t[r0+1:r1+1]
            s, e = law(Pm, tm, wm, sb, u, +1); Fl = cdf_mean(tm, wm, Pm, u, s, e, False)[1]
            kp, km = k_bounds(wm, Fh, Fl)
            PhU = seg(Fup, idx, np.maximum); PhL = seg(Flow, idx, np.minimum)
            newu[r0:r1] = up(P['lam1'][1]*sum_nn(up(kp*up(PhU*wm[1])[None, :]), 1, +1))
            newl[r0:r1] = dn(P['lam2'][0]*sum_nn(dn(km*dn(PhL*wm[0])[None, :]), 1, -1))
        Fup = newu; Flow = np.maximum(newl, 0.0)
    return Fup, Flow
# ---- 一区間（m813_prod.one_interval に対応、幾何の絞り込みつき） ----
def params(h1, h2, t):
    lam1 = div_pp(2.0, h1); lam2 = div_pp(2.0, h2)
    lam0 = math.sqrt((2.0/h1)*(2.0/h2))        # 基準の λ0 は任意の点でよい（中心形の恒等式は全ての λ0 で成り立つ）
    return {'lam0': lam0, 'SQ': sqrt_pos(pt(lam0)), 'lam1': lam1, 'lam2': lam2,
            'dl0': sub(lam2, pt(lam0)), 'dl1': sub(lam1, pt(lam0)), 'vr': vprime_range(t)}
def geometry_cells(h1, specfile=None):
    from m813_prod import geometry_cells as gc
    return gc(h1, specfile)
def one_interval(h1, h2, c1, specfile=None, band=None, only=None, chunk_elems=2e5):
    t0 = time.process_time()
    t = make_cells(h1, -XC, 0.0, c1, c2=C2); n = len(t)-1; chunk = max(8, int(chunk_elems//n))
    P = params(h1, h2, t)
    ac = np.where((t[:-1] >= -XC-1e-15) & (t[1:] <= 1e-15))[0]
    out = []
    for g in geometry_cells(h1, specfile):
        kind, N = g[0], g[1]
        if kind == 'endcells': pairs = g[2]
        else: bs = g[2]; pairs = [(bs[k], bs[k+1]) for k in range(len(bs)-1)]
        gname = kind if kind == 'int' else 'end%d' % g[-1]
        if only is not None:
            pairs = [p for p in pairs if (gname, p[0], p[1]) in only]
            if not pairs: continue
        cache = {}
        if band: R, G, Wf = band; W = Wf/math.sqrt(2*P['lam0'])
        def ch(b):
            key = 'inf' if b is None else repr(float(b))
            if key not in cache: cache[key] = chain_b(t, P, N, b, R, G, W) if band else chain(t, P, N, b, chunk)
            return cache[key]
        for blo, bhi in pairs:
            tj = time.process_time()
            slo = ch(blo); shi = ch(bhi)
            Fu, Fl = forward_b(t, P, slo, shi, 8, R, G, W) if band else forward2(t, P, slo, shi, 8, chunk)
            out.append({'geom': gname, 'blo': blo, 'bhi': bhi, 'rho_up': float(Fu[ac].max()), 'rho_low': float(Fl[ac].max()), 'cpu': time.process_time() - tj})
            print(f"  IA h=[{h1:.7g},{h2:.7g}] {gname} [{blo},{bhi}] rho_up={out[-1]['rho_up']:.10g} rho_low={out[-1]['rho_low']:.4g} cpu={out[-1]['cpu']:.1f}s", flush=True)
    sup = max(o['rho_up'] for o in out); w = max(out, key=lambda o: o['rho_up'])
    return {'h1': h1, 'h2': h2, 'c1': c1, 'n': n, 'band': band, 'rho_up_sup': sup, 'worst': [w['geom'], w['blo'], w['bhi']],
            'rho_low_sup': max(o['rho_low'] for o in out), 'cpu': time.process_time() - t0, 'ncells': len(out), 'cells': out}
