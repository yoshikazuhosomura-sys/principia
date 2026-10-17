# 第904便：外向きの丸めの区間演算（numpy の配列、[lo, hi] の組）。
# 規約：IEEE の +−×÷√（最近接の丸め）の結果を np.nextafter で一 ulp ずつ外に広げる。それ以外の浮動小数の関数（libm の exp・log・erf 等）は使わない。
# 超越関数：exp は Tang 型の引数の還元（2^{j/64} の表は mpmath の iv）＋六次の Taylor＋剰余、erfcx は表（mpmath の iv で作った各節点の Taylor 係数と
# 完全単調性による剰余）＋大きい x の漸近級数（剰余は最初の捨てた項で抑えられ同符号、DLMF 7.12(i)）、erf は小さい x の交代級数。
# 和：非負の項の和（任意の順序）は (1±u)^{n−1} の因子で外に、符号つきの累積和は 誤差 ≤ u·Σ|部分和| で外に（どちらも IEEE の加算の丸めの性質だけ）。
import os, math, numpy as np
INF = np.inf
U = 2.0**-53
RN_ONLY = False          # 陰性対照用：True にすると nextafter を外す（区間演算でなくなる）
# 広げ方：'ulp'＝np.nextafter で一 ulp（既定）。'rel'＝r ± (|r|·2⁻⁵¹ + 2⁻¹⁰⁷⁴)（最近接の丸めの誤差 ≤ |r|·2⁻⁵³ を、足し算の丸めを込めて覆う、2〜4 ulp、速い）
WIDEN = os.environ.get('IVX_WIDEN', 'ulp')
_E51 = 2.0**-51; _ETA = 5e-324
if WIDEN == 'rel':
    def dn(x):
        return x if RN_ONLY else x - (np.abs(x)*_E51 + _ETA)
    def up(x):
        return x if RN_ONLY else x + (np.abs(x)*_E51 + _ETA)
else:
    def dn(x):
        return x if RN_ONLY else np.nextafter(x, -INF)
    def up(x):
        return x if RN_ONLY else np.nextafter(x, INF)
# ---- 点どうしの演算（結果は区間） ----
def add_pp(a, b): s = a + b; return dn(s), up(s)
def sub_pp(a, b): s = a - b; return dn(s), up(s)
def mul_pp(a, b): s = a * b; return dn(s), up(s)
def div_pp(a, b): s = a / b; return dn(s), up(s)
# ---- 区間の演算 ----
def add(x, y): return dn(x[0] + y[0]), up(x[1] + y[1])
def sub(x, y): return dn(x[0] - y[1]), up(x[1] - y[0])
def neg(x): return -x[1], -x[0]
def mul(x, y):
    a = x[0]*y[0]; b = x[0]*y[1]; c = x[1]*y[0]; d = x[1]*y[1]
    return dn(np.minimum(np.minimum(a, b), np.minimum(c, d))), up(np.maximum(np.maximum(a, b), np.maximum(c, d)))
def mul_pos(x, y):
    # x, y ≥ 0（呼び手が保証）
    return dn(x[0]*y[0]), up(x[1]*y[1])
def mul_ip(x, p):
    # 区間 x × 点 p（p の符号は任意）
    a = x[0]*p; b = x[1]*p; pos = p >= 0
    return dn(np.where(pos, a, b)), up(np.where(pos, b, a))
def mul_iz(x, z):
    # 区間 x（符号は任意）× 正の区間 z
    lo = np.where(x[0] >= 0, x[0]*z[0], x[0]*z[1]); hi = np.where(x[1] >= 0, x[1]*z[1], x[1]*z[0])
    return dn(lo), up(hi)
def div_pos(x, y):
    # x ≥ 0、y > 0
    return dn(x[0]/y[1]), up(x[1]/y[0])
def div_ip(x, p):
    # 区間 ÷ 正の点
    return dn(x[0]/p), up(x[1]/p)
def sqrt_pos(x): return dn(np.sqrt(x[0])), up(np.sqrt(x[1]))
def pt(a): return a, a
def ipow_up(x, k):
    # x ≥ 0、x^k の上界（掛け算だけ）
    r = np.ones_like(np.asarray(x, float))
    for _ in range(k): r = up(r*x)
    return r
# ---- 和 ----
def _fac(m):
    # m 回の加算の丸めの因子：下 1 − m·u·(1+2⁻²⁰)、上 1/(1 − m·u) を上に（m·u ≤ 2⁻²⁰ を仮定）
    m = np.asarray(m, float)
    assert np.all(m*U <= 2.0**-20)
    lo = dn(1.0 - dn(m*U*(1.0 + 2.0**-20)))       # (1+u)^{−m} ≥ 1 − m u
    hi = up(1.0 + up(m*U*(1.0 + 2.0**-19)))       # (1−u)^{−m} ≤ 1 + m u (1 + m u + …) ≤ 1 + m u (1 + 2⁻¹⁹)
    return lo, hi
def sum_nn(x, axis, side):
    # 非負の項の和（numpy の総和の順序は任意でよい）。side = −1：下界、+1：上界
    n = x.shape[axis]; s = x.sum(axis)
    if RN_ONLY: return s
    f = _fac(max(n - 1, 0))
    return dn(s*f[0]) if side < 0 else up(s*f[1])
def cumsum_nn(x, axis, side):
    # 非負の項の累積和（逐次）。第 j 項までの部分和は j−1 回の加算。
    s = np.cumsum(x, axis)
    if RN_ONLY: return s
    n = x.shape[axis]; shp = [1]*x.ndim; shp[axis] = n
    m = np.arange(n, dtype=float).reshape(shp)
    f = _fac(m)
    return dn(s*f[0]) if side < 0 else up(s*f[1])
def cumsum_signed(x, axis, side):
    # 符号つきの累積和の下界（side −1）／上界（+1）。誤差 ≤ u·Σ_{k≤j}|Ŝ_k|（各加算の誤差 ≤ u|結果|、誤差は足し算で積もる）。
    s = np.cumsum(x, axis)
    if RN_ONLY: return s
    e = cumsum_nn(np.abs(s), axis, +1)
    e = up(e*U)
    e = up(e + 5e-324)       # 下位桁あふれの保険
    return dn(s - e) if side < 0 else up(s + e)
# ---- 定数（mpmath の iv から外向きに倍精度へ） ----
_here = os.path.dirname(os.path.abspath(__file__))
def _load_consts():
    p = os.path.join(_here, 'ivconst.npz')
    if not os.path.exists(p):
        raise SystemExit('ivconst.npz が無い：python3 gen_ivconst.py を先に')
    return dict(np.load(p))
C = _load_consts()
def cst(name): return float(C[name + '_lo']), float(C[name + '_hi'])
LN2_64_C1 = float(C['ln2_64_c1'])           # 32 ビットの上位部分（N·C1 は丸め無し）
LN2_64_C2 = cst('ln2_64_c2')                # ln2/64 − C1 の区間
INV_LN2_64 = float(C['inv_ln2_64'])          # 64/ln2 の近似（還元の整数の選び方だけに使う）
T64 = (C['t64_lo'], C['t64_hi'])             # 2^{j/64}、j = 0..63
SQRTPI = cst('sqrtpi'); TWO_OVER_SQRTPI = cst('two_over_sqrtpi')
INV_FACT = [cst('invfact%d' % k) for k in range(8)]
EXP_DEG = 6; EXP_RMAX = 0.0060
EXP_REM = float(C['exp_rem'])                # RMAX^7/7!·e^{RMAX} の上界
# ---- 第905便：多項式の評価の誤差を先に上から抑える（IVX_POLY=fast、既定）。'iv' は第904便の区間の Horner ----
# 浮動の Horner（FMA なし）で p̃(x) = Σ c̃_k x^k（次数 n）を計算した結果 ŷ は、IEEE の最近接の丸めの下で
#   |ŷ − p̃(x)| ≤ γ_{2n} Σ|c̃_k||x|^k、γ_m = m u/(1 − m u)  （Higham, Accuracy and Stability, 2nd ed., (5.3)、［典］）
# を満たす（下位桁あふれが無いとき。あるときは一回の演算ごとに絶対 2⁻¹⁰⁷⁴ 以下が加わり、|x| < 1 で積もっても 2n·2⁻¹⁰⁷⁴ 以下：2⁻¹⁰⁰⁰ で覆う）。
# 真の係数 c_k ∈ [lo_k, hi_k] と c̃_k = hi_k の差は Σ(hi_k − lo_k)|x|^k ≤ Σ(hi_k − lo_k)（|x| < 1）。
# 陰性対照の RN_ONLY では γ の項だけを外す（剰余は EXP_NO_REM／ERFCX_NO_REM が外す）。
POLY = os.environ.get('IVX_POLY', 'fast')
def _gamma_up(m):
    # γ_m の上界（m u ≤ 2⁻⁴⁰）
    return up(up(m*U)*(1.0 + 2.0**-39))
def _sum_up(vals):
    s = 0.0
    for v in vals: s = up(s + v)
    return s
_EXPB = {}
def _exp_bound(deg, rem):
    key = (deg, rem, RN_ONLY)
    if key not in _EXPB:
        S = _sum_up([up(INV_FACT[k][1]*float(EXP_RMAX)**k*(1.0 + 2.0**-40)) for k in range(deg + 1)])   # Σ c̃_k |r|^k（|r| ≤ RMAX）、冪の丸めを (1+2⁻⁴⁰) で覆う
        Wd = _sum_up([up(INV_FACT[k][1] - INV_FACT[k][0]) for k in range(deg + 1)])
        g = 0.0 if RN_ONLY else up(_gamma_up(2*deg)*S)
        _EXPB[key] = _sum_up([g, Wd, rem, 2.0**-1000])
    return _EXPB[key]
# ---- exp ----
EXP_DEG_OVERRIDE = None; EXP_NO_REM = False  # 陰性対照用
def _reduce(x):
    N = np.rint(x*INV_LN2_64)
    t1 = N*LN2_64_C1                         # 丸め無し（|N| < 2^17、C1 は 32 ビット）
    s_lo = dn(x - t1); s_hi = up(x - t1)
    nc = mul_ip(LN2_64_C2, N)
    r_lo = dn(s_lo - nc[1]); r_hi = up(s_hi - nc[0])
    return N, r_lo, r_hi
# 第905便：還元の片側だけを安く。s = fl(x − N·C1)（N·C1 は丸め無し）、n̂ = fl(N·c̃2)（c̃2 = C2 の上端）、r̂ = fl(s − n̂)。
# 真の r = x − N·ln2/64 との差 ≤ 2⁻⁵²(|s| + |r̂|)·(1+u) ＋ |N|·(C2 の幅 ＋ 2⁻⁵²c̃2) ＋ 下位桁あふれ。
# 定数を 2 倍（2⁻⁵¹、2K）にしておけば、この誤差の式を浮動で計算したときの丸め（三回、各 ≤ u）も覆う。
_RK2 = 2.0*((LN2_64_C2[1] - LN2_64_C2[0]) + LN2_64_C2[1]*2.0**-52)
def _reduce_side(x, side):
    N = np.rint(x*INV_LN2_64)
    s = x - N*LN2_64_C1
    r = s - N*LN2_64_C2[1]
    E = (np.abs(s) + np.abs(r))*2.0**-51 + np.abs(N)*_RK2 + 3*_ETA
    if RN_ONLY: E = 0.0
    return N, (dn(r - E) if side < 0 else up(r + E))
def exp_iv(x):
    # x = (lo, hi)。exp の区間を返す。
    xl = np.asarray(x[0], float); xh = np.asarray(x[1], float)
    assert not (np.isnan(xl).any() or np.isnan(xh).any())
    zero = xl < -1000.0
    xlc = np.clip(xl, -1000.0, 709.0); xhc = np.clip(xh, -1000.0, 710.0)
    if POLY == 'fast': Nl, rl = _reduce_side(xlc, -1); Nh, rh = _reduce_side(xhc, +1)
    else: Nl, rl, _ = _reduce(xlc); Nh, _, rh = _reduce(xhc)
    deg = EXP_DEG if EXP_DEG_OVERRIDE is None else EXP_DEG_OVERRIDE
    # 下界は xl の還元、上界は xh の還元で別々に Horner（r は点ではなく区間 [rl_lo, rl_hi] だが、単調性で端だけ要る）
    out = []
    for N, r, side in ((Nl, rl, -1), (Nh, rh, +1)):
        assert np.all(np.abs(r) <= EXP_RMAX), np.abs(r).max()
        rem = 0.0 if EXP_NO_REM else EXP_REM
        if POLY == 'fast':
            # 第905便：浮動の Horner を一度だけ（係数は区間の上端 c̃_k）、誤差は先に上から抑えた定数 B で囲む（_exp_bound）
            q = np.full(r.shape, INV_FACT[deg][1])
            for k in range(deg - 1, -1, -1):
                q = q*r + INV_FACT[k][1]
            B = _exp_bound(deg, rem)
            v = dn(q - B) if side < 0 else up(q + B)
        else:
            q = (np.full(r.shape, INV_FACT[deg][0]), np.full(r.shape, INV_FACT[deg][1]))
            for k in range(deg - 1, -1, -1):
                q = mul_ip(q, r)                     # q > 0、r の符号は任意
                q = add(q, (INV_FACT[k][0], INV_FACT[k][1]))
            v = dn(q[0] - rem) if side < 0 else up(q[1] + rem)
        # 第905便：N = 64m + j（N は整数の浮動、|N| < 2¹⁷：N·2⁻⁶ と floor と 64m は丸め無し）。2^m は指数の欄を直接組む。
        mf = np.floor(N*0.015625); j = (N - 64.0*mf).astype(np.int64); m = mf.astype(np.int64)
        tj = np.take(T64[0] if side < 0 else T64[1], j)
        v = dn(v*tj) if side < 0 else up(v*tj)
        # v ∈ [0.98, 2.1]：m1 ∈ [−1000, 1023] の 2^{m1} を掛けるのは丸め無し（結果は正規化数か inf）。残り 2^{m2}（m2 ∈ [−443, 1]）を掛ける一回だけが丸まる（非正規化数を含む）。
        m1 = np.clip(m, -1000, 1023); m2 = m - m1
        p1 = ((m1 + 1023) << 52).view(np.float64); p2 = ((m2 + 1023) << 52).view(np.float64)
        with np.errstate(over='ignore'):
            v = (v*p1)*p2
        v = dn(v) if side < 0 else up(v)
        out.append(v)
    lo = np.where(zero, 0.0, np.maximum(out[0], 0.0)); hi = out[1]
    return lo, hi
# ---- erfcx（x ≥ −1/64） ----
_T = None
ERFCX_NO_REM = False; ERFCX_DEG_OVERRIDE = None     # 陰性対照用
def _load_erfcx():
    global _T
    if _T is None:
        p = os.path.join(_here, 'erfcx_table.npz')
        if not os.path.exists(p): raise SystemExit('erfcx_table.npz が無い：python3 gen_erfcx_table.py を先に')
        _T = dict(np.load(p))
    return _T
_ERB = {}
def _erfcx_bound(deg):
    # 節点ごと：γ_{2·deg}·Σ_n max|c_n|·(g/2)^n ＋ Σ_n (hi_n − lo_n)(g/2)^n ＋ 2⁻¹⁰⁰⁰（|d| ≤ g/2 = 2⁻⁶、冪は丸め無し）
    key = (deg, RN_ONLY)
    if key not in _ERB:
        T = _load_erfcx(); hd = float(T['g'])/2.0
        S = np.zeros(T['c_hi'].shape[1]); Wd = np.zeros_like(S)
        for n in range(deg + 1):
            p = hd**n
            S = up(S + up(np.maximum(np.abs(T['c_lo'][n]), np.abs(T['c_hi'][n]))*p))
            Wd = up(Wd + up(up(T['c_hi'][n] - T['c_lo'][n])*p))
        g = 0.0 if RN_ONLY else up(_gamma_up(2*deg)*S)
        _ERB[key] = up(up(g + Wd) + 2.0**-1000)
    return _ERB[key]
_ERFT = {}
def _erfcx_fasttab(deg):
    key = (deg, RN_ONLY, ERFCX_NO_REM)
    if key not in _ERFT:
        T = _load_erfcx()
        CT = np.ascontiguousarray(T['c_hi'][:deg + 1].T)
        EE = _erfcx_bound(deg) if ERFCX_NO_REM else up(_erfcx_bound(deg) + T['rem'])
        _ERFT[key] = (CT, EE)
    return _ERFT[key]
def _asy_bound(KA):
    key = ('asy', KA, RN_ONLY)
    if key not in _ERB:
        T = _load_erfcx(); a = T['asy_coef']
        S = _sum_up([up(abs(float(a[m]))*2.0**(-9*m)) for m in range(KA)])     # z ≤ 1/(2·16²) = 2⁻⁹
        g = 0.0 if RN_ONLY else up(_gamma_up(2*(KA - 1))*S)
        _ERB[key] = up(g + 2.0**-1000)
    return _ERB[key]
def erfcx_pt(x):
    # 点 x（配列、x ≥ 0）の erfcx の区間
    T = _load_erfcx(); g = float(T['g']); X1 = float(T['X1']); K = int(T['K'])
    x = np.asarray(x, float); lo = np.empty(x.shape); hi = np.empty(x.shape)
    assert np.all(x >= 0.0)
    sm = x < X1
    if sm.any():
        xs = x[sm]; k = np.rint(xs/g).astype(np.int64); d = xs - k*g      # 丸め無し（Sterbenz、k·g は 2 の冪の倍）
        deg = K if ERFCX_DEG_OVERRIDE is None else ERFCX_DEG_OVERRIDE
        e = 0.0 if ERFCX_NO_REM else T['rem'][k]
        if POLY == 'fast':
            # 第905便：浮動の Horner（係数は上端）＋節点ごとの誤差の上界 Eb_k（_erfcx_bound、|d| ≤ g/2）
            CT, EE = _erfcx_fasttab(deg)
            c = np.take(CT, k, axis=0)                  # (点の数, deg+1)：一度に引く
            q = c[:, deg].copy()
            for nn in range(deg - 1, -1, -1):
                q = q*d + c[:, nn]
            E = EE[k]                                   # Eb_k ＋ 剰余_k の上界
            lo[sm] = dn(q - E); hi[sm] = up(q + E)
        else:
            q = (T['c_lo'][deg][k], T['c_hi'][deg][k])
            for nn in range(deg - 1, -1, -1):
                q = mul_ip(q, d); q = add(q, (T['c_lo'][nn][k], T['c_hi'][nn][k]))
            lo[sm] = dn(q[0] - e); hi[sm] = up(q[1] + e)
    bg = ~sm
    if bg.any():
        xb = x[bg]
        x2 = mul_pp(xb, xb)
        z = (dn(1.0/up(2.0*x2[1])), up(1.0/dn(2.0*x2[0])))   # 1/(2x²)
        KA = int(T['KA']); a = T['asy_coef']   # a_m = (−1)^m (2m−1)!!、m = 0..KA−1（丸めの無い整数）
        R = 0.0 if ERFCX_NO_REM else float(T['asy_rem'])     # 0 ≤ R_KA ≤ (2KA−1)!!/(2x²)^KA ≤ asy_rem（x ≥ X1、KA は偶数）
        if POLY == 'fast':
            # 第905便：q(z) = Σ a_m z^m は z ∈ [0, 1/512] で減少（q′(z) ≤ −1 + Σ_{m≥2} m(2m−1)!! 512^{1−m} < −0.98、［証］）。
            # 下界は z の上端、上界は z の下端で浮動の Horner、誤差 ≤ γ_{2(KA−1)}·Σ|a_m|512^{−m}（≤ 1.0021）＋2⁻¹⁰⁰⁰。
            qa = np.full(xb.shape, a[KA-1]); qb = np.full(xb.shape, a[KA-1])
            for mm in range(KA - 2, -1, -1):
                qa = qa*z[1] + a[mm]; qb = qb*z[0] + a[mm]
            Eb = _asy_bound(KA)
            q = (dn(qa - Eb), up(up(qb + Eb) + R))
        else:
            q = (np.full(xb.shape, a[KA-1]), np.full(xb.shape, a[KA-1]))
            for mm in range(KA - 2, -1, -1):
                q = mul_iz(q, z); q = add(q, (a[mm], a[mm]))
            q = (q[0], up(q[1] + R))
        den = mul_ip(SQRTPI, xb)                               # x√π
        v = div_pos(q, den)
        lo[bg] = v[0]; hi[bg] = v[1]
    return lo, hi
def erfcx_dec(x):
    # 区間 x ⊂ [0, ∞) の erfcx（減少関数）
    a = erfcx_pt(np.maximum(x[1], 0.0))[0]; b = erfcx_pt(np.maximum(x[0], 0.0))[1]
    return a, b
# ---- 小さい |x| の erf（|x| ≤ 0.3） ----
_ERFS_C = [(-1.0)**n/float(math.factorial(n)*(2*n+1)) for n in range(9)]   # 最近接の c̃_n（|c̃_n − c_n| ≤ u|c̃_n|·(1+2⁻⁵²)）
_ERFS_B = {}
def _erfs_bound():
    # q8(s) = Σ_{n≤8} c_n s^n（s = x² ≤ 0.0901）の浮動の Horner の誤差：γ_16·Σ|c̃_n|s^n ＋ Σ|c̃_n − c_n|s^n ＋ 2⁻¹⁰⁰⁰
    if RN_ONLY not in _ERFS_B:
        S = _sum_up([up(abs(c)*0.0901**n*(1.0 + 2.0**-40)) for n, c in enumerate(_ERFS_C)])
        g = 0.0 if RN_ONLY else up(_gamma_up(16)*S)
        w = 0.0 if RN_ONLY else up(S*U*(1.0 + 2.0**-40))
        _ERFS_B[RN_ONLY] = _sum_up([g, w, 2.0**-1000])
    return _ERFS_B[RN_ONLY]
def _erf_small_pos(x, side):
    if POLY == 'fast': return _erf_small_pos_fast(x, side)
    return _erf_small_pos_iv(x, side)
def _erf_small_pos_fast(x, side):
    # 第905便：q8 は s ∈ [0, 0.09] で減少（q8′(s) ≤ −1/3 + 2s/10 < 0、交代で項が減る）。下界は s の上端、上界は s の下端で浮動の Horner。
    x = np.asarray(x, float); s = x*x
    sv = up(s) if side < 0 else dn(s)
    sv = np.maximum(sv, 0.0)
    q = np.full(x.shape, _ERFS_C[8])
    for n in range(7, -1, -1):
        q = q*sv + _ERFS_C[n]
    E = _erfs_bound()
    s1 = up(s); s2 = up(s1*s1); s4 = up(s2*s2); s8 = up(s4*s4)
    r = up(up(up(s8*s1)*x)/float(math.factorial(9)*19))  # 最初の捨てた項 x^19/(9!·19) の上界（x ≥ 0、全て上向き）
    if side < 0:
        v = dn(dn(x*dn(q - E)) - r); return np.maximum(dn(v*TWO_OVER_SQRTPI[0]), 0.0)
    v = up(up(x*up(q + E)) + r); return up(v*TWO_OVER_SQRTPI[1])
def _erf_small_pos_iv(x, side):
    # x ≥ 0 の点、交代級数 (2/√π)Σ(−1)^n x^{2n+1}/(n!(2n+1))、n ≤ 8、剰余 ≤ 最初の捨てた項
    x2 = mul_pp(x, x); S = (np.zeros(x.shape), np.zeros(x.shape))
    # Horner：x Σ c_n (x²)^n
    cn = [((-1.0)**n, float(math.factorial(n)*(2*n+1))) for n in range(9)]
    q = div_pp(cn[8][0], cn[8][1])
    q = (np.full(x.shape, q[0]), np.full(x.shape, q[1]))
    for n in range(7, -1, -1):
        q = mul_iz(q, x2)
        c = div_pp(cn[n][0], cn[n][1]); q = add(q, c)
    q = mul_ip(q, x)
    r = up(ipow_up(x, 19)/float(math.factorial(9)*19))   # 最初の捨てた項 x^19/(9!·19)
    q = (dn(q[0] - r), up(q[1] + r))
    v = mul_iz(q, TWO_OVER_SQRTPI)
    return v[0] if side < 0 else v[1]
def erf_small(x):
    # 区間 x ⊂ [−0.3, 0.3] の erf（増加関数）
    xl, xh = x
    assert np.all(np.abs(xl) <= 0.3) and np.all(np.abs(xh) <= 0.3)
    lo = np.where(xl >= 0, _erf_small_pos(np.abs(xl), -1), -_erf_small_pos(np.abs(xl), +1))
    hi = np.where(xh >= 0, _erf_small_pos(np.abs(xh), +1), -_erf_small_pos(np.abs(xh), -1))
    return lo, hi

# ---- erf(x)、x ≥ 0 の点（任意の大きさ）：x ≤ 0.3 は級数、それより大きいと 1 − erfcx(x)·e^{−x²} ----
def _erf_pos(x, side):
    x = np.asarray(x, float); out = np.empty(x.shape)
    sm = x <= 0.3
    if sm.any(): out[sm] = _erf_small_pos(x[sm], side)
    bg = ~sm
    if bg.any():
        xb = x[bg]; e = erfcx_pt(xb); q = mul_pp(xb, xb); E = exp_iv((-q[1], -q[0]))
        p = mul_pos(e, E)
        out[bg] = dn(1.0 - p[1]) if side < 0 else up(1.0 - p[0])
    return out
def erf_any(x):
    # 区間 x の erf（増加・奇関数）
    xl, xh = x
    lo = np.where(xl >= 0, _erf_pos(np.abs(xl), -1), -_erf_pos(np.abs(xl), +1))
    hi = np.where(xh >= 0, _erf_pos(np.abs(xh), +1), -_erf_pos(np.abs(xh), -1))
    return lo, hi
# ---- h(y) = 1/(1−e^{−y}) − 1/y（[0,1] の上の密度 ∝ e^{yx} の平均、増加関数） ----
_BER = [1/6, -1/30, 1/42, -1/30, 5/66]     # B_{2k}
def _h_pt(y, side):
    # 点 y（配列）。side −1：下界、+1：上界
    y = np.asarray(y, float); out = np.empty(y.shape)
    ay = np.abs(y); neg_ = y < 0
    # h(−y) = 1 − h(y)：|y| で計算して、負なら 1 − (逆向きの側)
    def hpos(a, sd):
        res = np.empty(a.shape)
        sm = a < 0.5
        if sm.any():
            v = a[sm]
            s = (np.full(v.shape, 0.5), np.full(v.shape, 0.5))
            pw = (v, v)
            for k, B in enumerate(_BER, start=1):
                num, den = (B.as_integer_ratio())
                cB = div_pp(float(num), float(den)*float(math.factorial(2*k)))
                term = mul(cB, pw)
                s = add(s, term)
                pw = mul_pos(pw, mul_pp(v, v))
            # 剰余：|B_{2k}|/(2k)! = 2ζ(2k)/(2π)^{2k}、Σ_{k≥6} ≤ 2.0005·|y|^{11}/(2π)^{12}/(1 − (1/4π)²) ≤ 5.4·10⁻¹⁰|y|^{11}
            r = up(ipow_up(v, 11)*6e-10)
            res[sm] = dn(s[0] - r) if sd < 0 else up(s[1] + r)
        bg = ~sm
        if bg.any():
            v = a[bg]
            E = exp_iv((-v, -v))                    # e^{−y} ∈ [E_lo, E_hi]
            # 1/(1−E) は E について増加、1/y
            A = (dn(1.0/up(1.0 - E[0])), up(1.0/dn(1.0 - E[1])))
            B = div_pp(1.0, v)
            res[bg] = dn(A[0] - B[1]) if sd < 0 else up(A[1] - B[0])
        return res
    pos = ~neg_
    if pos.any(): out[pos] = hpos(ay[pos], side)
    if neg_.any():
        o = hpos(ay[neg_], -side)
        out[neg_] = dn(1.0 - o) if side < 0 else up(1.0 - o)
    return out
def hfun_iv(y):
    return _h_pt(y[0], -1), _h_pt(y[1], +1)

# ---- h(y) の速い版：格子 y_k = kΔ（Δ = 1/256、|y| ≤ 64）の上の区間の値の表と単調性、|y| > 64 は 1 − 1/y ≤ h ≤ 1 − 1/y + 10⁻²⁷ ----
# 幅の損は h′ ≤ 1/12 から ≤ Δ/12（平均のずれにだけ効く）。
_HT = None; _HD = 1.0/256; _HY = 64.0
def _htab():
    global _HT
    if _HT is None:
        k = np.arange(-int(_HY/_HD), int(_HY/_HD) + 1, dtype=float)*_HD
        _HT = (k, _h_pt(k, -1), _h_pt(k, +1))
    return _HT
def _h_fast(y, side):
    k, tl, th = _htab(); y = np.asarray(y, float); out = np.empty(y.shape)
    mid = np.abs(y) <= _HY
    if mid.any():
        q = y[mid]/_HD                                     # 丸め無し（2 の冪で割る）
        i = (np.floor(q) if side < 0 else np.ceil(q)).astype(np.int64) + int(_HY/_HD)
        out[mid] = tl[i] if side < 0 else th[i]
    big = y > _HY
    if big.any():
        r = div_pp(1.0, y[big]); out[big] = dn(1.0 - r[1]) if side < 0 else up(up(1.0 - r[0]) + 1e-27)
    sm = y < -_HY
    if sm.any():
        a = -y[sm]; r = div_pp(1.0, a)                     # h(y) = 1 − h(−y)
        out[sm] = dn(dn(r[0]) - 1e-27) if side < 0 else up(r[1])
    return out
def hfun_fast(y):
    return _h_fast(y[0], -1), _h_fast(y[1], +1)
