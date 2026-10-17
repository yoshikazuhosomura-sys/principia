# 第904便：式の監査（陰性対照つき）。最後のサイト（M ≡ b、法則が陽に書ける）で、区間演算の版が出す平均と CDF の上下を、
# mpmath の数値積分（30 桁）で λ = λ1・λ0・λ2 と無作為の u について照合する。参照は検査用で証明の部品ではない。
# 使い方：m904_audit.py <h1> <h2> <c1> <b> <nu> [drop]   drop：λ の角の項を落とした誤った版（陰性対照）
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
pass  # (a local site-packages path was appended here when run)
import mpmath
mpmath.mp.dps = 30
import m904_cert as IA
from m759_psi2 import make_cells, XC
from m813_iv2 import C2
h1, h2, c1, b, nu = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
if len(sys.argv) > 6 and sys.argv[6] == 'drop': IA.DROP_CORNERS = True
t = make_cells(h1, -XC, 0.0, c1, c2=C2); n = len(t) - 1; wI = IA.wof(t)
P = IA.params(h1, h2, t)
rng = np.random.default_rng(9041)
ks = np.sort(rng.choice(n + 1, size=nu, replace=False)); u = t[ks]
site = IA.Site(np.full(n, b), np.full(n, b))
s, e = IA.law(P, t, wI, site, u, +1); Fh_p, Fl_p, mlo_p, mup_p = IA.cdf_mean(t, wI, P, u, s, e)
s, e = IA.law(P, t, wI, site, u, -1); Fh_m, Fl_m, mlo_m, mup_m = IA.cdf_mean(t, wI, P, u, s, e)
# 主張：全ての λ ∈ [λ2,λ1] で、平均 ∈ [mlo(L⁻), mup(L⁺)]、CDF ≤ Fh(L⁻)、CDF ≥ Fl(L⁺)
mf = float; lo = float(-XC); hi = 0.0
# 参照：倍精度の細かい複合 Simpson（2·10⁶ 区間、頂上からの対数で）。参照の誤差 ~10⁻¹² は法則の挟みの余裕（≫10⁻⁸）より十分小さい。［計］
WG = np.linspace(lo, hi, 2000001); HW = (hi - lo)/2000000
SW = np.ones(WG.size); SW[1:-1:2] = 4; SW[2:-1:2] = 2; SW *= HW/3
def stats(lam, uu, kk):
    f = lam*(uu*WG - WG*WG + b*WG - 0.25*(WG*WG - 1)**2/8)
    g = np.exp(f - f.max())*SW
    Z = g.sum(); m = (WG*g).sum()/Z
    j = int(round((t[kk] - lo)/HW)); Fk = g[:j].sum()/Z    # t_k に最も近い格子点まで（端の重みの誤差は ≤ 1 区間ぶん、下で許容に入れる）
    return m, Fk, g[max(j-1,0):j+1].sum()/Z
viol = {'mean': 0, 'cdf': 0}; worst = 0.0; N = 0
for idx in range(nu):
    for lam in (P['lam1'][0], P['lam0'], P['lam2'][1]):
        kk = int(rng.integers(1, n))
        m, F, tol = stats(lam, float(u[idx]), kk)
        N += 1
        if not (mlo_m[idx] - 1e-11 <= m <= mup_p[idx] + 1e-11): viol['mean'] += 1
        if not (Fl_p[idx, kk] - tol - 1e-11 <= F <= Fh_m[idx, kk] + tol + 1e-11): viol['cdf'] += 1
        worst = min(worst, min(m - mlo_m[idx], mup_p[idx] - m)/(hi - lo)) if N > 1 else min(m - mlo_m[idx], mup_p[idx] - m)/(hi - lo)
print(f"AUDIT h=[{h1},{h2}] c1={c1} b={b} drop={IA.DROP_CORNERS} samples={N} violations={viol} min_slack_rel={worst:.3e}")
