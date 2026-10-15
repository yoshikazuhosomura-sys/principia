# 丸めの監査（別の経路）：証明書（psiP）の細胞の質量 log I と細胞の中の平均のずれの上下を、
# mpmath（40 桁）の数値積分（erf の式を使わない）と比べる。結論文は印字しない。数だけ。
import sys, os, math, random, glob, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import mpmath  # noqa: F401
except ImportError:
    sys.exit('audit3.py needs the mpmath package (pip install mpmath)')
from mpmath import mp, mpf, quad, exp, log
from psiP import make_cells, backward, law_rows, cells, vprime_range, EPS, XC
mp.dps = 40
def audit(h, c1, N, blo, bhi, nsamp, seed):
    random.seed(seed)
    t = make_cells(h, -XC, 0.0, c1, c2=20.0); n = len(t)-1; lam = 1.0/(EPS*h)
    P = {'lam0': lam, 'dl': (0.0, 0.0), 'lamr': (lam, lam), 'vr': vprime_range(t)}
    sites = backward(t, P, N, blo, bhi, max(8, int(4e5//n)))
    bad = 0; worst = 0.0; worstd = 0.0; cnt = 0
    for k in range(nsamp):
        i = random.randrange(N); st = sites[i]; sign = random.choice([-1, 1])
        if sign < 0 and st.lo_delta: continue
        u = np.array([float(t[random.randrange(n+1)])])
        s, e = law_rows(P, t, st, u, sign); lIm, lIp, dlo, dhi = cells(t, lam, u, s, e)
        # 質量の大きい細胞を半分、無作為を半分
        j = int(np.argmax(lIp[0])) if k % 2 == 0 else random.randrange(n)
        j = min(n-1, max(0, j + random.choice([-1, 0, 1])))
        tj = mpf(float(t[j])); w = mpf(float(t[j+1])) - tj; L = mpf(lam)
        E0 = L*mpf(float(u[0]))*tj - L*tj*tj + mpf(float(e[0, j]))
        beta = L*mpf(float(u[0])) - 2*L*tj + mpf(float(s[0, j]))
        f = lambda x: exp(beta*x - L*x*x)
        I0 = quad(f, [0, w/4, w/2, 3*w/4, w]); I1 = quad(lambda x: x*f(x), [0, w/4, w/2, 3*w/4, w])
        lI = E0 + log(I0); d = I1/I0
        a1, a2 = mpf(float(lIm[0, j])), mpf(float(lIp[0, j]))
        ok = (a1 <= lI <= a2) and (mpf(float(dlo[0, j])) <= d <= mpf(float(dhi[0, j])))
        cnt += 1
        if not ok:
            bad += 1
            print(f"  VIOLATION site={i+1} sign={sign} u={float(u[0]):.6f} cell={j}: exact={mp.nstr(lI, 15)} bounds=[{float(lIm[0,j]):.15g},{float(lIp[0,j]):.15g}] d={mp.nstr(d, 8)} in [{float(dlo[0,j]):.8g},{float(dhi[0,j]):.8g}]", flush=True)
        worst = max(worst, float((a2 - a1)/2))
        worstd = max(worstd, float((mpf(float(dhi[0, j])) - mpf(float(dlo[0, j])))/w))
    print(f"audit h={h} c1={c1} N={N} b=[{blo},{bhi}] n={n} samples={cnt}: violations={bad} max half-margin(log)={worst:.3e} max (dhi-dlo)/w={worstd:.3e}", flush=True)
if __name__ == '__main__':
    audit(1e-5, 0.25, 8, -1.02, -0.96, 150, 1)
    audit(1e-5, 0.25, 15, -0.01, 0.0, 150, 2)
    audit(0.035, 0.015, 15, -0.01, 0.0, 150, 3)
    audit(1e-3, 0.04, 9, None, -XC, 150, 4)
