# 第904便：erfcx の表（mpmath の iv、700 ビット）。節点 x_k = k·g（g = 1/32、k = 0..512、X1 = 16）。
# y = erfcx。y(x) = e^{x²} − (2/√π) Σ_{n≥0} 2^n x^{2n+1}/(2n+1)!!（正の項の級数、比 2x²/(2n+3) ≤ 1/2 から先の尾 ≤ 最後の項）。
# 導関数：y′ = 2xy − 2/√π、y^{(n+1)} = 2x y^{(n)} + 2n y^{(n−1)}。y(x) = (2/√π)∫_0^∞ e^{−t²−2xt}dt は完全単調なので
# |y^{(K+1)}| は x について減少：節点の細胞 [x_k − g/2, x_k + g/2] での最大は左端。剰余 ≤ |y^{(K+1)}(x_k − g/2)|/(K+1)!·(g/2)^{K+1}。
# 大きい x（≥ X1）の漸近級数の係数と剰余の上界も書く。
import sys, math, time, numpy as np
pass  # (a local site-packages path was appended here when run)
import mpmath
from mpmath import iv, mpf
from gen_ivconst import outward
iv.prec = 700
g = 1/32; X1 = 16.0; K = 8; KA = 10
SP = 2/iv.sqrt(iv.pi)
def erfcx_iv(x):
    x = iv.mpf(x); x2 = x*x
    if x == 0: return iv.mpf(1)
    t = x; S = iv.mpf(0); n = 0
    while True:
        S += t
        r = 2*x2/(2*n + 3)
        if n > 2*float(mpf(x2.b)) + 5 and abs(t).b < mpf(2)**-720 * abs(S).a:
            break
        t = t*r; n += 1
    # 尾：比 ≤ 1/2 から先、Σ_{m>n} t_m ≤ t_n（t は次の項 t_{n+1} ではなく最後に足した項の比で抑える）
    tail = iv.mpf([-abs(t*r).b*2, abs(t*r).b*2])   # 符号は x の符号（両側に取る）
    return iv.exp(x2) - SP*(S + tail)
def derivs(x, y, nmax):
    x = iv.mpf(x); d = [y, 2*x*y - SP]
    for n in range(1, nmax):
        d.append(2*x*d[n] + 2*n*d[n-1])
    return d
t0 = time.time()
nk = int(X1/g)
c_lo = np.zeros((K+1, nk+1)); c_hi = np.zeros((K+1, nk+1)); rem = np.zeros(nk+1)
for k in range(nk+1):
    xk = iv.mpf(k)*iv.mpf(g)
    d = derivs(xk, erfcx_iv(xk), K)
    for n in range(K+1):
        lo, hi = outward(d[n]/math.factorial(n)); c_lo[n, k] = lo; c_hi[n, k] = hi
    xl = xk - iv.mpf(g)/2
    dl = derivs(xl, erfcx_iv(xl), K+1)
    e = abs(dl[K+1]).b/math.factorial(K+1)*(mpf(g)/2)**(K+1)
    rem[k] = outward(iv.mpf(e))[1]
    if k % 64 == 0: print(k, float(mpf(d[0].a)), float(rem[k]), round(time.time()-t0, 1), flush=True)
# 漸近：x√π·y = Σ_{m<KA} (−1)^m (2m−1)!!/(2x²)^m + R、0 ≤ R ≤ (2KA−1)!!/(2x²)^KA（KA 偶数）、x ≥ X1
df = [1]
for m in range(1, KA+1): df.append(df[-1]*(2*m - 1))
asy = np.array([(-1)**m*df[m] for m in range(KA)], float)
assert all(float(int(v)) == v for v in asy)
asy_rem = outward(iv.mpf(df[KA])/(iv.mpf(2*X1*X1))**KA)[1]
# 検算：漸近の剰余の記述と表の値を X1 で突き合わせる（参考）
np.savez('erfcx_table.npz', g=g, X1=X1, K=K, KA=KA, c_lo=c_lo, c_hi=c_hi, rem=rem, asy_coef=asy, asy_rem=asy_rem)
print('done', nk+1, 'nodes', 'max rem', rem.max(), 'asy_rem', asy_rem, 'width max rel', np.max((c_hi[0]-c_lo[0])/c_lo[0]), 'sec', round(time.time()-t0, 1))
