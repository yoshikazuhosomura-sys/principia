# Rigorous enclosure of the UNTRUNCATED MK map T (SU(2), d=4, b=2) along Wilson orbits.
# Finite part plus tail bound, as in Lemma A.2 of the paper.
# State per step: interval enclosures of c_n (n<=K) + tail bound t >= sum_{n>K} (n+1) c_n chi_n(rho').
# Usage: python3 -I mk_tail_cert.py K rho' dps   (defaults 60 2 60)
import sys
import mpmath as mp
from mpmath import iv
K = int(sys.argv[1]) if len(sys.argv) > 1 else 60
RHO = mp.mpf(sys.argv[2]) if len(sys.argv) > 2 else mp.mpf(2)
DPS = int(sys.argv[3]) if len(sys.argv) > 3 else 60
mp.mp.dps = DPS; iv.dps = DPS
rho = iv.mpf(RHO)

def chi(n, r):  # chi_n(r) = sum_{k=0}^n r^(n-2k)
    return sum(r ** (n - 2 * k) for k in range(n + 1))
chiR = [chi(n, rho) for n in range(K + 2)]

def besselI(nu, x):  # rigorous enclosure of I_nu(x), x>0 interval: power series + geometric remainder
    x = iv.mpf(x); x2 = (x / 2) ** 2
    term = (x / 2) ** nu / iv.mpf(mp.factorial(nu)); s = iv.mpf(0); k = 0
    while True:
        s += term; k += 1; term = term * x2 / (k * (k + nu))
        r = x2.b / ((k + 1) * (k + 1 + nu))
        if r <= 0.5 and term.b < mp.mpf(10) ** (-(DPS + 10)) * s.a:
            break
    return s + iv.mpf([0, 2 * term.b])  # remaining terms <= term*(1+r+r^2+...) <= 2*term

def mul(a, b, top):  # (a*b)_m for m<=top, Clebsch-Gordan: chi_i chi_j = sum_{c=|i-j|, step 2}^{i+j} chi_c
    out = [iv.mpf(0)] * (top + 1)
    for i in range(len(a)):
        for j in range(len(b)):
            lo = abs(i - j)
            if lo > top: continue
            p = a[i] * b[j]
            for c in range(lo, min(i + j, top) + 1, 2): out[c] += p
    return out

def step(c, t):
    a = [(n + 1) * c[n] for n in range(K + 1)]
    hf = mul(a, a, 2 * K); h = hf[:K + 1]; G = mul(h, h, K)   # h = P_K(a^ * a^), G = P_K(h*h) (truncated products)
    F1 = sum((n + 1) * a[n] for n in range(K + 1))
    Fr = sum(a[n] * chiR[n] for n in range(K + 1))
    M1h = sum((n + 1) * h[n] for n in range(K + 1))
    tau_h = sum((n + 1) * hf[n] for n in range(K + 1, 2 * K + 1))   # M_1 of the dropped modes of a^*a^
    # Delta >= M_1(a)^4 - M_1(h)^2 = [M_1(a)^4 - M_1(a^)^4] + [(M_1(h)+tau_h)^2 - M_1(h)^2]  (no cancellation)
    D = (4 * (F1 + t) ** 3 * t + 2 * M1h * tau_h + tau_h ** 2).b
    g = [iv.mpf([G[m].a, G[m].b + D / (m + 1)]) for m in range(K + 1)]
    cp = [g[m] / ((m + 1) * g[0]) for m in range(K + 1)]
    cn = [x ** 4 for x in cp]; cn[0] = iv.mpf(1)
    Mg = ((Fr + t) ** 4).b
    S = (iv.mpf(1) / (K + 2) ** 3 * rho ** (-3 * (K + 1)) / (1 - rho ** (-3))).b
    tn = (Mg / g[0].a) ** 4 * S
    return cn, tn, D

def Fv(c, t):
    fp = sum((n + 1) ** 2 * c[n] for n in range(K + 1)) + iv.mpf([0, t])
    fm = sum((-1) ** n * (n + 1) ** 2 * c[n] for n in range(K + 1)) + iv.mpf([-t, t])
    return iv.log(fp / fm)

p1 = lambda n: iv.mpf(n * (n + 1) * (n + 2)) / 3
p2 = lambda n: iv.mpf((n - 1) * n * (n + 1) * (n + 2) * (n + 3)) / 15
# n>K: p_i(n+1)/p_i(n) <= (K/(K-1))^5 < rho' <= chi_{n+1}/chi_n, so sup_{n>K} p_i(n)/chi_n = value at K+1
assert (mp.mpf(K) / (K - 1)) ** 5 < RHO
w1 = (p1(K + 1) / chiR[K + 1]).b; w2 = (p2(K + 1) / chiR[K + 1]).b

def kappa_lower(c, t):
    fmin = 1 - (sum((n + 1) ** 2 * c[n] for n in range(1, K + 1)) + iv.mpf([0, t]))
    if fmin.a <= 0: return None
    d1 = sum((n + 1) * c[n] * p1(n) for n in range(1, K + 1)) + iv.mpf([0, t * w1])
    d2 = sum((n + 1) * c[n] * p2(n) for n in range(2, K + 1)) + iv.mpf([0, t * w2])
    g1 = d1 / fmin; g2 = d2 / fmin + g1 ** 2
    return 1 - 12 * (g1 + g2)

def run(beta):
    B = iv.mpf(beta); I1 = besselI(1, B)
    c = [iv.mpf(1)] + [besselI(n + 1, B) / I1 for n in range(1, K + 1)]
    Mtot = B / (2 * I1) * iv.exp(B * (rho + 1 / rho) / 2)      # closed form M_rho'(a^(0))
    t = (Mtot - sum((n + 1) * c[n] * chiR[n] for n in range(K + 1))).b
    F = [Fv(c, t)]; tails = [t]; Ds = []; kl = None; s = 0; c1chk = None
    while s < 30:
        c, t, D = step(c, t); s += 1; F.append(Fv(c, t)); tails.append(t); Ds.append(D)
        if s == 1:  # exact check: c^(1)_n = (I_{n+1}(4b)/I_1(4b))^4
            I14 = besselI(1, 4 * B)
            ex = [(besselI(n + 1, 4 * B) / I14) ** 4 for n in range(1, 6)]
            c1chk = all(not (ex[i].b < c[i + 1].a or ex[i].a > c[i + 1].b) for i in range(5))
        kl = kappa_lower(c, t)
        if kl is not None and kl.a > 0: break
    dec = [F[i + 1].b < F[i].a for i in range(len(F) - 1)]
    first = min(i for i in range(len(dec)) if all(dec[i:]))
    return dict(beta=beta, steps=s, F=F, first=first, kappa=kl, tails=tails, Ds=Ds, c=c, c1chk=c1chk)

def num(x):  # endpoint value for printing (mpmath>=1.4 returns degenerate intervals for .a/.b)
    s = str(x)
    return mp.mpf(s[1:].split(',')[0]) if s.startswith('[') else mp.mpf(s)

if __name__ == "__main__":
    print(f"K={K} rho'={RHO} dps={DPS}")
    for beta in sys.argv[4].split(',') if len(sys.argv) > 4 else ['2.0', '2.3', '2.6']:
        try:
            r = run(beta)
        except Exception as e:
            print(f"beta={beta}: enclosure lost ({type(e).__name__}) -> increase K"); continue
        print(f"beta={beta}: steps={r['steps']}  step-1 exact Bessel check: {r['c1chk']}")
        print("  F_v(T^k c0) lower end / width: " + "; ".join(f"k={k}: {mp.nstr(num(f.a), 12)} / {mp.nstr(num(f.b) - num(f.a), 2)}" for k, f in enumerate(r['F'])))
        print(f"  F_v strictly decreasing (certified, for T) from step {r['first']} to {r['steps']}")
        print(f"  kappa(T^{r['steps']} c0) >= {mp.nstr(num(r['kappa'].a), 12)}   (width of enclosure {mp.nstr(num(r['kappa'].b) - num(r['kappa'].a), 2)})")
        print("  tail bounds t_k: " + " ".join(mp.nstr(num(x), 2) for x in r['tails']))
        print("  Delta_k: " + " ".join(mp.nstr(num(x), 2) for x in r['Ds']))
