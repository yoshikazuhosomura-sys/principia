# 第904便：区間演算の部品の検査（包含の検査）。参照は mpmath 60 桁（検査の参照であって証明の部品ではない）と Fraction（和、丸め無し）。
# 使い方：test_ivx.py [ok|rn|exp2|erfcx3|sumplain] — 陰性対照は部品を壊して、包含の違反が出ることを見る。
import sys, os, math, random, numpy as np
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
pass  # (a local site-packages path was appended here when run)
import mpmath
mpmath.mp.dps = 60
import ivx
mode = sys.argv[1] if len(sys.argv) > 1 else 'ok'
if mode == 'rn': ivx.RN_ONLY = True
if mode == 'exp2': ivx.EXP_DEG_OVERRIDE = 2; ivx.EXP_NO_REM = True
if mode == 'erfcx3': ivx.ERFCX_DEG_OVERRIDE = 3; ivx.ERFCX_NO_REM = True
rng = np.random.default_rng(904)
mf = mpmath.mpf
def chk(name, lo, hi, xs, f):
    bad = 0; worst = 0.0
    for x, a, b in zip(xs, lo, hi):
        v = f(mf(float(x)))
        if not (mf(float(a)) <= v <= mf(float(b))): bad += 1
        if v != 0: worst = max(worst, float((mf(float(b)) - mf(float(a)))/abs(v)))
    print(f"{mode:8s} {name:10s} n={len(xs)} violations={bad} max_rel_width={worst:.2e}")
    return bad
tot = 0
# exp：[-745, 709] と小さい引数
xs = np.concatenate([rng.uniform(-745, 709, 3000), rng.uniform(-1, 1, 3000), rng.uniform(-1e-3, 1e-3, 1000)])
lo, hi = ivx.exp_iv((xs, xs)); tot += chk('exp', lo, hi, xs, mpmath.exp)
# erfcx：[0,16) の表と [16, 500] の漸近
xs = np.concatenate([rng.uniform(0, 16, 4000), rng.uniform(16, 500, 1500), np.array([0.0, 1/64, 15.999, 16.0])])
lo, hi = ivx.erfcx_pt(xs); tot += chk('erfcx', lo, hi, xs, lambda x: mpmath.exp(x*x)*mpmath.erfc(x))
# erf の小さい引数
xs = rng.uniform(-0.3, 0.3, 3000)
lo, hi = ivx.erf_small((xs, xs)); tot += chk('erf_small', lo, hi, xs, mpmath.erf)
xs = rng.uniform(-6, 6, 3000)
lo, hi = ivx.erf_any((xs, xs)); tot += chk('erf_any', lo, hi, xs, mpmath.erf)
# h(y)
xs = np.concatenate([rng.uniform(-60, 60, 2000), rng.uniform(-0.6, 0.6, 2000), rng.uniform(-1e-4, 1e-4, 500)])
lo, hi = ivx.hfun_iv((xs, xs))
tot += chk('hfun', lo, hi, xs, lambda y: (1/(1 - mpmath.exp(-y)) - 1/y) if y != 0 else mf(1)/2)
lo, hi = ivx.hfun_fast((xs, xs))
tot += chk('hfun_fast', lo, hi, xs, lambda y: (1/(1 - mpmath.exp(-y)) - 1/y) if y != 0 else mf(1)/2)
xs2 = np.concatenate([rng.uniform(60, 3000, 500), -rng.uniform(60, 3000, 500)])
lo, hi = ivx.hfun_fast((xs2, xs2)); tot += chk('hfun_big', lo, hi, xs2, lambda y: (1/(1 - mpmath.exp(-y)) - 1/y))
# 和（Fraction で誤差なしで）
bad = 0
for trial in range(40):
    n = int(rng.integers(50, 3000))
    x = rng.uniform(0, 1, n)*10.0**rng.uniform(-5, 5, n)
    sl = ivx.cumsum_nn(x[None, :], 1, -1)[0]; sh = ivx.cumsum_nn(x[None, :], 1, +1)[0]
    S = Fraction(0)
    for j in range(n):
        S += Fraction(float(x[j]))
        if not (Fraction(float(sl[j])) <= S <= Fraction(float(sh[j]))): bad += 1
    y = rng.normal(0, 1, n)*10.0**rng.uniform(-3, 3, n)
    sl = ivx.cumsum_signed(y[None, :], 1, -1)[0]; sh = ivx.cumsum_signed(y[None, :], 1, +1)[0]
    S = Fraction(0)
    for j in range(n):
        S += Fraction(float(y[j]))
        if not (Fraction(float(sl[j])) <= S <= Fraction(float(sh[j]))): bad += 1
    tl = ivx.sum_nn(x[None, :], 1, -1)[0]; th = ivx.sum_nn(x[None, :], 1, +1)[0]
    S = sum(Fraction(float(v)) for v in x)
    if not (Fraction(float(tl)) <= S <= Fraction(float(th))): bad += 1
print(f"{mode:8s} {'sums':10s} trials=40 violations={bad}")
tot += bad
# 五つの演算（無作為の点で Fraction と）
bad = 0
a = rng.normal(0, 1, 5000)*10.0**rng.uniform(-30, 30, 5000); b = rng.normal(0, 1, 5000)*10.0**rng.uniform(-30, 30, 5000)
for op, f, g in (('add', ivx.add_pp, lambda p, q: p + q), ('mul', ivx.mul_pp, lambda p, q: p*q), ('div', ivx.div_pp, lambda p, q: p/q)):
    lo, hi = f(a, b)
    for p, q, l, h in zip(a, b, lo, hi):
        v = g(Fraction(float(p)), Fraction(float(q)))
        if not (Fraction(float(l)) <= v <= Fraction(float(h))): bad += 1
print(f"{mode:8s} {'ops':10s} n=15000 violations={bad}")
tot += bad
print(f"{mode} TOTAL violations={tot}")
