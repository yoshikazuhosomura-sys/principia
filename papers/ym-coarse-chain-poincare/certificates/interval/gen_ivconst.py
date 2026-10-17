# 第904便：区間演算の定数（mpmath の iv、600 ビット）を外向きに倍精度へ丸めて ivconst.npz に書く。
import sys, math, numpy as np
pass  # (a local site-packages path was appended here when run)
import mpmath
from mpmath import iv, mpf
iv.prec = 600; mpmath.mp.prec = 600
def outward(x):
    a, b = x.a, x.b
    lo = float(a); hi = float(b)
    if mpf(lo) > a: lo = float(np.nextafter(lo, -np.inf))
    if mpf(hi) < b: hi = float(np.nextafter(hi, np.inf))
    assert mpf(lo) <= a and mpf(hi) >= b
    return lo, hi
out = {}
def put(name, x):
    lo, hi = outward(x); out[name + '_lo'] = lo; out[name + '_hi'] = hi
ln2 = iv.log(iv.mpf(2))
l64 = ln2/64
mid = float(mpmath.mpf(l64.a))
c1 = math.floor(mid*2.0**38)/2.0**38            # 32 ビット以内
assert c1*2**38 < 2**32
out['ln2_64_c1'] = c1
put('ln2_64_c2', l64 - iv.mpf(c1))
out['inv_ln2_64'] = float(mpmath.mpf(64)/mpmath.log(2))
lo = []; hi = []
for j in range(64):
    a, b = outward(iv.exp(ln2*j/64)); lo.append(a); hi.append(b)
out['t64_lo'] = np.array(lo); out['t64_hi'] = np.array(hi)
put('sqrtpi', iv.sqrt(iv.pi)); put('two_over_sqrtpi', 2/iv.sqrt(iv.pi))
for k in range(8): put('invfact%d' % k, iv.mpf(1)/math.factorial(k))
R = iv.mpf('0.0060')
rem = R**7/math.factorial(7)*iv.exp(R)
out['exp_rem'] = outward(rem)[1]
np.savez('ivconst.npz', **out)
print('ok', {k: v for k, v in out.items() if not k.startswith('t64')})
