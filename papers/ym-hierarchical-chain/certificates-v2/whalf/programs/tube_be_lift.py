# Part (ii) of Proposition 5.2 for T: for every point of the tube D_T = {c_n <= up_n(s) (2<=n<=K), tail t <= T0} with s in [0, smax],
# the rigorous kappa lower bound (with tail, kappa_lower(c,t), Lemma A.3) is > 0.  Rigorous envelopes (envelope.py).
import sys, numpy as np, mpmath as mp
import os as _os; HERE=_os.path.dirname(_os.path.abspath(__file__))   # the programs read each other from this directory
from mpmath import iv
sys.argv=[sys.argv[0],'20','2','25']+sys.argv[1:]
src=open(_os.path.join(HERE,'mk_tail_cert.py')).read().split("def run(beta):")[0]
exec(src); _kl_tail=kappa_lower; _K=K
exec(open(_os.path.join(HERE,'tube_cap4.py')).read().split("def mul(a,b):")[0]); kappa_lower=_kl_tail; K=_K; assert J==K
exec(open(_os.path.join(HERE,'envelope.py')).read())
T0=mp.mpf('1e-15'); smax=float(sys.argv[4])
edges=[0.0,1e-3]+list(np.geomspace(1e-3,smax,80)[1:]); bad=[]; worst=None
for a,b in zip(edges[:-1],edges[1:]):
    U=up_max(a,b); B=[iv.mpf(1),iv.mpf([a,b])]+[iv.mpf([0,U[n]]) for n in range(2,K+1)]
    kl=kappa_lower(B,T0)
    v=None if kl is None else float(kl.a)
    if v is None or v<=0: bad.append((a,b,v))
    worst=v if worst is None or (v is not None and v<worst) else worst
print(f"BE-lift s in [0,{smax}]: cells={len(edges)-1} failures={bad[:5]} min kappa_lower={worst}",flush=True)
