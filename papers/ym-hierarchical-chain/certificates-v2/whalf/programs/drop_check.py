# Decrease of the cell index for W-half(T): for each cell [s_k, s_{k+1}] of the original logs, enclose the image
# coordinate a'_1 over the whole cell box (a_1 in the cell, 0 <= a_n <= upper envelope, tail 1e-15) in ONE box
# with the same enclosure of T as tube_lift.py, and check that its upper end is below s_k.
# usage: python3 drop_check.py LO HI REL   (same cell grid as tube_lift.py)
import sys, numpy as np, mpmath as mp
import os as _os; HERE=_os.path.dirname(_os.path.abspath(__file__))   # the programs read each other from this directory
from mpmath import iv
sys.argv=[sys.argv[0],'20','2','25']+sys.argv[1:]
src=open(_os.path.join(HERE,'mk_tail_cert.py')).read().split("def run(beta):")[0]
exec(src)
args=sys.argv[4:]; lo,hi,rel=float(args[0]),float(args[1]),float(args[2]); T0=mp.mpf('1e-15')
_kl_tail=kappa_lower; _K=K
exec(open(_os.path.join(HERE,'tube_cap4.py')).read().split("def mul(a,b):")[0])
kappa_lower=_kl_tail; K=_K; assert J==K
exec(open(_os.path.join(HERE,'envelope.py')).read())
s=lo; n=0; bad=[]; worst=0.0
while s<hi:
    s2=min(s*(1+rel),hi); U=up_max(s,s2)
    B=[iv.mpf(1),iv.mpf([s,s2])]+[iv.mpf([0,U[k]]) for k in range(2,K+1)]
    cn,tn,D=step(B,T0); t1b=float(cn[1].b); r=t1b/s; worst=max(worst,r); n+=1
    ok = t1b < s
    print(f"cell {s:.5f} image_a1_upper={t1b:.6g} ratio={r:.6f} ok={ok}",flush=True)
    if not ok: bad.append(round(s,5))
    s=s2
print(f"DROP [{lo},{hi}] cells={n} largest ratio={worst:.6f} failures={bad}",flush=True)
