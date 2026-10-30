# Cell test of Proposition 5.2(i) for the untruncated hierarchical map T (Lemma A.2: finite part K=20 + tail t).
import sys, numpy as np, mpmath as mp
import os as _os; HERE=_os.path.dirname(_os.path.abspath(__file__))   # the programs read each other from this directory
from mpmath import iv
sys.argv=[sys.argv[0],'20','2','25']+sys.argv[1:]
src=open(_os.path.join(HERE,'mk_tail_cert.py')).read().split("def run(beta):")[0]
exec(src)                      # defines K=20, step(c,t), kappa_lower(c,t), Fv
args=sys.argv[4:]; lo,hi,rel=float(args[0]),float(args[1]),float(args[2]); T0=mp.mpf('1e-15'); BUD=int(args[3]) if len(args)>3 else 3000
_kl_tail=kappa_lower; _K=K
exec(open(_os.path.join(HERE,'tube_cap4.py')).read().split("def mul(a,b):")[0])   # gamma, up(s), eps  (NOTE: redefines kappa_lower(c) -> restore)
kappa_lower=_kl_tail; K=_K; assert J==K
exec(open(_os.path.join(HERE,'envelope.py')).read())
def cert_box(B,t,slo):
    cn,tn,D=step(B,t)
    if tn>T0: return False
    t1a,t1b=float(cn[1].a),float(cn[1].b)
    if not t1b<slo: return False
    if t1b<=0.0165:
        kl=kappa_lower(cn,tn); return kl is not None and kl.a>0
    Ul=up_min(t1a,t1b)
    return all(float(cn[n].b)<=Ul[n] for n in range(2,K+1))
s=lo; nc=0; ok=0; fails=[]
while s<hi:
    s2=min(s*(1+rel),hi); U=up_max(s,s2)
    stack=[[iv.mpf(1),iv.mpf([s,s2])]+[iv.mpf([0,U[n]]) for n in range(2,K+1)]]; used=0; good=True
    while stack:
        B=stack.pop(); used+=1
        if used>BUD: good=False; break
        try: r=cert_box(B,T0,s)
        except (ValueError,ZeroDivisionError): r=False
        if r: continue
        best=None
        for k in range(1,6):                      # split the coordinate whose midpoint-freeze shrinks the image s' most (bisection rule)
            m=(B[k].a+B[k].b)/2; Bm=list(B); Bm[k]=iv.mpf([m,m])
            try: cm,_,_=step(Bm,T0); w=float(cm[1].b-cm[1].a)
            except (ValueError,ZeroDivisionError): w=float('inf')
            if best is None or w<best[0]: best=(w,k)
        k=best[1]; m=(B[k].a+B[k].b)/2
        B1=list(B); B2=list(B); B1[k]=iv.mpf([B[k].a,m]); B2[k]=iv.mpf([m,B[k].b]); stack+=[B1,B2]
    nc+=1; ok+=good; print(f"cell {s:.5f} ok={good} boxes={used}",flush=True)
    if not good and len(fails)<5: fails.append(round(s,4))
    s=s2
print(f"LIFTED [{lo},{hi}] cells={nc} certified={ok} fails={fails}",flush=True)
