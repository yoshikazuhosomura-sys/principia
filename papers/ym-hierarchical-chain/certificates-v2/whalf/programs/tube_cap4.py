import mpmath as mp, numpy as np, sys
from mpmath import iv
from scipy.special import ive
iv.dps=25; J=20; eps=0.005
# gamma from float MK (J=60) trajectories, restricted to first J+1 modes
Jf=60; nf=np.arange(Jf); th=np.linspace(0,np.pi,8001)[1:-1]; w=(2/np.pi)*np.sin(th)**2; dth=th[1]-th[0]
chi=np.array([np.sin((k+1)*th)/np.sin(th) for k in range(Jf)])
def coeffs(f): Z=np.sum(f*w)*dth; return (chi*w)@f*dth/((nf+1)*Z)
def build(c): return ((nf+1)*c)@chi
def Tf(c): f=np.maximum(build(c),1e-300); f=f/f.max(); return coeffs(f**4)**4
P=[]
for beta in np.linspace(2.0,6.0,33):
    c=ive(nf+1,beta)/ive(1,beta)
    for k in range(40):
        c=Tf(c)
        if k>=2 and 0.004<c[1]<0.95: P.append(c[:J+1].copy())
        if c[1]<0.004: break
P=np.array(P); P=P[np.argsort(P[:,1])]; S=P[:,1]
def up(s): return np.array([np.interp(s,S,P[:,m]) for m in range(J+1)])+eps*s**np.arange(J+1)
def kappa_lower(c):
    a=[(n+1)*c[n] for n in range(J+1)]
    fmin=1-sum(a[n]*(n+1) for n in range(1,J+1))
    if fmin.a<=0: return None
    d1=sum(a[n]*n*(n+1)*(n+2)/3 for n in range(1,J+1)); d2=sum(a[n]*(n-1)*n*(n+1)*(n+2)*(n+3)/15 for n in range(1,J+1))
    g1=d1/fmin; return 1-12*(g1+d2/fmin+g1**2)
def mul(a,b):
    out=[iv.mpf(0)]*(J+1)
    for i in range(J+1):
        for j in range(J+1):
            p=a[i]*b[j]
            for c in range(abs(i-j),min(i+j,J)+1,2): out[c]+=p
    return out
def T(c):
    a=[(n+1)*c[n] for n in range(J+1)]; a2=mul(a,a); a4=mul(a2,a2)
    return [ (a4[n]/((n+1)*a4[0]))**4 for n in range(J+1)]
lo,hi=float(sys.argv[1]),float(sys.argv[2]); rel=float(sys.argv[3])
s=lo; nd=0; ni=0; nc=0; fails=[]
while s<hi:
    s2=min(s*(1+rel),hi); ss=np.linspace(s,s2,5); U=np.max([up(x) for x in ss],0)
    B=[iv.mpf(1),iv.mpf([s,s2])]+[iv.mpf([0,U[n]]) for n in range(2,J+1)]
    TB=T(B); t1a,t1b=float(TB[1].a),float(TB[1].b)
    dec = t1b < s
    if t1a>=0.07 and t1b<=0.95:
        sp=np.linspace(t1a,t1b,7); Ul=np.min([up(x) for x in sp],0); inv=all(float(TB[n].b)<=Ul[n] for n in range(2,J+1))
    else: inv = t1b<0.07   # lands in BE region
    if not inv:
        kl=kappa_lower(TB); inv = (kl is not None and kl.a>0)
    nc+=1; nd+=dec; ni+=inv
    if not(dec and inv) and len(fails)<6: fails.append((round(s,4),dec,inv,round(t1b/s,4)))
    s=s2
print(f"[{lo},{hi}] cells={nc}: decrease certified {nd}, invariance certified {ni}; first fails {fails}")
