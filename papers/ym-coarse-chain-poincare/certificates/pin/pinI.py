# 命題 PIN の D(u) を区間演算で下から押さえる。
# 上解の補題：ẑ∈K、ẑ_i<0 の全てのサイトで ∂_iΦ(ẑ)≥0 ⇒ 橋の最小点 m ≤ ẑ（劣モジュラ＋凸＋一意）。
# m は u について増加（比較原理）なので、細胞 [ul,uh] で m_last(u) ≤ ẑ_last(uh)。
import numpy as np, sys
from mpmath import iv, mpf
from scipy.optimize import minimize
iv.prec=80
eps=0.5; xc=0.89
V=lambda z:(z*z-1)**2/8; dV=lambda z:z*(z*z-1)/2
E2=iv.mpf(1)/4; XC=iv.mpf('0.89')
def bridge(a,u,n):
    f=lambda z:0.5*np.sum(np.diff(np.concatenate(([a],z,[u])))**2)+eps**2*np.sum(V(z))
    g=lambda z:(lambda d:d[:-1]-d[1:]+eps**2*dV(z))(np.diff(np.concatenate(([a],z,[u]))))
    r=minimize(f,np.linspace(a,u,n+2)[1:-1],jac=g,method='L-BFGS-B',bounds=[(-xc,0)]*n,options={'ftol':1e-16,'gtol':1e-15,'maxiter':10000})
    return r.x
def super_last(a,u,n):
    """数の最小点を少し持ち上げて上解にし、区間で検査。成功なら ẑ_last の上端（区間）を返す"""
    if n==0: return iv.mpf(repr(float(a))) if a!=-xc else -XC
    z=bridge(a,u,n)
    free=z>-xc+1e-12
    d2=(3*z*z-1)/2
    H=np.diag(2+eps**2*d2)-np.eye(n,k=1)-np.eye(n,k=-1)
    w=np.zeros(n)
    if free.any():
        Hf=H[np.ix_(free,free)]; w[free]=np.linalg.solve(Hf,np.ones(free.sum()))
    for k in range(14):
        dlt=10.0**(-13+k)
        zh=np.where(free,np.minimum(z+dlt*np.abs(w),0.0),-xc)
        A=iv.mpf(repr(float(a))); U=iv.mpf(repr(float(u)))
        Z=[(-XC if float(x)<=-xc else iv.mpf(repr(float(x)))) for x in zh]
        ok=True
        for i in range(n):
            l=A if i==0 else Z[i-1]; r=U if i==n-1 else Z[i+1]
            gr=2*Z[i]-l-r+E2*Z[i]*(Z[i]**2-1)/2
            if float(zh[i])<0 and not (gr.a>=0): ok=False;break
        if ok: return Z[-1]
    raise RuntimeError('上解が作れない a=%g u=%g n=%d'%(a,u,n))
# 細胞：壁の近くは細かく
cells=list(np.round(np.concatenate((np.linspace(-0.89,-0.88,101),np.linspace(-0.88,-0.80,161)[1:],np.linspace(-0.80,0,801)[1:])),12))
geoms=[('int',0.0,7)]+[('edge r=%d'%r,-xc,r) for r in range(8)]
res=[]
for k in range(len(cells)-1):
    ul,uh=cells[k],cells[k+1]
    UL=iv.mpf(repr(float(ul))) if ul!=-0.89 else -XC; UH=iv.mpf(repr(float(uh)))
    m7=super_last(0.0,uh,7)            # 左の橋 a=0（最悪）
    m9=min((super_last(b,uh,n) for _,b,n in geoms),key=lambda x:-float(x.b.a))  # 右の最悪（上端が最大）
    # ε²V'(u) の細胞上の下界：区間で
    Ucell=iv.mpf([UL.a,UH.b])
    vlow=(E2*Ucell*(Ucell**2-1)/2).a
    D=(2*UL.a-m7.b-m9.b+vlow).a
    res.append((ul,uh,float(D.a)))
D=np.array([r[2] for r in res]); u0=np.array([r[0] for r in res]); u1=np.array([r[1] for r in res])
print('cells',len(res),' D_low on [-xc,-0.8]: min %.6f'%D[u1<=-0.8+1e-12].min(), ' at wall cell %.6f'%D[0])
np.save('Dlow.npy',np.array(res))
lamh=[]
H0=np.diag(np.full(7,1.875))-np.eye(7,k=1)-np.eye(7,k=-1); Hi=np.linalg.inv(H0)
for h in [1e-5]:
    e=np.sqrt(7*Hi[6,6]*eps*h)
    I=np.cumsum((D-2*e)*(u1-u0)); Delta=I[u1>-0.8+1e-12].min()
    print('hbar=1e-5: e=%.5f d=%.5f Delta>=%.5f'%(e,D[u1<=-0.8+1e-12].min()-2*e,Delta))
