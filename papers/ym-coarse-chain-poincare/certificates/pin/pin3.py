# 命題 PIN の数：最悪の幾何（a=0、内部 b=0）の D(u)、d(ħ)、ρ の上界、Δ と裾
import numpy as np
exec('def bridge'+open('pin.py').read().split('def bridge')[1].split('worst=(9,)')[0].replace('',''), globals()) if False else None
from scipy.optimize import minimize
eps=0.5; xc=0.89
V=lambda z:(z*z-1)**2/8; dV=lambda z:z*(z*z-1)/2
def bridge(a,u,n):
    f=lambda z:0.5*np.sum(np.diff(np.concatenate(([a],z,[u])))**2)+eps**2*np.sum(V(z))
    g=lambda z:(lambda d:d[:-1]-d[1:]+eps**2*dV(z))(np.diff(np.concatenate(([a],z,[u]))))
    r=minimize(f,np.linspace(a,u,n+2)[1:-1],jac=g,method='L-BFGS-B',bounds=[(-xc,0)]*n,options={'ftol':1e-16,'gtol':1e-14})
    return r.x
H0=np.diag(np.full(7,1.875))-np.eye(7,k=1)-np.eye(7,k=-1); Hi=np.linalg.inv(H0)
Lg=(Hi[0,0]+Hi[6,6]+2*Hi[0,6])/4; e2=7*Hi[6,6]
print('Lg=%.5f  n*Hi77=%.5f'%(Lg,e2))
z=bridge(0.0,-xc,7); print('bridge a=0,u=-xc:',np.round(z,5))
# KKT の乗数（壁のサイト）
zz=np.concatenate(([0.0],z,[-xc])); grad=(zz[1:-1]-zz[:-2])-(zz[2:]-zz[1:-1])+eps**2*dV(z); print('grad at sites (>=0 on wall):',np.round(grad,6))
us=np.linspace(-xc,0,891)
D=np.array([2*u-bridge(0,u,7)[-1]-bridge(0,u,7)[-1]+eps**2*dV(u) for u in us])
print('D at -xc %.6f, min on [-xc,-0.8] %.6f'%(D[0],D[us<=-0.8].min()))
for h in [5e-6,7e-6,9e-6,1e-5]:
    lam=1/(eps*h); e=np.sqrt(e2/lam); d=D[us<=-0.8].min()-2*e
    I=np.concatenate(([0],np.cumsum((D[1:]+D[:-1])/2*np.diff(us))))-2*e*(us+xc)
    Delta=I[us>=-0.8].min()
    M=2.0; tail=xc**2*lam*M*xc*np.exp(-lam*Delta)
    rho=2*Lg/(lam*d*d)+lam*Lg*tail
    print('hbar=%.0e lam=%.3g e=%.5f d=%.5f Delta=%.5f lamDelta=%.0f rho<=%.4f rho_col<=%.4f'%(h,lam,e,d,Delta,lam*Delta,rho,2*rho))
