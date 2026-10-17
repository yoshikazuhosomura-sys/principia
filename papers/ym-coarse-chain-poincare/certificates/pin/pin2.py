exec(open('pin.py').read().split('worst=(9,)')[0].split('for n in')[0])
exec('def bridge'+open('pin.py').read().split('def bridge')[1].split('worst=(9,)')[0])
import numpy as np
us=np.concatenate((np.linspace(-xc,-0.7,20),np.linspace(-0.69,0,24)))
Dmin=np.full(len(us),9.0)
for r in range(8):
    bs=[0,-0.15,-0.3,-0.6,-xc] if r==7 else [-xc,-xc-0.02,-xc-0.1,-xc-0.5,-xc-3]
    for a in [0,-0.1,-0.3,-0.6,-xc]:
        for b in bs:
            for k,u in enumerate(us):
                D=2*u-bridge(a,u,7)-bridge(b,u,r)+eps**2*dV(u)
                Dmin[k]=min(Dmin[k],D)
for u,D in zip(us,Dmin): print('%.4f %.5f'%(u,D))
