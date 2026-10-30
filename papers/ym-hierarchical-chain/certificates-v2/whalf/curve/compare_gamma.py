# Compare the reference curve computed by the certificate program (tube_cap4.py) with the recomputed curve (gamma_S.txt, gamma_P.txt).
# usage: python3 compare_gamma.py programs/tube_cap4.py curve/gamma_S.txt curve/gamma_P.txt
import sys, numpy as np
src=open(sys.argv[1]).read().split("def mul(a,b):")[0]
sys.argv=[sys.argv[0],'0','0','0',sys.argv[2],sys.argv[3]]
g={}; exec(src,g)
S,P=g['S'],g['P']
GS=np.loadtxt(sys.argv[4]); GP=np.loadtxt(sys.argv[5])
print(len(S),len(GS), P.shape, GP.shape)
print("max|dS|",np.max(np.abs(S-GS)))
print("q(0.3)=",np.interp(0.3,S,P[:,2])/0.09)
n=np.arange(21); eps=0.005*S[:,None]**n[None,:]
d=np.abs(P-GP)
print("max abs dP",d.max(),"max dP/(0.005 t^n) for n>=2", (d[:,2:]/eps[:,2:]).max())
