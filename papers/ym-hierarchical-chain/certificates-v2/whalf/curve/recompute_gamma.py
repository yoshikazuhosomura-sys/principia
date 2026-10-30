# Recompute the reference curve gamma of Definition 5.1(a) in double precision:
# Wilson orbits for beta in linspace(2,6,33) (J=60, theta grid of 8001 points, f scaled by max f); points of the third and later
# iterates with 0.004 < c_1 < 0.95, sorted by c_1; gamma is their piecewise-linear interpolation. Output: gamma_S.txt, gamma_P.txt
import numpy as np, sys
from scipy.special import ive
J = 20; Jf = 60; nf = np.arange(Jf)
th = np.linspace(0, np.pi, 8001)[1:-1]; w = (2 / np.pi) * np.sin(th) ** 2; dth = th[1] - th[0]
chi = np.array([np.sin((k + 1) * th) / np.sin(th) for k in range(Jf)])
def coeffs(f): Z = np.sum(f * w) * dth; return (chi * w) @ f * dth / ((nf + 1) * Z)
def build(c): return ((nf + 1) * c) @ chi
def Tf(c): f = np.maximum(build(c), 1e-300); f = f / f.max(); return coeffs(f ** 4) ** 4
P = []
for beta in np.linspace(2.0, 6.0, 33):
    c = ive(nf + 1, beta) / ive(1, beta)
    for k in range(40):
        c = Tf(c)
        if k >= 2 and 0.004 < c[1] < 0.95: P.append(c[:J + 1].copy())
        if c[1] < 0.004: break
P = np.array(P); P = P[np.argsort(P[:, 1])]; S = P[:, 1]
np.savetxt(sys.argv[1] + '/gamma_S.txt', S, fmt='%.17g'); np.savetxt(sys.argv[1] + '/gamma_P.txt', P, fmt='%.17g')
print('points', len(S), 'S range', S.min(), S.max())
