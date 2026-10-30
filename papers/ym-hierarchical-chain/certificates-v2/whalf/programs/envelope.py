
# ---- rigorous envelopes of the tube boundary up_n(s) = gamma_n(s) + eps*s^n  (gamma = np.interp of data (S,P), constant outside [S0,S_end]) ----
SAFE=1e-9   # relative safety margin covering float rounding of np.interp
def _gamma_pts(a,b):
    a=max(a,0.0); pts=[a,b]+[x for x in S if a<x<b]
    return np.array([[np.interp(x,S,P[:,m]) for m in range(J+1)] for x in pts])
def up_max(a,b):   # >= sup_{s in [a,b]} up_n(s)  (piecewise linear: extremes at endpoints/breakpoints; eps s^n increasing)
    G=_gamma_pts(a,b).max(0); return G*(1+SAFE)+eps*b**np.arange(J+1)
def up_min(a,b):   # <= inf_{s in [a,b]} up_n(s)
    G=_gamma_pts(a,b).min(0); return G*(1-SAFE)+eps*max(a,0.0)**np.arange(J+1)
