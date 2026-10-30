import os as _os; HERE=_os.path.dirname(_os.path.abspath(__file__))   # logs are read from ../logs
import re
runs=[('liftA_0.0144.txt',0.0144,0.06),('liftA_0.06.txt',0.06,0.11),('liftA_0.11.txt',0.11,0.163),('liftA_0.11_r2.txt',0.14836,0.163),
      ('liftB_0.163.txt',0.163,0.18),('liftB_0.163_r2.txt',0.16711,0.18),('liftB_0.18.txt',0.18,0.198),('liftB_0.18_r2.txt',0.18639,0.198)]
rel=0.005; intervals=[]; tot=0; boxes=0; maxbox=0
for f,lo,hi in runs:
    L=[l for l in open(_os.path.join(HERE,'..','logs',f)) if l.startswith('cell')]
    s=lo
    for l in L:
        m=re.match(r'cell ([0-9.]+) ok=(\w+) boxes=(\d+)',l); ps,ok,b=float(m.group(1)),m.group(2)=='True',int(m.group(3))
        assert abs(ps-s)<6e-6, (f,ps,s)
        assert ok, (f,ps)
        s2=min(s*(1+rel),hi); intervals.append((s,s2)); tot+=1; boxes+=b; maxbox=max(maxbox,b); s=s2
intervals.sort(); cur=0.0144; gaps=[]
for a,b in intervals:
    if a>cur+1e-15: gaps.append((cur,a))
    cur=max(cur,b)
print("cells",tot,"boxes",boxes,"max boxes/cell",maxbox,"covered up to",cur,"gaps",gaps)
