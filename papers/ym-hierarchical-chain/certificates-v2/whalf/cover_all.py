import re,sys,os
d=sys.argv[1]
runs=[('liftA_0.0144.txt',0.0144,0.06,0.005),('liftA_0.06.txt',0.06,0.11,0.005),('liftA_0.11.txt',0.11,0.163,0.005),('liftA_0.11_r2.txt',0.14836,0.163,0.005),
      ('liftB_0.163.txt',0.163,0.18,0.005),('liftB_0.163_r2.txt',0.16711,0.18,0.005),('liftB_0.18.txt',0.18,0.198,0.005),('liftB_0.18_r2.txt',0.18639,0.198,0.005),
      ('liftC_0.198.txt',0.198,0.21,0.0025),('liftC_r2.txt',0.20452,0.21,0.0025)]
iv=[];tot=0;boxes=0;mx=0;per={}
for f,lo,hi,rel in runs:
    L=[l for l in open(os.path.join(d,f)) if l.startswith('cell')]
    s=lo;n=0
    for l in L:
        m=re.match(r'cell ([0-9.]+) ok=(\w+) boxes=(\d+)',l); ps,ok,b=float(m.group(1)),m.group(2)=='True',int(m.group(3))
        assert abs(ps-s)<6e-6,(f,ps,s); assert ok,(f,ps)
        s2=min(s*(1+rel),hi); iv.append((s,s2)); tot+=1; n+=1; boxes+=b; mx=max(mx,b); s=s2
    per[f]=n
iv.sort(); cur=0.0144; gaps=[]
for a,b in iv:
    if a>cur+1e-15: gaps.append((cur,a))
    cur=max(cur,b)
# distinct cells (overlapping restarts counted once by unique left end rounded)
print("log-lines",tot,"boxes",boxes,"max",mx,"covered to",cur,"gaps",gaps); print(per)
