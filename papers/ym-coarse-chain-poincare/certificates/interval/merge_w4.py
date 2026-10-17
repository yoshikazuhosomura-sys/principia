import json,os
D='.'
def load(f): return json.load(open(f)) if os.path.exists(f) else []
keys3={tuple(k) for k in json.load(open(D+'/W3_keys.json'))}; keys4={tuple(k) for k in json.load(open(D+'/W4_keys.json'))}
out=load(D+'/FULL_out.json'); st=json.load(open(D+'/FULL_state.json'))
for tag,flt in (('W2',lambda r:True),('W3',lambda r:(r['h1'],r['h2']) in keys3),('W4',lambda r:(r['h1'],r['h2']) in keys4)):
    o=[r for r in load(D+'/FULL_%s_out.json'%tag) if flt(r)]; s=[d for d in json.load(open(D+'/FULL_%s_state.json'%tag))['done'] if flt(d)]
    ko={(r['h1'],r['h2']) for r in out}; out+=[r for r in o if (r['h1'],r['h2']) not in ko]
    kd={(d['h1'],d['h2']) for d in st['done']}; st['done']+=[d for d in s if (d['h1'],d['h2']) not in kd]
    print(tag,'merged',len(o),len(s))
json.dump(out,open(D+'/FULL_out.json.tmp','w')); os.replace(D+'/FULL_out.json.tmp',D+'/FULL_out.json')
json.dump(st,open(D+'/FULL_state.json.tmp','w')); os.replace(D+'/FULL_state.json.tmp',D+'/FULL_state.json')
print('state done=%d all_pass=%s max=%.6g'%(len(st['done']),all(d['pass'] for d in st['done']),max(d['rho_up_sup'] for d in st['done'])))
