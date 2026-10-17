# 第904便：受理済みの 239 区間（第813便の P*_out.json の h1・h2・c1・混合の格子・端の表）を、区間演算の版で全ての幾何について回し直す。
# 適応はしない（区間の表は固定）。状態ファイルで続きから。判定：各区間の sup ρ⁺ < 0.5（ρ_col ≤ 2 sup ρ < 1）。結論文は印字しない。
# 使い方：m904_full.py <state.json> <out.json> <cpu_budget_s> [max_intervals] [order: small|large]
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m904_cert as IA
D813 = './table813'; D = os.path.dirname(os.path.abspath(__file__))
SPEC = {'P5a': D + '/spec_p5a.txt', 'P5b': D + '/spec_p5b.txt'}
def table():
    L = []
    for f in ('P1', 'P2', 'P3', 'P4a', 'P4b', 'P4c', 'P5a', 'P5b'):
        for r in json.load(open(f'{D813}/{f}_out.json')):
            b = r.get('band'); b = (int(b[0]), int(b[1]), float(b[2])) if b else None
            L.append({'src': f, 'h1': r['h1'], 'h2': r['h2'], 'c1': r['c1'], 'band': b, 'spec': SPEC.get(f), 'fl_sup': r['rho_up_sup'], 'fl_cpu': r['cpu']})
    L.sort(key=lambda x: x['h1'])
    for a, b in zip(L[:-1], L[1:]): assert b['h1'] <= a['h2'], (a['h2'], b['h1'])     # 隙間 0
    assert L[0]['h1'] <= 1e-5 and L[-1]['h2'] >= 1.0
    return L
if __name__ == '__main__':
    st_f, out_f, budget = sys.argv[1], sys.argv[2], float(sys.argv[3])
    maxn = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
    order = sys.argv[5] if len(sys.argv) > 5 else 'large'
    L = table()
    if order == 'large': L = L[::-1]                       # 安い大きい ħ から
    st = json.load(open(st_f)) if os.path.exists(st_f) else {'done': []}
    done = {(d['h1'], d['h2']) for d in st['done']}
    # 第905便：予算は CPU と壁時計の両方で見る（外側の timeout に途中で切られないように）。書き込みは一時ファイル→os.replace。
    SET = {k: os.environ.get(k) for k in ('IVX_WIDEN', 'IVX_POLY', 'M904_HFAST', 'M905_RB')}
    print('SETTINGS', SET, 'ivx.WIDEN=', IA.ivx.WIDEN, 'ivx.POLY=', IA.ivx.POLY, 'HFAST=', IA.HFAST, 'RB=', IA.RB, 'start', time.strftime('%Y-%m-%d %H:%M:%S'), flush=True)
    def dump(obj, f):
        tmp = f + '.tmp'; json.dump(obj, open(tmp, 'w')); os.replace(tmp, f)
    T0 = time.process_time(); W0 = time.time(); k = 0; last = 0.0; lastw = 0.0
    for iv in L:
        if (iv['h1'], iv['h2']) in done: continue
        if k >= maxn or time.process_time() - T0 + 1.3*last > budget or time.time() - W0 + 1.3*lastw > budget: break
        w0 = time.time()
        r = IA.one_interval(iv['h1'], iv['h2'], iv['c1'], iv['spec'], iv['band'])
        last = r['cpu']; lastw = time.time() - w0; k += 1
        rec = {kk: v for kk, v in r.items() if kk != 'cells'}; rec.update({'src': iv['src'], 'fl_sup': iv['fl_sup'], 'pass': r['rho_up_sup'] < 0.5, 'over_tau': r['rho_up_sup'] > 0.2, 'wall': lastw, 'settings': SET, 'finished': time.strftime('%Y-%m-%d %H:%M:%S')})
        allc = json.load(open(out_f)) if os.path.exists(out_f) else []
        allc = [a for a in allc if (a['h1'], a['h2']) != (iv['h1'], iv['h2'])]
        allc.append(r); dump(allc, out_f)
        st['done'].append(rec); dump(st, st_f)
        print(f"FULL {iv['src']} h=[{iv['h1']:.7g},{iv['h2']:.7g}] IA_sup={r['rho_up_sup']:.8g} FL_sup={iv['fl_sup']:.8g} pass={rec['pass']} cpu={r['cpu']:.1f}s (FL rec {iv['fl_cpu']:.1f}s)", flush=True)
    print(f"STOP done={len(st['done'])}/{len(L)} all_pass={all(d['pass'] for d in st['done'])} n_over_tau={sum(d['rho_up_sup'] > 0.2 for d in st['done'])} max={max([d['rho_up_sup'] for d in st['done']] or [0]):.6g} cpu={time.process_time()-T0:.1f}s wall={time.time()-W0:.1f}s at {time.strftime('%Y-%m-%d %H:%M:%S')}", flush=True)
    if len(st['done']) == len(L): print('ALL_DONE', flush=True)
