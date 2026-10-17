# 第813便・本番：ħ の区間 [h1,h2] を順に（適応の幅で）回す。b の格子の各点の鎖は一度だけ作り、隣り合う細胞で共有する。
# 判定は m813_iv（中心形の後ろ向き）＋前向き（fwd z＝m813_iv2.forward2 ／ y＝m813_y.forward_y）。結論文は印字しない。
# 使い方：m813_prod.py <state.json> <out.json> <A> <B> <c1> <target> <delta0> <fwd> <cpu_budget> [specfile_for_ends_at_small_h]
#   区間 [h, h(1+δ)] を h = A から B まで。上界 ≤ target なら受理して進み、越えたら δ を縮めて同じ h から回し直す。
import sys, os, json, time, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m813_iv2 import chain, forward2, endgrid, BG, make_cells, vprime_range, EPS, XC, C2
from m813_y import forward_y
from m813_band import chain_b, forward_b
def geometry_cells(h1, specfile=None):
    # (N, 鎖の b の列) の組：隣り合う b の細胞が鎖を共有する。b = None は b → −∞。
    # 指定のファイルの行 "r b_lo b_hi"（r = 0..7 は端、r = int は内部の b の格子を BG の代わりに）。
    G = [('int', 15, list(BG))]
    if specfile:
        rows = [l.split() for l in open(specfile) if l.strip()]
        ir = [(float(l[1]), float(l[2])) for l in rows if l[0] == 'int']
        ib = ([ir[0][0]] + [b for a, b in ir]) if ir else []
        assert all(ir[k][0] == ir[k-1][1] for k in range(1, len(ir)))
        if ib:
            ib = [-XC if abs(x + 0.89) < 1e-15 else x for x in ib]; assert ib[0] == -XC and ib[-1] == 0.0 and all(a < b for a, b in zip(ib[:-1], ib[1:]))
            G = [('int', 15, ib)]
        rows = [l for l in rows if l[0] != 'int']
        by_r = {}
        for r, bl, bh in rows: by_r.setdefault(int(r), []).append((None if bl == 'inf' else float(bl), -XC if float(bh) == -0.89 else float(bh)))
        for r in range(8):
            if r in by_r:
                cells = by_r[r]; G.append(('endcells', 8 + r, cells, r))
            else:
                G.append(('end', 8 + r, endgrid(r, h1), r))
    else:
        for r in range(8): G.append(('end', 8 + r, endgrid(r, h1), r))
    return G
def one_interval(h1, h2, c1, fwd, specfile=None, band=None):
    t0 = time.process_time()
    t = make_cells(h1, -XC, 0.0, c1, c2=C2); n = len(t)-1; chunk = max(8, int(4e5//n))
    lam1 = 1.0/(EPS*h1); lam2 = 1.0/(EPS*h2); lam0 = math.sqrt(lam1*lam2)
    P = {'lam0': lam0, 'dl': (lam2 - lam0, lam1 - lam0), 'lamr': (lam1, lam2), 'vr': vprime_range(t), 'mode': 'center', 'dw': True}
    ac = np.where((t[:-1] >= -XC-1e-15) & (t[1:] <= 1e-15))[0]
    out = []
    for g in geometry_cells(h1, specfile):
        kind, N = g[0], g[1]
        if kind == 'endcells': pairs = g[2]
        else: bs = g[2]; pairs = [(bs[k], bs[k+1]) for k in range(len(bs)-1)]
        cache = {}
        if band:
            R, G, Wf = band; W = Wf/math.sqrt(2*lam0)
        def ch(b):
            key = 'inf' if b is None else repr(float(b))
            if key not in cache: cache[key] = chain_b(t, P, N, b, R, G, W) if band else chain(t, P, N, b, chunk, True, True)
            return cache[key]
        for blo, bhi in pairs:
            slo = ch(blo); shi = ch(bhi)
            if band: Fu, Fl = forward_b(t, P, slo, shi, 8, R, G, W)
            else: Fu, Fl = (forward_y if fwd == 'y' else forward2)(t, P, slo, shi, 8, chunk)
            out.append({'geom': kind if kind == 'int' else 'end%d' % g[-1], 'blo': blo, 'bhi': bhi, 'rho_up': float(Fu[ac].max()), 'rho_low': float(Fl[ac].max())})
    sup = max(o['rho_up'] for o in out); w = max(out, key=lambda o: o['rho_up'])
    return {'h1': h1, 'h2': h2, 'delta': h2/h1 - 1, 'c1': c1, 'n': n, 'fwd': fwd, 'band': band, 'rho_up_sup': sup, 'worst': [w['geom'], w['blo'], w['bhi']],
            'rho_low_sup': max(o['rho_low'] for o in out), 'cpu': time.process_time() - t0, 'ncells': len(out), 'cells': out}
if __name__ == '__main__':
    st_f, out_f, A, B, c1, target, d0, fwd, budget = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6]), float(sys.argv[7]), sys.argv[8], float(sys.argv[9])
    spec = sys.argv[10] if len(sys.argv) > 10 and sys.argv[10] != '-' else None
    band = tuple(float(x) for x in sys.argv[11].split(',')) if len(sys.argv) > 11 and sys.argv[11] != '-' else None
    if band: band = (int(band[0]), int(band[1]), band[2])
    st = json.load(open(st_f)) if os.path.exists(st_f) else {'h': A, 'delta': d0, 'done': [], 'rejected': []}
    T0 = time.process_time(); last = 0.0
    while st['h'] < B*(1 - 1e-12):
        if time.process_time() - T0 + 1.3*last > budget: break
        if st['delta'] < 2e-4: print('STUCK delta < 2e-4（点の上界が目標に近すぎる：c1 を細かくして再開）', flush=True); break
        h1 = st['h']; h2 = min(B, h1*(1 + st['delta']))
        r = one_interval(h1, h2, c1, fwd, spec, band); last = r['cpu']
        rec = {k: v for k, v in r.items() if k != 'cells'}
        if r['rho_up_sup'] <= target:
            st['done'].append(rec); st['h'] = h2
            # 次の幅：測った c ≈ 21 で点の値を推し量り、上界が 0.93·target になる幅へ（0.7 倍〜1.4 倍に制限）。正しさには効かない。
            dd = h2/h1 - 1; pt = r['rho_up_sup']*math.exp(-21.0*dd)
            dn = math.log(0.93*target/pt)/21.0 if pt < 0.93*target else 0.5*dd
            st['delta'] = min(1.4*dd, max(0.7*dd, dn))
            allc = json.load(open(out_f)) if os.path.exists(out_f) else []
            allc.append(r); json.dump(allc, open(out_f, 'w'))
        else:
            st['rejected'].append(rec); st['delta'] *= 0.6
        json.dump(st, open(st_f, 'w'))
        print(f"IV h=[{h1:.7g},{h2:.7g}] delta={h2/h1-1:.4f} c1={c1} n={r['n']} fwd={fwd} rho_up_sup={r['rho_up_sup']:.6g} worst={r['worst']} rho_low_sup={r['rho_low_sup']:.4g} cpu={r['cpu']:.1f}s {'ACCEPT' if r['rho_up_sup'] <= target else 'REJECT'}", flush=True)
    print(f"STOP h={st['h']:.7g} B={B} accepted={len(st['done'])} rejected={len(st['rejected'])} cpu={time.process_time()-T0:.1f}s", flush=True)
