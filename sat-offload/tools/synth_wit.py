#!/usr/bin/env python3
r"""Monotone2 witness synthesis for the PG(2,3) partial-spec rows (L-meta-2056 family).

Specs (row generators, mirroring the Lean statements' semantics byte-for-byte):
  2056 : n=26 (A=bits 0..12, B=bits 13..25).
         pos: (p,q) with (p+q)%13 in D -> true on the {p}/{q} encoding.
         neg: S (|S|<=3): (S, comp S) and (comp S, S) -> false;
              comp S = {v | forall u in S, (u+v)%13 not in D}.
  3773 : same rows as 2056 (+ optional forced head gate; pairInput/addCases are
         semantically identical encodings).
  7161 : same rows as 2056 (its witness is derived from a 2056 witness, not solved here).
  7875 : n=25 compressed (bits 0..11 = A_{i+1}, bits 12..24 = B_{i-12}; A_0 invisible).
         main pos: (p,q), p != 0, (p+q)%13 in D.  aux pos: ({}, {q}), q in D.
         main neg: (S, comp S), (comp S, S).  aux neg: (S, comp S \ D), (comp S, S \ D).
         |S| <= 3.  TWO constrained wires: output (main) + one selected aux wire.
  1979 : n=26. pos: (p,q) with (p-q)%13 in D.
         neg: arcs A,B (each meets every translate v+D in <= 2 points) with no
              incident pair (a-b in D) -> false.

CEGAR: encode k-gate AND/OR fan-in-2 circuits over a growing row subset; cadical solves;
bigint-parallel simulation checks the decoded candidate against ALL rows; violated rows
join the active set. UNSAT on a row subset is UNSAT for the full spec (a subset of the
constraints), so an UNSAT round is a sound negative verdict.
Search-space soundness (wlog for any valid witness of a spec with both true and false
rows): output = last gate (dead-gate-free), every gate reads exactly two earlier wires
(0/1-input gates are copies; constants are eliminable in monotone circuits), first input
index <= second (ops commute).

Positive control: the known per-line constructions (2056/3773: 64 gates, 7875: 62 gates,
1979: 64 gates) are checked two ways: (a) bigint simulation against every generated row;
(b) in round 1, as a full variable assignment checked against EVERY emitted clause -
validating both the clause semantics and the row requirements (a wrong row requirement
falsifies a unit clause).

Env: SAT_N = spec id, SAT_S = k (gate budget), SAT_TIMEOUT_MIN = wall budget (minutes),
     SAT_CADICAL = solver path, SAT_EXTRA_ARGS = 'key=value,...' overrides:
        headgate=and013|or01|or013|or213   rows0=<n> (default 28)   addcap=<n> (default 400)
        roundsec=<s> (default 900)   seed=<s>   control=<0|1> (default 1)
argv[1] = work dir. Writes verdict.txt ('SAT'|'UNSAT'|'UNKNOWN'|'CONTROL-FAIL'),
witness.json, cegar.log, input.cnf, model.
"""
import sys, os, json, subprocess, time, itertools, shlex

D = {0, 1, 3, 9}
N13 = 13


def comp_add(S):
    """2056's x4: {v | forall u in S, (u+v)%13 not in D}."""
    return frozenset(v for v in range(N13)
                    if all(((u + v) % N13) not in D for u in S))


def mask(points, n, offset=0):
    m = 0
    for p in points:
        m |= 1 << (offset + p)
    return m


def rows_2056():
    n = 26
    rows = []
    for p in range(N13):
        for q in range(N13):
            if (p + q) % N13 in D:
                rows.append((mask([p], n) | mask([q], n, 13), True, 'out', f'pos+{p},{q}'))
    sets = [S for r in range(4) for S in itertools.combinations(range(N13), r)]
    for S in sets:
        C = comp_add(S)
        rows.append((mask(S, n) | mask(C, n, 13), False, 'out', f'neg S={list(S)},comp'))
        rows.append((mask(C, n) | mask(S, n, 13), False, 'out', f'neg comp,S={list(S)}'))
    return n, dedupe(rows)


def dedupe(rows):
    seen = set()
    out = []
    for r in rows:
        key = (r[0], r[1], r[2])
        if key not in seen:
            seen.add(key)
            out.append(r)
    return out


def rows_7875():
    n = 25
    def enc(A, B):
        m = 0
        for p in A:
            if p != 0:
                m |= 1 << (p - 1)
        for q in B:
            m |= 1 << (12 + q)
        return m
    rows = []
    for p in range(1, N13):
        for q in range(N13):
            if (p + q) % N13 in D:
                rows.append((enc([p], [q]), True, 'out', f'pos+{p},{q}'))
    for q in D:
        rows.append((enc([], [q]), True, 'aux', f'pos-aux0,{q}'))
    sets = [S for r in range(4) for S in itertools.combinations(range(N13), r)]
    for S in sets:
        C = comp_add(S)
        rows.append((enc(S, C), False, 'out', f'neg-main S={list(S)}'))
        rows.append((enc(C, S), False, 'out', f'neg-main comp,S={list(S)}'))
        CD = sorted(C - D)
        SD = sorted(set(S) - D)
        rows.append((enc(S, CD), False, 'aux', f'neg-aux S={list(S)}'))
        rows.append((enc(C, SD), False, 'aux', f'neg-aux comp,S={list(S)}'))
    return n, dedupe(rows)


def rows_1979():
    n = 26
    rows = []
    for p in range(N13):
        for q in range(N13):
            if (p - q) % N13 in D:
                rows.append((mask([p], n) | mask([q], n, 13), True, 'out', f'pos+{p},{q}'))
    arcs = []
    for r in range(5):
        for S in itertools.combinations(range(N13), r):
            ok = True
            for v in range(N13):
                line = {(v + d) % N13 for d in D}
                if len(set(S) & line) > 2:
                    ok = False
                    break
            if ok:
                arcs.append(frozenset(S))
    negs = []
    for A in arcs:
        forbid = {(a - d) % N13 for a in A for d in D}   # b with a-b in D
        for B in arcs:
            if not (set(B) & forbid):
                negs.append((mask(sorted(A), n) | mask(sorted(B), n, 13), False, 'out',
                             f'arc {sorted(A)},{sorted(B)}'))
    rows.extend(negs)
    return n, dedupe(rows), len(arcs)


# ---------------- known constructions (positive controls) ----------------
def _g(op, a, b):
    return (op, min(a, b), max(a, b))


def build_fdisj(flavor):
    """OR_q (B_q & OR_{p in P_q} A_p), P_q = {p | p+q in D} ('add') or {p | p-q in D} ('sub').
    64 gates. Wires: A_p = p, B_q = 13+q, gate j -> 26+j. Inputs sorted (a <= b)."""
    gates = []
    for q in range(N13):
        if flavor == 'add':
            ps = sorted({(d - q) % N13 for d in D})
        else:
            ps = sorted({(q + d) % N13 for d in D})
        g0 = len(gates)
        gates.append(_g('or', ps[0], ps[1]))
        gates.append(_g('or', 26 + g0, ps[2]))
        gates.append(_g('or', 26 + g0 + 1, ps[3]))
        gates.append(_g('and', 13 + q, 26 + g0 + 2))
    terms = [26 + 4 * q + 3 for q in range(N13)]
    cur = terms[0]
    for t in terms[1:]:
        g = len(gates)
        gates.append(_g('or', cur, t))
        cur = 26 + g
    return 26, gates, cur


def build_7875_62():
    """main = OR_{p=1..12}(A_p & OR_{q in D-p} B_q) [59 gates], aux = OR_{q in D} B_q [3].
    n=25. Wires: A_p (p>=1) = p-1; B_q = 12+q; gate j -> 25+j. Inputs sorted (a <= b)."""
    gates = []
    for p in range(1, N13):
        qs = sorted({(d - p) % N13 for d in D})
        g0 = len(gates)
        gates.append(_g('or', 12 + qs[0], 12 + qs[1]))
        gates.append(_g('or', 25 + g0, 12 + qs[2]))
        gates.append(_g('or', 25 + g0 + 1, 12 + qs[3]))
        gates.append(_g('and', p - 1, 25 + g0 + 2))
    terms = [25 + 4 * (p - 1) + 3 for p in range(1, N13)]
    cur = terms[0]
    for t in terms[1:]:
        g = len(gates)
        gates.append(_g('or', cur, t))
        cur = 25 + g
    qD = sorted(D)
    g0 = len(gates)
    gates.append(_g('or', 12 + qD[0], 12 + qD[1]))
    gates.append(_g('or', 12 + qD[2], 12 + qD[3]))
    gates.append(_g('or', 25 + g0, 25 + g0 + 1))
    return 25, gates, cur, 25 + g0 + 2   # n, gates, main out, aux wire


# ---------------- bigint simulation ----------------
def wire_bigints(n, rows):
    """wire i -> bigint whose bit r = row r's bit i."""
    out = []
    for i in range(n):
        v = 0
        for idx, r in enumerate(rows):
            if (r[0] >> i) & 1:
                v |= 1 << idx
        out.append(v)
    return out


def simulate(n, gates, win):
    w = list(win)
    for op, a, b in gates:
        wa = w[a] if a < len(w) else 0
        wb = w[b] if b < len(w) else 0
        w.append((wa & wb) if op == 'and' else (wa | wb))
    return w


def violated(rows, w, outwire, auxwire=None):
    vo = w[outwire] if outwire is not None and outwire < len(w) else 0
    va = w[auxwire] if auxwire is not None and auxwire < len(w) else 0
    viol = []
    for idx, r in enumerate(rows):
        got = (vo >> idx) & 1 if r[2] == 'out' else (va >> idx) & 1
        if bool(got) != r[1]:
            viol.append(idx)
    return viol


def check_all(n, gates, outwire, rows, auxwire=None):
    w = simulate(n, gates, wire_bigints(n, rows))
    v = violated(rows, w, outwire, auxwire)
    return (len(v) == 0), v


def row_wire_vals(n, gates, rows):
    """wire i -> list of bools per row (inputs then gates)."""
    R = len(rows)
    w = [[bool((r[0] >> i) & 1) for r in rows] for i in range(n)]
    for op, a, b in gates:
        wa = w[a] if a < len(w) else [False] * R
        wb = w[b] if b < len(w) else [False] * R
        w.append([(x and y) if op == 'and' else (x or y) for x, y in zip(wa, wb)])
    return w


# ---------------- CNF encoder ----------------
class ControlFail(Exception):
    pass


def layout(n, k, R, two_out):
    W = n + k
    v = 0
    d = {}
    d['op'] = v; v += k
    d['sel'] = v; v += k * W
    d['sel2'] = v; v += k * W
    d['V'] = v; v += R * k
    d['p1'] = v; v += R * k
    d['p2'] = v; v += R * k
    d['Aa'] = v; v += R * k
    d['Oo'] = v; v += R * k
    if two_out:
        d['osel'] = v; v += W
        d['asel'] = v; v += W
        d['OV'] = v; v += R
        d['AX'] = v; v += R
    d['nvars'] = v
    return d


def encode_cnf(path, n, k, rows, headgate=None, two_out=False,
              control_gates=None, control_out=None, control_aux=None):
    """rows: list of (bits, req, kind, tag). Returns (nvars, nclauses)."""
    R = len(rows)
    W = n + k
    L = layout(n, k, R, two_out)

    def V(kind, *key):
        if kind == 'op': return L['op'] + key[0]
        if kind == 'sel': return L['sel'] + key[0] * W + key[1]
        if kind == 'sel2': return L['sel2'] + key[0] * W + key[1]
        if kind == 'V': return L['V'] + key[0] * k + key[1]
        if kind == 'p1': return L['p1'] + key[0] * k + key[1]
        if kind == 'p2': return L['p2'] + key[0] * k + key[1]
        if kind == 'Aa': return L['Aa'] + key[0] * k + key[1]
        if kind == 'Oo': return L['Oo'] + key[0] * k + key[1]
        if kind == 'osel': return L['osel'] + key[0]
        if kind == 'asel': return L['asel'] + key[0]
        if kind == 'OV': return L['OV'] + key[0]
        if kind == 'AX': return L['AX'] + key[0]
        raise KeyError(kind)

    assign = None
    if control_gates is not None:
        wv = row_wire_vals(n, control_gates, rows)
        assert len(control_gates) == k, f'control gates {len(control_gates)} != k {k}'
        assign = {}
        for g, (op, a, b) in enumerate(control_gates):
            assign[V('op', g)] = (op == 'and')
            for i in range(n + g):
                assign[V('sel', g, i)] = (i == a)
                assign[V('sel2', g, i)] = (i == b)
            for r in range(R):
                va = wv[a][r] if a < len(wv) else False
                vb = wv[b][r] if b < len(wv) else False
                assign[V('p1', r, g)] = va
                assign[V('p2', r, g)] = vb
                assign[V('Aa', r, g)] = va and vb
                assign[V('Oo', r, g)] = va or vb
                assign[V('V', r, g)] = wv[n + g][r]
        if two_out:
            for wi in range(W):
                assign[V('osel', wi)] = (wi == control_out)
                assign[V('asel', wi)] = (wi == control_aux)
            for r in range(R):
                assign[V('OV', r)] = wv[control_out][r]
                assign[V('AX', r)] = wv[control_aux][r]

    nclauses = 0
    body = path + '.body'
    f = open(body, 'w', buffering=1 << 20)

    def E(lits):
        nonlocal nclauses
        if assign is not None:
            sat = False
            unknown = False
            for (v0, s) in lits:
                bv = assign.get(v0)
                if bv is None:
                    unknown = True
                    continue
                if bv == s:
                    sat = True
                    break
            if not sat and not unknown:
                f.close()
                try:
                    os.remove(body)
                except OSError:
                    pass
                raise ControlFail(f'clause falsified by control assignment: {lits[:8]}')
        f.write(' '.join(('' if s else '-') + str(v0 + 1) for (v0, s) in lits) + '\n')
        nclauses += 1

    # gate structure
    for g in range(k):
        avail = n + g
        E([(V('sel', g, i), True) for i in range(avail)])
        E([(V('sel2', g, i), True) for i in range(avail)])
        for i in range(avail):
            for j in range(i + 1, avail):
                E([(V('sel', g, i), False), (V('sel', g, j), False)])
                E([(V('sel2', g, i), False), (V('sel2', g, j), False)])
            for j in range(i):
                E([(V('sel', g, i), False), (V('sel2', g, j), False)])
    if headgate:
        opv, a, b = headgate
        E([(V('op', 0), opv == 'and')])
        E([(V('sel', 0, a), True)])
        E([(V('sel2', 0, b), True)])
    # row semantics
    for r in range(R):
        bits = rows[r][0]
        for g in range(k):
            avail = n + g
            p1, p2 = V('p1', r, g), V('p2', r, g)
            Aa, Oo = V('Aa', r, g), V('Oo', r, g)
            Vr = V('V', r, g)
            opv = V('op', g)
            for i in range(avail):
                s1, s2 = V('sel', g, i), V('sel2', g, i)
                if i < n:
                    bit = bool((bits >> i) & 1)
                    if bit:
                        E([(p1, True), (s1, False)])
                        E([(p2, True), (s2, False)])
                    else:
                        E([(p1, False), (s1, False)])
                        E([(p2, False), (s2, False)])
                else:
                    Vsrc = V('V', r, i - n)
                    E([(p1, False), (s1, False), (Vsrc, True)])
                    E([(p1, True), (s1, False), (Vsrc, False)])
                    E([(p2, False), (s2, False), (Vsrc, True)])
                    E([(p2, True), (s2, False), (Vsrc, False)])
            E([(Aa, False), (p1, True)])
            E([(Aa, False), (p2, True)])
            E([(Aa, True), (p1, False), (p2, False)])
            E([(Oo, True), (p1, False)])
            E([(Oo, True), (p2, False)])
            E([(Oo, False), (p1, True), (p2, True)])
            E([(Vr, False), (opv, True), (Oo, True)])
            E([(Vr, False), (opv, False), (Aa, True)])
            E([(Vr, True), (Aa, False), (opv, False)])
            E([(Vr, True), (Oo, False), (opv, True)])
    # output constraints
    if two_out:
        E([(V('osel', wi), True) for wi in range(W)])
        E([(V('asel', wi), True) for wi in range(W)])
        for i in range(W):
            for j in range(i + 1, W):
                E([(V('osel', i), False), (V('osel', j), False)])
                E([(V('asel', i), False), (V('asel', j), False)])
        for r in range(R):
            kind = rows[r][2]
            bits = rows[r][0]
            if kind == 'out':
                selkind, valvar = 'osel', V('OV', r)
            else:
                selkind, valvar = 'asel', V('AX', r)
            for wi in range(W):
                sw = V(selkind, wi)
                if wi < n:
                    bit = bool((bits >> wi) & 1)
                    if bit:
                        E([(valvar, True), (sw, False)])
                    else:
                        E([(valvar, False), (sw, False)])
                else:
                    Vsrc = V('V', r, wi - n)
                    E([(valvar, False), (sw, False), (Vsrc, True)])
                    E([(valvar, True), (sw, False), (Vsrc, False)])
            E([(valvar, rows[r][1])])
    else:
        for r in range(R):
            E([(V('V', r, k - 1), rows[r][1])])
    f.close()
    with open(path, 'w') as out:
        out.write(f'p cnf {L["nvars"]} {nclauses}\n')
        with open(body, 'r', buffering=1 << 20) as bf:
            while True:
                chunk = bf.read(1 << 22)
                if not chunk:
                    break
                out.write(chunk)
    os.remove(body)
    return L['nvars'], nclauses


def read_model(model_path):
    m = {}
    with open(model_path) as f:
        for line in f:
            if line.startswith('c'):
                continue
            toks = line.replace('v', ' ').split()
            for t in toks:
                if not t.lstrip('-').isdigit():
                    continue
                lit = int(t)
                if lit == 0:
                    continue
                m[abs(lit) - 1] = lit > 0
    return m


def trim_cone(n, gates, outwire, keep_extra=()):
    """Keep only gates feeding outwire/keep_extra; re-index. Returns (gates', out', extras')."""
    keep = set()
    stack = [outwire] + list(keep_extra)
    while stack:
        w = stack.pop()
        if w < n:
            continue
        g = w - n
        if g < 0 or g >= len(gates) or g in keep:
            continue
        keep.add(g)
        op, a, b = gates[g]
        stack.append(a)
        stack.append(b)
    order = sorted(keep)
    remap = {n + g: n + new for new, g in enumerate(order)}
    out2 = []
    for g in order:
        op, a, b = gates[g]
        a2 = a if a < n else remap[a]
        b2 = b if b < n else remap[b]
        out2.append((op, a2, b2))
    outwire2 = outwire if outwire < n else remap.get(outwire, outwire)
    extras2 = [w if w < n else remap.get(w, w) for w in keep_extra]
    return out2, outwire2, extras2


# ---------------- main ----------------
def main():
    work = sys.argv[1] if len(sys.argv) > 1 else '.'
    os.makedirs(work, exist_ok=True)
    spec = os.environ.get('SAT_N', '2056')
    k = int(os.environ.get('SAT_S', '63'))
    budget_min = float(os.environ.get('SAT_TIMEOUT_MIN', '350'))
    cad = os.environ.get('SAT_CADICAL', 'cadical')
    extra = {}
    for kv in os.environ.get('SAT_EXTRA_ARGS', '').split(','):
        if '=' in kv:
            a, b = kv.split('=', 1)
            extra[a.strip()] = b.strip()
    seed = extra.get('seed', '2')
    rows0 = int(extra.get('rows0', '28'))
    addcap = int(extra.get('addcap', '400'))
    roundsec = int(extra.get('roundsec', '900'))
    maxrows = int(extra.get('maxrows', '1000000'))
    do_control = extra.get('control', '1') == '1'
    headgate = None
    if extra.get('headgate'):
        headgate = {'and013': ('and', 0, 13), 'or01': ('or', 0, 1),
                    'or013': ('or', 0, 13), 'or213': ('or', 2, 13)}[extra['headgate']]
    log = open(os.path.join(work, 'cegar.log'), 'w', buffering=1 << 16)

    def L(*a):
        msg = ' '.join(str(x) for x in a)
        print(msg, flush=True)
        log.write(msg + '\n')
        log.flush()

    t0 = time.time()
    two_out = (spec == '7875')
    if spec in ('2056', '3773'):
        n, rows = rows_2056()
        ctrl = build_fdisj('add')
        cn, cg, cout, caux = ctrl[0], ctrl[1], ctrl[2], None
    elif spec == '7875':
        n, rows = rows_7875()
        cn, cg, cout, caux = build_7875_62()
    elif spec == '1979':
        n, rows, narcs = rows_1979()
        ctrl = build_fdisj('sub')
        cn, cg, cout = ctrl
        caux = None
        L(f'arcs: {narcs}')
    else:
        raise SystemExit(f'unknown spec {spec}')

    pos = [r for r in rows if r[1]]
    neg = [r for r in rows if not r[1]]
    L(f'spec={spec} n={n} k={k} rows: {len(rows)} = {len(pos)} pos + {len(neg)} neg')

    # control (a): known construction satisfies every generated row
    okc, violc = check_all(cn, cg, cout, rows, caux)
    if not okc:
        L(f'CONTROL FAILED (rows): {len(violc)} violated, e.g. {[rows[i][3] for i in violc[:10]]}')
        with open(os.path.join(work, 'verdict.txt'), 'w') as f:
            f.write('CONTROL-FAIL\n')
        return 2
    L('control (a): known construction satisfies all rows OK')

    def control_for_k(kk):
        cgk = list(cg)
        coutk, cauxk = cout, caux
        if headgate is not None:
            opv, a, b = headgate
            cgk = [(op,
                    (x if x < cn else cn + 1 + (x - cn)),
                    (y if y < cn else cn + 1 + (y - cn))) for (op, x, y) in cgk]
            cgk = [(opv, a, b)] + cgk
            coutk = cn + 1 + (cout - cn)
            if cauxk is not None:
                cauxk = cn + 1 + (cauxk - cn)
        if len(cgk) > kk:
            return None
        cgk = cgk + [('or', 0, 0)] * (kk - len(cgk))
        return cgk, coutk, cauxk

    active = pos + neg[:rows0]
    active_idx = set(range(len(active)))
    cnf_path = os.path.join(work, 'input.cnf')
    model_path = os.path.join(work, 'model')
    round_no = 0
    while True:
        round_no += 1
        remaining = budget_min * 60 - (time.time() - t0)
        if remaining <= 90:
            L('budget exhausted')
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('UNKNOWN\n')
            with open(os.path.join(work, 'cegar_state.json'), 'w') as f:
                json.dump({'rounds': round_no, 'active_rows': len(active), 'k': k,
                           'spec': spec}, f)
            return 0
        cap = min(roundsec, int(remaining) - 60)
        t_enc = time.time()
        ctl = None
        if do_control and round_no == 1:
            ctl = control_for_k(k)
        try:
            if ctl is not None:
                cgk, coutk, cauxk = ctl
                nvars, ncl = encode_cnf(cnf_path, n, k, active, headgate=headgate,
                                        two_out=two_out, control_gates=cgk,
                                        control_out=coutk, control_aux=cauxk)
                L(f'round {round_no}: encoding control checked against all {ncl} clauses OK')
            else:
                nvars, ncl = encode_cnf(cnf_path, n, k, active, headgate=headgate,
                                        two_out=two_out)
        except ControlFail as e:
            L(f'ENCODING CONTROL FAILED: {e}')
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('CONTROL-FAIL\n')
            return 2
        L(f'round {round_no}: rows={len(active)} vars={nvars} clauses={ncl} '
          f'enc={time.time()-t_enc:.1f}s cap={cap}s')
        cmd = (shlex.split(cad) if ' ' in cad else [cad]) + \
              [f'--seed={seed}', '--elim=false', '-w', model_path, cnf_path]
        t_solve = time.time()
        try:
            rc = subprocess.run(cmd, capture_output=True, timeout=cap).returncode
        except subprocess.TimeoutExpired:
            L(f'round {round_no}: TIMEOUT after {cap}s')
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('UNKNOWN\n')
            with open(os.path.join(work, 'cegar_state.json'), 'w') as f:
                json.dump({'rounds': round_no, 'active_rows': len(active), 'k': k,
                           'spec': spec}, f)
            return 0
        L(f'round {round_no}: cadical rc={rc} in {time.time()-t_solve:.1f}s')
        if rc == 20:
            L(f'UNSAT on {len(active)} of {len(rows)} rows -> NO circuit of size <= {k} '
              f'(sound: subset-UNSAT)')
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('UNSAT\n')
            with open(os.path.join(work, 'cegar_state.json'), 'w') as f:
                json.dump({'rounds': round_no, 'active_rows': len(active), 'k': k,
                           'spec': spec}, f)
            return 0
        if rc != 10 or not os.path.exists(model_path):
            L('no verdict (unknown)')
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('UNKNOWN\n')
            with open(os.path.join(work, 'cegar_state.json'), 'w') as f:
                json.dump({'rounds': round_no, 'active_rows': len(active), 'k': k,
                           'spec': spec}, f)
            return 0
        m = read_model(model_path)
        W = n + k
        sel_b, sel2_b = k, k + k * W
        gates = []
        okdec = True
        for g in range(k):
            a = b = None
            for i in range(n + g):
                if m.get(sel_b + g * W + i):
                    a = i
                if m.get(sel2_b + g * W + i):
                    b = i
            if a is None or b is None:
                okdec = False
                break
            gates.append(('and' if m.get(g, False) else 'or', a, b))
        if not okdec:
            L('model decode failed')
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('UNKNOWN\n')
            return 0
        if two_out:
            R = len(active)
            osel_b = k + 2 * k * W + 4 * R * k
            asel_b = osel_b + W
            owire = next((w for w in range(W) if m.get(osel_b + w)), None)
            awire = next((w for w in range(W) if m.get(asel_b + w)), None)
            if owire is None or awire is None:
                L('selector decode failed')
                with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                    f.write('UNKNOWN\n')
                return 0
            tg, tout, extras = trim_cone(n, gates, owire, keep_extra=[awire])
            taux = extras[0]
            ok, viol = check_all(n, tg, tout, rows, taux)
            cand = {'spec': spec, 'n': n, 'size': len(tg), 'gates': tg, 'output': tout,
                    'aux': taux}
        else:
            tg, tout, _ = trim_cone(n, gates, n + k - 1)
            ok, viol = check_all(n, tg, tout, rows)
            cand = {'spec': spec, 'n': n, 'size': len(tg), 'gates': tg, 'output': tout}
        L(f'round {round_no}: candidate size={len(tg)}, all-rows violations={len(viol)}')
        if ok:
            cand['verified_all_rows'] = True
            with open(os.path.join(work, 'witness.json'), 'w') as f:
                json.dump(cand, f, indent=1)
            with open(os.path.join(work, 'verdict.txt'), 'w') as f:
                f.write('SAT\n')
            L(f'WITNESS: size {len(tg)} <= {k}, verified against all {len(rows)} rows')
            return 0
        add = [rows[i] for i in viol if i not in active_idx][:addcap]
        if len(active) + len(add) > maxrows:
            add = add[:max(0, maxrows - len(active))]
        active = active + add
        row_index = {id(r): i for i, r in enumerate(rows)}
        active_idx |= {row_index[id(r)] for r in add}
        L(f'round {round_no}: added {len(add)} violated rows (active={len(active)})')


if __name__ == '__main__':
    sys.exit(main())