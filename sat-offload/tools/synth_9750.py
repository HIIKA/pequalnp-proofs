#!/usr/bin/env python3
r"""L-meta-9750 exact synthesis: AND/OR/NOT fan-in-2, <= K gates, 12-var 16-edge graph.

Row L-meta-9750 (w55): no AND/OR/NOT fan-in-2 circuit of <= 20 gates computes
  F(x) = OR over the 16 edges (i,j) of (x_i && x_j)
on 12 variables (edges 0-7 0-11 1-6 1-10 1-11 2-9 2-10 3-8 3-9 3-11 4-7 4-8
4-10 5-6 5-7 5-9; bipartite {0..5}/{6..11}, triangle-free, C4-free, tau=6).
K=20 UNSAT over the full 4096-row table settles the row TRUE solver-level;
K=21 SAT is the desk's own upper bound (the embedded 21-gate star construction;
min_mono = 21 = E + tau - 1, the C4-free star-cover bound, attained).

Encoder: the validated fixed-padding <=K form (row11293/synth_11293.py lineage):
any <=K circuit deletes dead gates and pads with AND[wire0, NONE] copies, so WLOG
every gate is (read by a later gate or the output) or has the padding form.
Live AND/OR gates read 2 real earlier wires in canonical slot order (NONE last);
a NOT gate reads one real wire in slot0, slot1 = NONE (GateOp.not = !(headD false)).
UNBOUNDED NOTs (the row's basis) unless mono=1.

Controls (control=1, default), all must pass before any solve:
 (a) the 21-gate construction is bigint-simulated against all 4096 rows;
 (b) a complete-assignment check of EVERY clause of a small-row K=21 encoding
     (validates op/slot/NONE/padding/liveness/output semantics);
 (c) a complete-assignment check of a K=3 NOT-circuit encoding with target
     g = x0 && !x1 (validates the NOT clauses: op var, slot1=NONE forcing,
     NONE identities, V = !A, liveness with a NOT gate).

Modes (extra args, k=v,...):
  mode=direct   one cadical shot on the row set (default; rows=all is decisive)
  mode=cegar    growing rows from the scenario seed; subset-UNSAT is DECISIVE
  mode=control  controls only, no solve
  rows=all|scen|<N>      row set for direct mode (default all)
  mono=1        forbid NOT gates (the monotone question; scenario-sound)
  out=<wire>    pin the output wire (cube shard)
  op<i>=<op>    fix gate i's op (cube shard), e.g. op19=or
  notmin=1      force >= 1 NOT gate
  seed=<s>      cadical seed (default 2)
  roundsec=<s>  cegar per-round cap (default 1800)
  addcap=<n>    cegar row add cap (default 512)
  elim=1        omit --elim=false (full preprocessing; UNSAT-only runs)
  control=0     skip the control checks

Env: SAT_N=9750, SAT_S=K, SAT_TIMEOUT_MIN, SAT_CADICAL, SAT_EXTRA_ARGS.
argv[1] = work dir. Writes verdict.txt ('SAT'|'UNSAT'|'UNKNOWN'|'CONTROL-FAIL'),
witness.json (SAT), cegar.log, info.json, input.cnf, model.
"""
import json
import os
import shlex
import subprocess
import sys
import time

EDGES = [(0, 7), (0, 11), (1, 6), (1, 10), (1, 11), (2, 9), (2, 10), (3, 8),
         (3, 9), (3, 11), (4, 7), (4, 8), (4, 10), (5, 6), (5, 7), (5, 9)]
N = 12
NROWS = 1 << N
MASK = (1 << NROWS) - 1

# the 21-gate star construction (canonical slot order), output wire 32
CONTROL_GATES = [
    ('or', 7, 11), ('and', 0, 12), ('or', 6, 10), ('or', 11, 14), ('and', 1, 15),
    ('or', 9, 10), ('and', 2, 17), ('or', 8, 9), ('or', 11, 19), ('and', 3, 20),
    ('or', 7, 8), ('or', 10, 22), ('and', 4, 23), ('or', 6, 7), ('or', 9, 25),
    ('and', 5, 26), ('or', 13, 16), ('or', 18, 28), ('or', 21, 29), ('or', 24, 30),
    ('or', 27, 31)]
CONTROL_OUT = 32

# the K=2 NOT-circuit control: g = x0 && !x1  (gates: NOT[1], AND[0,12]; no padding)
NOT_CONTROL_GATES = [('not', 1, None), ('and', 0, 12)]
NOT_CONTROL_OUT = 13
NOT_CONTROL_ROWS = list(range(16))


def not_control_target(row):
    return 1 if ((row & 1) and not ((row >> 1) & 1)) else 0


def F(row):
    for (i, j) in EDGES:
        if (row >> i) & 1 and (row >> j) & 1:
            return 1
    return 0


F_TABLE = sum(F(r) << r for r in range(NROWS))
MIN_ONES = sorted((1 << i) | (1 << j) for (i, j) in EDGES)


def _maximal_independent_sets():
    mis = []
    for s in range(NROWS):
        if any((s >> i) & 1 and (s >> j) & 1 for (i, j) in EDGES):
            continue
        if not any(t != s and (s & t) == s and
                   not any((t >> i) & 1 and (t >> j) & 1 for (i, j) in EDGES)
                   for t in range(NROWS)):
            mis.append(s)
    return mis


MAX_ZEROS = _maximal_independent_sets()
SCEN = MIN_ONES + MAX_ZEROS


# ---------------- bigint simulation (candidate verification) ----------------


def input_tables():
    return [sum(((r >> i) & 1) << r for r in range(NROWS)) for i in range(N)]


def simulate(gates):
    """gates: (op, a, b) triples; a/b None = absent slot. Returns wire tables."""
    w = input_tables()
    for op, a, b in gates:
        if op == 'not':
            va = w[a] if a is not None else 0
            v = (~va) & MASK
        elif op == 'and':
            va = w[a] if a is not None else MASK
            vb = w[b] if b is not None else MASK
            v = va & vb
        else:
            va = w[a] if a is not None else 0
            vb = w[b] if b is not None else 0
            v = va | vb
        w.append(v)
    return w


def viol_rows(gates, outwire):
    w = simulate(gates)
    got = w[outwire] if outwire < len(w) else 0
    diff = got ^ F_TABLE
    return [r for r in range(NROWS) if (diff >> r) & 1]


def sim_row(gates_padded, row):
    """Wire values (0/1 list, length N+len(gates_padded)) of a control circuit."""
    wires = [(row >> i) & 1 for i in range(N)]
    for op, a, b in gates_padded:
        if op == 'not':
            va = wires[a] if a is not None else 0
            v = 1 - va
        elif op == 'and':
            va = wires[a] if a is not None else 1
            vb = wires[b] if b is not None else 1
            v = va & vb
        else:
            va = wires[a] if a is not None else 0
            vb = wires[b] if b is not None else 0
            v = va | vb
        wires.append(v)
    return wires


def slot_val(gate, wires, which):
    """Control value of the A/B auxiliary: the encoder's NONE identity.
    which=0 -> slot0 (A), which=1 -> slot1 (B)."""
    op, a, b = gate
    w = a if which == 0 else b
    if w is not None:
        return wires[w]
    # NONE identities per op (must match the encoder's NONE clauses):
    # and -> true (identity), or -> false, not -> true (!false)
    return 1 if op in ('and', 'not') else 0


# ---------------- CNF encoder (streaming, control-checked) ----------------


class ControlFail(Exception):
    pass


class Enc:
    def __init__(self, path, control=None):
        self.f = open(path, 'w', buffering=1 << 20)
        self.nv = 0
        self.ncl = 0
        self.assign = control  # dict var(1-based) -> bool, or None

    def new(self, val):
        self.nv += 1
        if self.assign is not None:
            self.assign[self.nv] = val
        return self.nv

    def add(self, lits):
        if self.assign is not None:
            sat = unknown = False
            for l in lits:
                bv = self.assign.get(l if l > 0 else -l)
                if bv is None:
                    unknown = True
                elif bv == (l > 0):
                    sat = True
                    break
            if not sat and not unknown:
                self.f.close()
                raise ControlFail(f'clause falsified by control: {lits[:10]}')
        self.f.write(' '.join(map(str, lits)) + ' 0\n')
        self.ncl += 1


def build_cnf(path, K, rows, allow_not, cube_ops=None, out_wire=None,
              notmin=False, control_gates=None, control_out=None, target=None):
    """Streaming DIMACS build. target: row -> 0/1 (default F); used with
    control_gates for the tiny NOT control. Returns (nvars, nclauses, info)."""
    if target is None:
        target = F
    body = path + '.body'
    control = {} if control_gates is not None else None
    cgate = None
    ctrl_wires = None
    if control_gates is not None:
        cgate = list(control_gates[:K])
        for _ in range(len(control_gates), K):
            cgate.append(('and', 0, None))  # padding AND[0, NONE]
        ctrl_wires = [sim_row(cgate, row) for row in rows]
        assert control_out is not None
    e = Enc(body, control)
    ops, s0v, s1v, pads = [], [], [], []
    val = {}
    for r_i, row in enumerate(rows):
        for i in range(N):
            v = e.new((row >> i) & 1 == 1)
            val[(r_i, i)] = v
            e.add([v if (row >> i) & 1 else -v])
    for i in range(K):
        nw = N + i
        cand = list(range(nw)) + [None]
        cop = cgate[i][0] if cgate is not None else None
        d = {}
        for opn in ('and', 'or', 'not'):
            if opn == 'not' and not allow_not:
                continue
            d[opn] = e.new(cop == opn)
        e.add(list(d.values()))
        for x in d.values():
            for y in d.values():
                if x < y:
                    e.add([-x, -y])
        ops.append(d)
        ca = cgate[i][1] if cgate is not None else None
        cb = cgate[i][2] if cgate is not None else None
        s0 = {}
        s1 = {}
        for w in range(nw):
            s0[w] = e.new(ca == w)
            s1[w] = e.new(cb == w)
        s0[None] = e.new(ca is None)
        s1[None] = e.new(cb is None)
        for dd in (s0, s1):
            e.add(list(dd.values()))
            for x in dd.values():
                for y in dd.values():
                    if x < y:
                        e.add([-x, -y])
        s0v.append(s0)
        s1v.append(s1)
        pad = e.new(cgate is not None and i >= len(control_gates))
        pads.append(pad)
        for c0 in cand:
            for c1 in cand:
                if cand.index(c0) > cand.index(c1):
                    e.add([-s0[c0], -s1[c1]])
        if allow_not:
            for w1 in cand:
                if w1 is not None:
                    e.add([-d['not'], -s1[w1]])
        e.add([-pad, d['and']])
        e.add([-pad, s0[0]])
        e.add([-pad, s1[None]])
        for opn in ('and', 'or'):
            e.add([pad, -d[opn], -s1[None]])
            for w in range(nw):
                e.add([pad, -d[opn], -s0[w], -s1[w]])
        for r_i, row in enumerate(rows):
            cw = ctrl_wires[r_i] if ctrl_wires is not None else None
            V = e.new(cw is not None and cw[N + i] == 1)
            val[(r_i, N + i)] = V
            A = e.new(cw is not None and slot_val(cgate[i], cw, 0) == 1)
            B = e.new(cw is not None and slot_val(cgate[i], cw, 1) == 1)
            val[('A', r_i, i)] = A
            val[('B', r_i, i)] = B
            for w in range(nw):
                wv = val[(r_i, w)]
                e.add([-s0[w], -A, wv])
                e.add([-s0[w], A, -wv])
                e.add([-s1[w], -B, wv])
                e.add([-s1[w], B, -wv])
            e.add([-d['and'], -s0[None], A])
            e.add([-d['and'], -s1[None], B])
            e.add([-d['or'], -s0[None], A])
            e.add([-d['or'], -s1[None], B])
            if allow_not:
                e.add([-d['not'], -s0[None], A])
                e.add([-d['not'], -s1[None], B])
            e.add([-d['and'], -V, A])
            e.add([-d['and'], -V, B])
            e.add([-d['and'], V, -A, -B])
            e.add([-d['or'], -A, V])
            e.add([-d['or'], -B, V])
            e.add([-d['or'], A, B, -V])
            if allow_not:
                e.add([-d['not'], -A, -V])
                e.add([-d['not'], A, V])  # V = !A: (A or V) and (not-A or not-V); the 11293 lineage had -V here = NOT gates forced to 0
    oc = {w: e.new(cgate is not None and w == control_out) for w in range(N + K)}
    e.add(list(oc.values()))
    for x in oc.values():
        for y in oc.values():
            if x < y:
                e.add([-x, -y])
    for i in range(K):
        wme = N + i
        lits = [pads[i], oc[wme]]
        for j in range(i + 1, K):
            lits.append(s0v[j][wme])
            lits.append(s1v[j][wme])
        e.add(lits)
    if notmin:
        nl = [ops[i]['not'] for i in range(K) if 'not' in ops[i]]
        if not nl:
            e.add([])  # mono+notmin: impossible
        else:
            e.add(nl)
    if cube_ops:
        for gi, opname in sorted(cube_ops.items()):
            if opname == 'not' and not allow_not:
                e.add([])
            else:
                e.add([ops[gi][opname]])
    if out_wire is not None:
        e.add([oc[out_wire]])
    for r_i, row in enumerate(rows):
        O = e.new(target(row) == 1)
        val[('O', r_i)] = O
        for w in range(N + K):
            e.add([-oc[w], -O, val[(r_i, w)]])
            e.add([-oc[w], O, -val[(r_i, w)]])
        e.add([O if target(row) else -O])
    e.f.close()
    with open(body) as fb:
        data = fb.read()
    with open(path, 'w', buffering=1 << 20) as f:
        f.write(f'p cnf {e.nv} {e.ncl}\n')
        f.write(data)
    os.remove(body)
    return e.nv, e.ncl, (ops, s0v, s1v, oc, pads, val)


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


def decode(model, K, info, allow_not):
    ops, s0v, s1v, oc, pads, val = info
    gates = []
    for i in range(K):
        opname = None
        for o, l in ops[i].items():
            if model.get(l - 1):
                opname = o
        if opname is None:
            return None
        a = None
        b = None
        for w, l in s0v[i].items():
            if model.get(l - 1):
                a = w
        for w, l in s1v[i].items():
            if model.get(l - 1):
                b = w
        if a is None:
            return None
        gates.append((opname, a, b))
    output = None
    for w, l in oc.items():
        if model.get(l - 1):
            output = w
    if output is None:
        return None
    return gates, output


def trim_cone(gates, outwire):
    keep = set()
    stack = [outwire]
    while stack:
        w = stack.pop()
        if w < N:
            continue
        g = w - N
        if g < 0 or g >= len(gates) or g in keep:
            continue
        keep.add(g)
        op, a, b = gates[g]
        if a is not None:
            stack.append(a)
        if b is not None:
            stack.append(b)
    order = sorted(keep)
    remap = {N + g: N + new for new, g in enumerate(order)}
    out2 = []
    for g in order:
        op, a, b = gates[g]
        a2 = a if a is None or a < N else remap.get(a, a)
        b2 = b if b is None or b < N else remap.get(b, b)
        out2.append((op, a2, b2))
    outwire2 = outwire if outwire < N else remap.get(outwire, outwire)
    return out2, outwire2


# ---------------- main ----------------


def main():
    work = sys.argv[1] if len(sys.argv) > 1 else '.'
    os.makedirs(work, exist_ok=True)
    K = int(os.environ.get('SAT_S', '20'))
    budget_min = float(os.environ.get('SAT_TIMEOUT_MIN', '350'))
    cad = os.environ.get('SAT_CADICAL', 'cadical')
    extra = {}
    for kv in os.environ.get('SAT_EXTRA_ARGS', '').split(','):
        if '=' in kv:
            a, b = kv.split('=', 1)
            extra[a.strip()] = b.strip()
    mode = extra.get('mode', 'direct')
    rowspec = extra.get('rows', 'all')
    mono = extra.get('mono', '0') == '1'
    allow_not = not mono
    seed = extra.get('seed', '2')
    roundsec = int(extra.get('roundsec', '1800'))
    addcap = int(extra.get('addcap', '512'))
    do_control = extra.get('control', '1') == '1'
    elim_false = extra.get('elim', '0') != '1'
    cube_ops = {}
    out_wire = None
    notmin = extra.get('notmin', '0') == '1'
    for k, v in extra.items():
        if k.startswith('op') and k[2:].isdigit():
            cube_ops[int(k[2:])] = v
    if extra.get('out'):
        out_wire = int(extra['out'])
    log = open(os.path.join(work, 'cegar.log'), 'w', buffering=1 << 16)

    def L(*a):
        msg = ' '.join(str(x) for x in a)
        print(msg, flush=True)
        log.write(msg + '\n')
        log.flush()

    t0 = time.time()

    def write_verdict(v, extra_info=None):
        with open(os.path.join(work, 'verdict.txt'), 'w') as f:
            f.write(v + '\n')
        info = {'row': 'L-meta-9750', 'K': K, 'mode': mode, 'rows': rowspec,
                'mono': mono, 'cube_ops': cube_ops, 'out': out_wire,
                'notmin': notmin, 'seed': seed,
                'elapsed_s': round(time.time() - t0, 1), 'verdict': v}
        if extra_info:
            info.update(extra_info)
        with open(os.path.join(work, 'info.json'), 'w') as f:
            json.dump(info, f, indent=1)

    L(f'9750: K={K} mode={mode} rows={rowspec} mono={mono} cube={cube_ops} '
      f'out={out_wire} notmin={notmin} seed={seed} budget={budget_min}m')
    L(f'graph: {len(EDGES)} edges; scen = {len(MIN_ONES)} min-ones + {len(MAX_ZEROS)} max-zeros')

    if do_control:
        # (a) construction computes F on ALL rows
        cv = viol_rows(CONTROL_GATES, CONTROL_OUT)
        if cv:
            L(f'CONTROL (a) FAILED: construction violates {len(cv)} rows')
            write_verdict('CONTROL-FAIL')
            return 2
        L('control (a): 21-gate construction exact on all 4096 rows OK')
        # (b) K=21 complete-assignment clause check on a small row set
        try:
            rows_b = sorted(set(SCEN[: 120] + [r for r in range(0, NROWS, 97)]))
            nb, cb, _ = build_cnf(os.path.join(work, 'control_b.cnf'), 21, rows_b,
                                  True, control_gates=CONTROL_GATES,
                                  control_out=CONTROL_OUT)
            L(f'control (b): K=21 encoding control checked all {cb} clauses OK')
            os.remove(os.path.join(work, 'control_b.cnf'))
        except ControlFail as ex:
            L(f'CONTROL (b) FAILED: {ex}')
            write_verdict('CONTROL-FAIL')
            return 2
        # (c) K=2 NOT-circuit complete-assignment check (NOT semantics)
        try:
            nc, cc, _ = build_cnf(os.path.join(work, 'control_c.cnf'), 2,
                                  NOT_CONTROL_ROWS, True,
                                  control_gates=NOT_CONTROL_GATES,
                                  control_out=NOT_CONTROL_OUT,
                                  target=not_control_target)
            L(f'control (c): K=2 NOT-circuit encoding control checked all {cc} clauses OK')
            os.remove(os.path.join(work, 'control_c.cnf'))
        except ControlFail as ex:
            L(f'CONTROL (c) FAILED: {ex}')
            write_verdict('CONTROL-FAIL')
            return 2
        # (d) K=21 mono-mode (allow_not=False) complete-assignment check
        try:
            nd, cd, _ = build_cnf(os.path.join(work, 'control_d.cnf'), 21, rows_b,
                                  False, control_gates=CONTROL_GATES,
                                  control_out=CONTROL_OUT)
            L(f'control (d): K=21 mono-mode encoding control checked all {cd} clauses OK')
            os.remove(os.path.join(work, 'control_d.cnf'))
        except ControlFail as ex:
            L(f'CONTROL (d) FAILED: {ex}')
            write_verdict('CONTROL-FAIL')
            return 2

    if rowspec == 'all':
        base_rows = list(range(NROWS))
    elif rowspec == 'scen':
        base_rows = list(SCEN)
    else:
        base_rows = list(range(NROWS))[:int(rowspec)]

    if mode == 'control':
        write_verdict('CONTROL-OK', {'note': 'controls only, no solve'})
        return 0

    cnf_path = os.path.join(work, 'input.cnf')
    model_path = os.path.join(work, 'model')
    cmd0 = shlex.split(cad) if ' ' in cad else [cad]
    cmd_tail = []
    if elim_false:
        cmd_tail.append('--elim=false')
    cmd_tail += ['-w', model_path]

    def cadical_solve(cnf, cap):
        cmd = cmd0 + [f'--seed={seed}'] + cmd_tail + [cnf]
        ts = time.time()
        try:
            r = subprocess.run(cmd, capture_output=True, timeout=cap)
            rc = r.returncode
        except subprocess.TimeoutExpired:
            return 'TIMEOUT', time.time() - ts
        if rc == 20:
            return 'UNSAT', time.time() - ts
        if rc == 10:
            return 'SAT', time.time() - ts
        return f'UNKNOWN-rc{rc}', time.time() - ts

    if mode == 'direct':
        rows = base_rows
        t_enc = time.time()
        cg = CONTROL_GATES if (K >= 21 and do_control) else None
        nv, ncl, info = build_cnf(cnf_path, K, rows, allow_not, cube_ops,
                                  out_wire, notmin, control_gates=cg,
                                  control_out=CONTROL_OUT if cg else None)
        if cg:
            L(f'direct: K=21 encoding control checked all {ncl} clauses OK')
        L(f'direct: rows={len(rows)} vars={nv} clauses={ncl} enc={time.time()-t_enc:.1f}s')
        remaining = budget_min * 60 - (time.time() - t0) - 60
        if remaining <= 60:
            L('budget exhausted before solve')
            write_verdict('UNKNOWN')
            return 0
        verdict, dt = cadical_solve(cnf_path, remaining)
        L(f'direct: {verdict} in {dt:.1f}s')
        if verdict == 'UNSAT':
            L(f'UNSAT on {len(rows)} rows => NO <= {K}-gate '
              f'({"monotone" if mono else "AND/OR/NOT"}) circuit'
              f'{", cube " + str(cube_ops) if cube_ops else ""}'
              f'{", out=" + str(out_wire) if out_wire is not None else ""}')
            write_verdict('UNSAT')
            return 0
        if verdict == 'SAT':
            m = read_model(model_path)
            dec = decode(m, K, info, allow_not)
            if dec is None:
                L('model decode failed')
                write_verdict('UNKNOWN')
                return 0
            gates, output = dec
            tg, tout = trim_cone(gates, output)
            v = viol_rows(tg, tout)
            L(f'SAT: live core {len(tg)} gates, output {tout}, full-table violations {len(v)}')
            with open(os.path.join(work, 'witness.json'), 'w') as f:
                json.dump({'row': 'L-meta-9750', 'K': K, 'size': len(tg),
                           'gates': tg, 'output': tout,
                           'verified_all_rows': len(v) == 0,
                           'violations': v[:64]}, f, indent=1)
            if not v:
                L(f'WITNESS: {len(tg)} <= {K} gates verified on all 4096 rows '
                  f'=> min <= {K}; the row L-meta-9750 is '
                  f'{"FALSE (a <=20 circuit exists)" if K <= 20 else "consistent"}')
                write_verdict('SAT')
            else:
                L('model violates the full table (subset-instance candidate only)')
                write_verdict('UNKNOWN')
            return 0
        write_verdict('UNKNOWN')
        return 0

    if mode == 'cegar':
        active = list(SCEN)
        active_idx = set(active)
        rnd = 0
        while True:
            rnd += 1
            remaining = budget_min * 60 - (time.time() - t0)
            if remaining <= 90:
                L('budget exhausted')
                write_verdict('UNKNOWN', {'rounds': rnd, 'active_rows': len(active)})
                return 0
            cap = min(roundsec, int(remaining) - 60)
            t_enc = time.time()
            cg = CONTROL_GATES if (rnd == 1 and K >= 21 and do_control) else None
            nv, ncl, info = build_cnf(cnf_path, K, active, allow_not, cube_ops,
                                      out_wire, notmin, control_gates=cg,
                                      control_out=CONTROL_OUT if cg else None)
            if cg:
                L(f'cegar r{rnd}: K=21 encoding control checked all {ncl} clauses OK')
            L(f'cegar r{rnd}: rows={len(active)} vars={nv} clauses={ncl} '
              f'enc={time.time()-t_enc:.1f}s cap={cap}s')
            verdict, dt = cadical_solve(cnf_path, cap)
            L(f'cegar r{rnd}: {verdict} in {dt:.1f}s')
            if verdict == 'UNSAT':
                L(f'UNSAT on {len(active)} of {NROWS} rows -> NO circuit of size <= {K} '
                  f'(sound: subset-UNSAT is decisive)')
                write_verdict('UNSAT', {'rounds': rnd, 'active_rows': len(active)})
                return 0
            if verdict != 'SAT':
                write_verdict('UNKNOWN', {'rounds': rnd, 'active_rows': len(active)})
                return 0
            m = read_model(model_path)
            dec = decode(m, K, info, allow_not)
            if dec is None:
                L('model decode failed')
                write_verdict('UNKNOWN', {'rounds': rnd, 'active_rows': len(active)})
                return 0
            gates, output = dec
            tg, tout = trim_cone(gates, output)
            v = viol_rows(tg, tout)
            L(f'cegar r{rnd}: candidate live size={len(tg)}, violations={len(v)}')
            if not v:
                with open(os.path.join(work, 'witness.json'), 'w') as f:
                    json.dump({'row': 'L-meta-9750', 'K': K, 'size': len(tg),
                               'gates': tg, 'output': tout,
                               'verified_all_rows': True}, f, indent=1)
                L(f'WITNESS: {len(tg)} <= {K} gates verified on all 4096 rows => row FALSE')
                write_verdict('SAT', {'rounds': rnd, 'active_rows': len(active)})
                return 0
            add = [r for r in v if r not in active_idx][:addcap]
            if not add:
                L('violations persist but no new rows to add: logic error')
                write_verdict('CONTROL-FAIL', {'rounds': rnd,
                                               'active_rows': len(active)})
                return 2
            active += add
            active_idx |= set(add)
            L(f'cegar r{rnd}: added {len(add)} rows (active={len(active)})')

    L('unknown mode')
    write_verdict('UNKNOWN')
    return 1


if __name__ == '__main__':
    sys.exit(main())