#!/usr/bin/env python3
"""Decode a cadical model of a genmask.py circuit-link CNF and verify the circuit.

Usage: decode_verify.py <model-file> <n> <s> <mask-or-'-'> [out.json]

Byte-mirror of the fleet's proven decode (sweep8402.py / build_row.py):
  A = 2^n + n + s + 2; DIMACS var = ix+1; ix(kd,j,a) = (kd*(s+1)+j)*A + a;
  ops 0=AND 1=OR 2=padding 3=NOT; padding = AND of no inputs (const true, unread);
  NOT reads src1; output wire selector = kd 6.

With a mask (decimal, bit r = f(r), big ints fine): the decoded circuit is evaluated
on ALL 2^n rows and compared against the mask — a full verification of the witness.

Exit codes: 0 decoded (+ verified, if mask given) | 1 decode failure | 2 verify mismatch.
Prints a one-line summary on stdout; writes the full report (incl. the circuit in the
fleet's hand15.json gate format) to out.json (default witness.json).
"""
import json
import sys

model_path, n, s = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
mask_arg = sys.argv[4]
out_path = sys.argv[5] if len(sys.argv) > 5 else 'witness.json'
R = 1 << n
A = R + n + s + 2
mask = None if mask_arg in ('', '-') else int(mask_arg)


def fail(code, msg):
    print('ERROR: ' + msg, file=sys.stderr)
    sys.exit(code)


if mask is not None and mask >= (1 << R):
    fail(2, 'mask needs at most %d bits' % R)

# ---- read the model (only 'v' lines carry the assignment) ----
val = set()
with open(model_path) as fh:
    for line in fh:
        if line.startswith('v'):
            for x in line.split()[1:]:
                if x != '0':
                    val.add(int(x))


def T(kd, j, a):
    return ((kd * (s + 1) + j) * A + a + 1) in val


# ---- decode gates (identical to the fleet's decode) ----
gates = []
for j in range(s):
    op = [t for t in range(4) if T(0, j, t)]
    s1 = [k for k in range(n + j + 1) if T(1, j, k)]
    s2 = [k for k in range(n + j + 1) if T(2, j, k)]
    if not (op and s1 and s2):
        fail(1, 'gate %d incomplete (op=%s s1=%s s2=%s); witness mode requires --elim=false'
             % (j, op, s1[:4], s2[:4]))
    if op[0] == 2:
        gates.append(['and', []])          # padding: AND of no inputs
    elif op[0] == 3:
        gates.append(['not', [s1[0]]])     # NOT reads the first source
    else:
        gates.append(['and' if op[0] == 0 else 'or', [s1[0], s2[0]]])
so = [k for k in range(n + s + 1) if T(6, 0, k)]
if not so:
    fail(1, 'no output wire')
circuit = {'gates': gates, 'output': so[0]}


def eval_circ(c, r):
    w = [(r >> i) & 1 == 1 for i in range(n)]
    for op, ins in c['gates']:
        v = [w[i] if i < len(w) else False for i in ins]
        w.append(all(v) if op == 'and' else
                 (any(v) if op == 'or' else (not v[0] if v else True)))
    return w[c['output']] if c['output'] < len(w) else False


n_real = sum(1 for op, ins in gates if ins)  # padding gates have no inputs

if mask is None:
    report = {'ok': True, 'verified': False, 'n': n, 's': s,
              'n_real_gates': n_real, 'n_rows_checked': 0, 'n_bad_rows': 0,
              'bad_rows': [], 'circuit': circuit}
    json.dump(report, open(out_path, 'w'), indent=1)
    print('DECODED-ONLY: %d real gates, output wire %d (no mask given; NOT verified)'
          % (n_real, so[0]))
    sys.exit(0)

bad = [r for r in range(R) if eval_circ(circuit, r) != bool((mask >> r) & 1)]
ok = not bad
report = {'ok': ok, 'verified': True, 'n': n, 's': s,
          'n_real_gates': n_real, 'n_rows_checked': R,
          'n_bad_rows': len(bad), 'bad_rows': bad[:32], 'circuit': circuit}
json.dump(report, open(out_path, 'w'), indent=1)
print('%s: %d real gates, output wire %d, %d/%d rows ok, %d bad'
      % ('VERIFIED' if ok else 'MISMATCH', n_real, so[0], R - len(bad), R, len(bad)))
sys.exit(0 if ok else 2)