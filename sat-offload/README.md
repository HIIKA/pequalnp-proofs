# sat-offload — the GH-Actions cloud SAT farm

Reusable SAT offload for the pequalnp backlog. Heavy SAT NEVER runs locally
(no WSL, no long local grinds — standing user order); this branch turns our
public fork (HIIKA/pequalnp-proofs) into a SAT farm: GitHub-hosted runners,
360 min/job, ~20 concurrent jobs on the free tier, results as artifacts.

## Design

- Workflow: `.github/workflows/sat-offload.yml` — **manual dispatch only**
  (`workflow_dispatch`), one job `sat` on `ubuntu-24.04` (pinned image).
- **Fork-only guard**: the job has `if: github.repository == 'HIIKA/pequalnp-proofs'`
  — it never runs in any other repository, and it is never triggered by pushes
  or PRs, so it cannot fire in upstream even if this branch were ever copied there.
- Inputs: `label` (artifact name), `cnf` (repo path | https URL | empty →
  generate), `n`/`s`/`mask` (generate + decode/verify context), `rows`
  (`all` | `essential`), `mode` (`solve` | `witness` | `lrat`), `extra_args`,
  `timeout_minutes` (≤ 350), `expect` (`SAT`/`UNSAT`/`any` → red job on mismatch).
- Solver: **cadical pinned at tag `rel-3.1.0`** (the fleet's local version),
  built from source with `./configure && make` (release defaults: `-O3 -DNDEBUG`),
  cached across runs (`.cadical/cadical`, key `cadical-rel-3.1.0-ubuntu-24.04-v1`).
  Its verified CLI surface: configs `--plain`/`--unsat`/`--sat`; options
  `--seed`, `--elim`, `--lrat`, `--no-binary`; flags `-w/-n/-q/-t`;
  positional `[<input> [<proof>]]`.
- Modes (exactly the fleet's proven local invocations):
  - `solve`:   `cadical --seed=2 -n <cnf>` — decision only.
  - `witness`: `cadical --seed=2 --elim=false -w model <cnf>` — `--elim=false` is
    REQUIRED for a complete model (bounded variable elimination drops vars and
    starves the decode; on n=6 it removed ~3/4 of the vars). The model is decoded
    and, when `mask` is given, **verified on all 2^n rows** on the runner.
  - `lrat`:    `cadical -n --seed=2 --unsat --lrat --no-binary <cnf> proof.lrat`
    — UNSAT LRAT certificate (RUP hints, ASCII), gzipped into the artifact.
- Verdict = the `s SATISFIABLE` / `s UNSATISFIABLE` line only (from the `-w`
  file in witness mode, else stdout); a GNU-timeout kill yields `TIMEOUT`
  (rc 124/137) and never a fake UNSAT.
- Artifact `sat-<label>`: verdict.txt, solve.log, solve_tail, model (gz),
  witness.json (decoded + verified circuit, hand15.json gate format),
  proof.lrat (gz), input.cnf (gz), cnf_header, gen.log, driver.log,
  cadical_version.txt, verify.err. Uploaded `if: always()`.

## Dispatch examples

```bash
# smoke: 8399 piece p_00_8 (gate-0 AND(x0,w8) reads its own wire: known UNSAT, <1s)
gh workflow run sat-offload.yml --repo HIIKA/pequalnp-proofs --ref sat-offload \
  -f label=smoke-8399-p00x8 -f cnf=sat-offload/cnfs/p_00_8.cnf \
  -f mode=solve -f timeout_minutes=15 -f expect=UNSAT

# anchor: 8402 s=15 full rows — known SAT (hand15.json); decodes+verifies on-runner
gh workflow run sat-offload.yml --repo HIIKA/pequalnp-proofs --ref sat-offload \
  -f label=8402-s15-anchor -f cnf=sat-offload/cnfs/mask_15.cnf -f mode=witness \
  -f n=8 -f s=15 -f mask=115792089237316195423570985008687437700436316516407802162747861043449034369768 \
  -f timeout_minutes=240 -f expect=SAT

# real: 8402 s=14 full rows (hours)
gh workflow run sat-offload.yml --repo HIIKA/pequalnp-proofs --ref sat-offload \
  -f label=8402-s14-full -f cnf=sat-offload/cnfs/mask_14.cnf -f mode=witness \
  -f n=8 -f s=14 -f mask=115792089237316195423570985008687437700436316516407802162747861043449034369768 \
  -f timeout_minutes=350 -f expect=any
```

## Provenance (byte-pinned instances)

| file | sha256 | what |
|---|---|---|
| `cnfs/p_00_8.cnf` | `83c405a3…c22c61197` | 8399 g8_14 + units `1 0; 4201 0; 8409 0` (gate0 = AND(x0,w8)); UNSAT <1s |
| `cnfs/mask_14.cnf` | `e252b21b…d838acff1a2b` | 8402 full-256-row s=14 (42000 vars, 229339 clauses) |
| `cnfs/mask_15.cnf` | `b079b24f…461e028c53` | 8402 full-256-row s=15 (44960 vars, 257476 clauses) |

- 8402 MASK = `115792089237316195423570985008687437700436316516407802162747861043449034369768`
  (edge function of G = 0-1 0-2 0-3 0-4 1-2 1-5 3-4 3-6 5-6 5-7 6-7).
- 8399 MASK = `115792089237316195423570985008687439529794315870556048435324087954308648856296`
  (edge function of G = 0-1 0-2 0-3 0-4 1-2 1-5 2-6 3-4 3-7 5-7 6-7).
- `tools/genmask.py` regenerates both CNFs **byte-identically** (verified:
  `genmask.py 8 14 <8402-MASK>` == `cnfs/mask_14.cnf`, same for s=15) — so the
  farm can also generate instances from `(n, s, mask)` directly (used for the
  N=6 queue; `rows=essential` selects minterms + maximal false points).

## Security / etiquette

- This branch lives **only in the fork**. Never open a PR to
  `open-goat/pequalnp-proofs` from `sat-offload` (it carries multi-MB CNF
  payloads; upstream PRs are one Lean file each). Upstream's own workflows
  (`advisory.yml` on pull_request, `authoritative.yml` on dispatch) are never
  triggered by pushes to fork branches.
- Token usage: all local commands go through the `gh` CLI (keyring token,
  scopes `repo`, `workflow`, `gist`). Used for: `git push` of this branch
  (HTTPS + gh credential helper), `gh workflow run` (dispatch), `gh run
  view/watch` (status), `gh run download` (artifacts). Nothing is embedded in
  the workflow; the runner gets only the default ephemeral `GITHUB_TOKEN`,
  workflow `permissions: contents: read`.
- The runner executes solver code only from the pinned cadical tag plus the
  scripts in `sat-offload/tools/` — no untrusted code paths, no secrets.

## Queue plan (dispatch order once a run type proves out)

1. **8402** — `s=15` anchor (expect SAT+verified) → **`s=14` full attempt**
   (`label=8402-s14-full`): SAT ⇒ a ≤14-gate witness refutes the row's statement
   (artifact `witness.json` → `build_lean.py` → PR L-meta-8402); UNSAT ⇒ the row
   is a dud (min = 15 = bound; statement false) — release `statement_seems_false`
   with the run URLs as evidence. On TIMEOUT: re-dispatch with seed sweeps
   (`-f extra_args="--seed=<p>"`, new `label` each time; ~20 jobs in parallel).
2. **8399** — (a) `s=14` full-row UNSAT hunt on `g8_14` (generate from the 8399
   MASK, `mode=lrat`, seed sweep across jobs); (b) the 82-piece cube attack in
   parallel batches (~20 jobs at a time, `expect=UNSAT` per piece; any piece SAT
   ⇒ statement FALSE, witness decodes via `mode=witness` re-run of that piece);
   (c) small-row-subset UNSAT hunt (21–46 rows via `genrows`-style row lists) for
   a ≤512 KB LRAT certificate — the only route to a submittable Lean file.
3. **N=6 sweep** (45 rows) — per row from `wave3_state.md`: (a) k-ladder on
   generated full-rows CNFs (s = 0..vmax+1, `mode=solve`), (b) witness at s=k
   (`mode=witness`, mask from `wave3_state.md`, `--elim=false` already default),
   (c) essential-rows `mode=lrat` UNSAT at s=k−1 for the lower certificate; drop
   `s_<k>.model` + `mask_<k-1>.lrat` + `{id, mask, vmax, k}` into the ktable and
   run `wave3.py` locally for the Lean assembly + submission.