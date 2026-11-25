#!/usr/bin/env bash
# sat-offload driver — runs on the GitHub runner (ubuntu-24.04), driven by SAT_* env vars.
#
# Chain: resolve CNF (committed path | https URL | genmask.py from n/s/mask)
#     -> build cadical pinned at tag rel-3.1.0 (cached across runs)
#     -> solve under GNU timeout (modes below)
#     -> verdict from the 's ' line ONLY ('s SATISFIABLE'/'s UNSATISFIABLE'; anything else is UNKNOWN/TIMEOUT)
#     -> witness mode: decode the model + verify the circuit against the mask on ALL 2^n rows
#     -> pack + leave work_out/ for the artifact upload step
#
# Modes (matching the fleet's proven local invocations):
#   solve   : cadical --seed=2 -n                     <cnf>
#   witness : cadical --seed=2 --elim=false -w model   <cnf>        (--elim=false: complete model, REQUIRED for decode)
#   lrat    : cadical -n --seed=2 --unsat --lrat --no-binary <cnf> proof.lrat
# extra_args is appended last and wins (e.g. --seed=13 overrides the default seed).
#
# Exit codes: 0 = clean verdict (matches `expect` if given); 1 = expectation mismatch
# or witness decode/verify failure (artifact is still uploaded); 2 = setup failure.

set -o pipefail

label="${SAT_LABEL:-run}"
mode="${SAT_MODE:-solve}"
cnf_in="${SAT_CNF:-}"
gen_n="${SAT_N:-}"
gen_s="${SAT_S:-}"
gen_mask="${SAT_MASK:-}"
gen_rows="${SAT_ROWS:-all}"
extra="${SAT_EXTRA_ARGS:-}"
timeout_min="${SAT_TIMEOUT_MIN:-350}"
expect="${SAT_EXPECT:-any}"

repo="$(cd "$(dirname "$0")/../.." && pwd)"
work="$repo/work_out"
mkdir -p "$work"
: > "$work/driver.log"

log() { echo "[sat_run] $*" | tee -a "$work/driver.log"; }

# ---- 0. sanity ---------------------------------------------------------------
case "$timeout_min" in
  ''|*[!0-9]*|0) log "bad timeout_minutes '$timeout_min'"; exit 2 ;;
esac
[ "$timeout_min" -le 350 ] || { log "timeout_minutes must be <= 350"; exit 2; }
case "$mode" in
  solve|witness|lrat) ;;
  *) log "bad mode '$mode'"; exit 2 ;;
esac

# ---- 1t. python synthesis-tool mode (cnf ends with .py) ------------------------
# The tool (e.g. sat-offload/tools/synth_wit.py) generates its own CNFs and drives
# cadical itself (CEGAR); it writes work_out/verdict.txt ('SAT'|'UNSAT'|'UNKNOWN'|
# 'CONTROL-FAIL'), witness.json and cegar.log. SAT_N = spec id, SAT_S = gate budget k.
if [ -n "$cnf_in" ] && case "$cnf_in" in *.py) true;; *) false;; esac; then
  [ -f "$cnf_in" ] || { log "tool not found in checkout: $cnf_in"; exit 2; }
  log "tool mode: $cnf_in (n=$gen_n s=$gen_s timeout=${timeout_min}m extra='$extra')"
  # build cadical first (same pinning as below) - the tool drives the binary itself
  CAD="$repo/.cadical/cadical"
  if [ ! -x "$CAD" ]; then
    log "building cadical from pinned tag rel-3.1.0"
    src="$repo/.cadical/src"
    mkdir -p "$repo/.cadical"
    [ -d "$src/.git" ] || git clone -q --depth 1 --branch rel-3.1.0 \
        https://github.com/arminbiere/cadical.git "$src" || { log "clone failed"; exit 2; }
    if ! ( cd "$src" \
           && ./configure > "$repo/.cadical/configure.log" 2>&1 \
           && make -j"$(nproc)" > "$repo/.cadical/make.log" 2>&1 ); then
      log "cadical build failed"; tail -n 30 "$repo/.cadical/make.log" "$repo/.cadical/configure.log" 2>/dev/null
      exit 2
    fi
    cp "$src/build/cadical" "$CAD"
  fi
  "$CAD" --version > "$work/cadical_version.txt" 2>&1 || true
  log "cadical: $(head -n 2 "$work/cadical_version.txt" | tr '\n' ' ')"
  SAT_CADICAL="$CAD" SAT_N="$gen_n" SAT_S="$gen_s" SAT_TIMEOUT_MIN="$timeout_min" \
    SAT_EXTRA_ARGS="$extra" python3 "$cnf_in" "$work" 2>&1 | tee -a "$work/driver.log"
  trc=$?
  log "tool exit code: $trc"
  verdict="UNKNOWN"
  [ -f "$work/verdict.txt" ] && verdict="$(cat "$work/verdict.txt" | tr -d '\r\n')"
  echo "$verdict" > "$work/verdict.txt"
  log "verdict: $verdict (expected: $expect)"
  verify_note="tool mode (see cegar.log)"
  [ -f "$work/witness.json" ] && verify_note="witness.json written"
  [ -f "$work/input.cnf" ] && gzip -f -9 "$work/input.cnf" 2>/dev/null || true
  [ -f "$work/model" ] && gzip -f -9 "$work/model" 2>/dev/null || true
  {
    echo "## sat-offload: $label"
    echo ""
    echo "| field | value |"
    echo "|---|---|"
    echo "| verdict | **$verdict** (expected $expect) |"
    echo "| mode | tool ($cnf_in) | tool rc | $trc |"
    echo "| cadical | $(sed -n '2p' "$work/cadical_version.txt" 2>/dev/null || head -1 "$work/cadical_version.txt") |"
    echo "| witness | $verify_note |"
    echo "| artifact | sat-$label |"
  } >> "$GITHUB_STEP_SUMMARY" 2>/dev/null || true
  if [ "$expect" = "SAT" ]   && [ "$verdict" != "SAT" ];   then log "EXPECT MISMATCH"; exit 1; fi
  if [ "$expect" = "UNSAT" ] && [ "$verdict" != "UNSAT" ]; then log "EXPECT MISMATCH"; exit 1; fi
  log "done"
  exit 0
fi

# ---- 1. resolve the CNF --------------------------------------------------------
if [ -n "$cnf_in" ]; then
  case "$cnf_in" in
    http://*|https://*)
      log "downloading CNF: $cnf_in"
      curl -fsSL --retry 3 "$cnf_in" -o "$work/input.cnf" || { log "download failed"; exit 2; } ;;
    *)
      log "using committed CNF: $cnf_in"
      [ -f "$cnf_in" ] || { log "CNF not found in checkout: $cnf_in"; exit 2; }
      cp "$cnf_in" "$work/input.cnf" ;;
  esac
else
  if [ -z "$gen_n" ] || [ -z "$gen_s" ] || [ -z "$gen_mask" ]; then
    log "need SAT_CNF or SAT_N/SAT_S/SAT_MASK"; exit 2
  fi
  rowflag=""
  [ "$gen_rows" = "essential" ] && rowflag="rows"
  log "generating CNF: genmask n=$gen_n s=$gen_s rows=$gen_rows"
  if ! python3 "$repo/sat-offload/tools/genmask.py" "$gen_n" "$gen_s" "$gen_mask" \
        "$work/input.cnf" $rowflag 2> "$work/gen.log"; then
    log "genmask failed"; cat "$work/gen.log"; exit 2
  fi
fi
[ -s "$work/input.cnf" ] || { log "input.cnf missing/empty"; exit 2; }
head -1 "$work/input.cnf" | tr -d '\r' > "$work/cnf_header.txt"
log "instance header: $(cat "$work/cnf_header.txt")"

# ---- 2. cadical, pinned at tag rel-3.1.0 (the fleet's local version) -----------
CAD="$repo/.cadical/cadical"
if [ ! -x "$CAD" ]; then
  log "building cadical from pinned tag rel-3.1.0"
  src="$repo/.cadical/src"
  mkdir -p "$repo/.cadical"
  [ -d "$src/.git" ] || git clone -q --depth 1 --branch rel-3.1.0 \
      https://github.com/arminbiere/cadical.git "$src" || { log "clone failed"; exit 2; }
  if ! ( cd "$src" \
         && ./configure > "$repo/.cadical/configure.log" 2>&1 \
         && make -j"$(nproc)" > "$repo/.cadical/make.log" 2>&1 ); then
    log "cadical build failed"; tail -n 30 "$repo/.cadical/make.log" "$repo/.cadical/configure.log" 2>/dev/null
    exit 2
  fi
  cp "$src/build/cadical" "$CAD"
fi
"$CAD" --version > "$work/cadical_version.txt" 2>&1 || true
log "cadical: $(head -n 2 "$work/cadical_version.txt" | tr '\n' ' ')"

# ---- 3. solve --------------------------------------------------------------------
secs=$(( timeout_min * 60 ))
proof=""
case "$mode" in
  witness) cad_args=(--seed=2 --elim=false -w "$work/model") ;;
  lrat)    cad_args=(-n --seed=2 --unsat --lrat --no-binary); proof="$work/proof.lrat" ;;
  *)       cad_args=(-n --seed=2) ;;
esac
if [ -n "$extra" ]; then read -r -a extra_arr <<< "$extra"; else extra_arr=(); fi
rm -f "$work/model" "$work/proof.lrat" "$work/witness.json"

log "solving: mode=$mode timeout=${timeout_min}m extra='$extra' cnf=$(basename "$cnf_in" 2>/dev/null || echo generated)"
timeout --kill-after=30s "${secs}s" \
  stdbuf -oL -eL "$CAD" ${cad_args[@]+"${cad_args[@]}"} ${extra_arr[@]+"${extra_arr[@]}"} \
  "$work/input.cnf" ${proof:+"$proof"} > "$work/solve.log" 2>&1
rc=$?
log "cadical exit code: $rc"

# ---- 4. verdict (the 's ' line is the only truth; never trust anything else) ------
verdict=UNKNOWN
first=""
if [ "$mode" = witness ] && [ -f "$work/model" ]; then
  first="$(head -n 1 "$work/model" | tr -d '\r\n')"
else
  first="$(grep -m1 '^s ' "$work/solve.log" | tr -d '\r\n')"
fi
case "$first" in
  *" SATISFIABLE")   verdict=SAT ;;
  *" UNSATISFIABLE") verdict=UNSAT ;;
  *) if [ "$rc" = "124" ] || [ "$rc" = "137" ]; then verdict=TIMEOUT; fi ;;
esac
echo "$verdict" > "$work/verdict.txt"
log "verdict: $verdict (expected: $expect)"

# ---- 5. witness decode + verify (witness mode, SAT, n and s given) ----------------
verify_note="n/a (mode=$mode)"
if [ "$mode" = witness ] && [ "$verdict" = SAT ] && [ -n "$gen_n" ] && [ -n "$gen_s" ]; then
  log "decoding witness at n=$gen_n s=$gen_s (mask verify: $([ -n "$gen_mask" ] && echo yes || echo no))"
  if summary=$(python3 "$repo/sat-offload/tools/decode_verify.py" \
        "$work/model" "$gen_n" "$gen_s" "$gen_mask" "$work/witness.json" 2> "$work/verify.err"); then
    verify_note="$summary"
    log "witness: $summary"
  else
    rc2=$?
    log "decode/verify FAILED (rc=$rc2):"
    sed -n '1,10p' "$work/verify.err" | tee -a "$work/driver.log"
    verdict="WITNESS-INVALID"
    echo "$verdict" > "$work/verdict.txt"
    verify_note="decode/verify failed (see verify.err)"
  fi
fi

# ---- 6. pack payload + step summary ------------------------------------------------
gzip -f -9 "$work/input.cnf" 2>/dev/null || true
[ -f "$work/model" ]      && gzip -f -9 "$work/model"
[ -f "$work/proof.lrat" ] && gzip -f -1 "$work/proof.lrat"   # big proofs: fast gzip
tail -n 5 "$work/solve.log" > "$work/solve_tail.txt" 2>/dev/null || true

{
  echo "## sat-offload: $label"
  echo ""
  echo "| field | value |"
  echo "|---|---|"
  echo "| verdict | **$verdict** (expected $expect) |"
  echo "| mode | $mode | cadical rc | $rc |"
  echo "| instance | $(cat "$work/cnf_header.txt" 2>/dev/null) |"
  echo "| cadical | $(sed -n '2p' "$work/cadical_version.txt" 2>/dev/null || head -1 "$work/cadical_version.txt") |"
  echo "| witness | $verify_note |"
  echo "| artifact | sat-$label |"
} >> "$GITHUB_STEP_SUMMARY" 2>/dev/null || true

# ---- 7. expectation check (LAST so the artifact always uploads) --------------------
if [ "$expect" = "SAT" ]   && [ "$verdict" != "SAT" ];   then log "EXPECT MISMATCH"; exit 1; fi
if [ "$expect" = "UNSAT" ] && [ "$verdict" != "UNSAT" ]; then log "EXPECT MISMATCH"; exit 1; fi
log "done"
exit 0