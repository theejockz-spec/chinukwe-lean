#!/usr/bin/env bash
# Project invariants. Run from the project root after a build:  bash scripts/check.sh
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

echo "== 1. build"
lake build 2>&1 | tee build.log
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "FAIL: build"; fail=1; }

echo "== 2. no source-level axioms in the core"
if grep -rnE '^\s*(axiom|constant)\s' Chinukwe Chinukwe.lean; then
  echo "FAIL: axiom found in core"; fail=1
fi

echo "== 3. empirical boundary: nothing outside Chinukwe/Empirical* imports it"
if grep -rnE '^import +Chinukwe\.Empirical' Chinukwe Chinukwe.lean | grep -v '^Chinukwe/Empirical'; then
  echo "FAIL: core imports Chinukwe.Empirical"; fail=1
fi
if grep -rnE '^import +Conjectures' Chinukwe Chinukwe.lean; then
  echo "FAIL: core imports Conjectures"; fail=1
fi

echo "== 4. sorry whitelist (files)"
grep -E "declaration uses .?sorry.?" build.log \
  | sed -E 's#^[^ ]+ ([A-Za-z]+[\\/][A-Za-z0-9_\\/]*\.lean):.*$#\1#' | tr '\\' '/' | sort -u > /tmp/sorry-files.txt
bad=$(comm -23 /tmp/sorry-files.txt <(sort scripts/sorry-whitelist.txt))
if [ -n "$bad" ]; then echo "FAIL: unexpected sorry in:"; echo "$bad"; fail=1; fi

echo "== 5. axiom audit"
lake env lean scripts/AxiomAudit.lean > audit.log 2>&1 || true
cat audit.log
if grep "depends on axioms" audit.log | grep -vE "^'[^']+' depends on axioms: \[(propext|Classical\.choice|Quot\.sound|sorryAx)(, (propext|Classical\.choice|Quot\.sound|sorryAx))*\]$"; then
  echo "FAIL: non-standard axiom"; fail=1
fi
grep "sorryAx" audit.log | sed -E "s/^'([^']+)'.*/\1/" | sort -u > /tmp/dep.txt
bad=$(comm -23 /tmp/dep.txt <(sort scripts/sorry-dependents.txt))
if [ -n "$bad" ]; then echo "FAIL: unexpected sorry dependents:"; echo "$bad"; fail=1; fi

if [ "$fail" -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "CHECKS FAILED"; exit 1; fi
