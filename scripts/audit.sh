#!/usr/bin/env bash
# Checks the two claims the papers make about this development:
#   (1) no admitted statements anywhere;
#   (2) every headline theorem is closed under the global context.
# Run from the repository root.  Exits non-zero on failure.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

echo "== (1) no admitted statements =="
hits=$(grep -rn --include='*.v' -E '(^|[^_[:alnum:]])(Admitted|admit)\.' \
         algorithm examples extraction || true)
if [ -n "$hits" ]; then
  echo "FAIL: admitted statements found:"; echo "$hits"; fail=1
else
  echo "ok: none in algorithm/, examples/, extraction/"
fi

echo
echo "== (2) axiom audit =="
if [ ! -d _build/default/algorithm ]; then
  echo "FAIL: run 'dune build' first (_build/default/algorithm missing)"; exit 1
fi

list=scripts/audit_theorems.txt
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
src=$tmp/Audit.v
: > "$src"
awk '!/^[[:space:]]*(#|$)/ {print $1}' "$list" | sort -u |
  while read -r m; do echo "Require Import $m." >> "$src"; done
awk '!/^[[:space:]]*(#|$)/ {print $2}' "$list" |
  while read -r n; do echo "Print Assumptions $n." >> "$src"; done

out=$(coqc -R _build/default/algorithm Semiring \
           -R _build/default/examples Examples \
           "$src" 2>&1) || { echo "FAIL: audit file did not compile:"; echo "$out"; exit 1; }

expected=$(awk '!/^[[:space:]]*(#|$)/' "$list" | wc -l | tr -d ' ')
closed=$(printf '%s\n' "$out" | grep -c 'Closed under the global context' || true)
echo "theorems checked: $expected, reported closed: $closed"
if [ "$closed" -ne "$expected" ]; then
  echo "FAIL: some theorem depends on an axiom:"
  printf '%s\n' "$out" | grep -v 'Closed under the global context' \
                       | grep -v '^Fetching opaque proofs' | sed '/^$/d'
  fail=1
else
  echo "ok: all $expected closed under the global context"
fi

exit $fail
