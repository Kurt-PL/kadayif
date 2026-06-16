#!/bin/zsh
# Build every *.kr in this directory with kadayif's own driver (which now
# assembles and links via as/ld through system(3)), run the result, and
# print exit code + stdout (semicolon-joined) per test.

set -u
HERE=${0:A:h}
KADAYIF=$HERE/../bin/main
TMP=$(mktemp -d)
trap "rm -rf $TMP" EXIT

pass=0; fail=0
for f in $HERE/*.kr; do
  name=${f:t:r}
  if $KADAYIF "$f" -o "$TMP/$name" >/dev/null 2>&1; then
    out=$("$TMP/$name" 2>&1); code=$?
    printf "%-24s exit=%s | %s\n" "$name" "$code" "${out//$'\n'/;}"
    pass=$((pass+1))
  else
    printf "%-24s FAILED\n" "$name"
    fail=$((fail+1))
  fi
done
echo "=== pass=$pass fail=$fail ==="
[ $fail -eq 0 ]
