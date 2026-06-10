#!/bin/zsh
# Run every *.kr in this directory through the compiler+assembler+linker
# and print exit code + stdout (semicolon-joined) per test.

set -u
HERE=${0:A:h}
KADAIF=$HERE/../bin/main
SDK=$(xcrun --show-sdk-path)
TMP=$(mktemp -d)
trap "rm -rf $TMP" EXIT

pass=0; fail=0
for f in $HERE/*.kr; do
  name=${f:t:r}
  if $KADAIF "$f" -o "$TMP/$name.s" >/dev/null 2>&1 \
     && as -arch arm64 "$TMP/$name.s" -o "$TMP/$name.o" 2>/dev/null \
     && ld "$TMP/$name.o" -lSystem -syslibroot "$SDK" -e _main -o "$TMP/$name" 2>/dev/null; then
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
