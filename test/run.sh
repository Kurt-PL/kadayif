#!/bin/sh
# 회귀 시험: test/cases/NAME.kr 마다
#   NAME.expected 가 있으면 번역·실행해 표준 출력을 비교하고,
#   NAME.fail 이 있으면 번역이 실패하며 진단이 같은지 비교한다.
# 저장소 최상위에서 실행한다. --update 를 주면 기대값을 다시 쓴다.
cd "$(dirname "$0")/.." || exit 1
K=./bin/kadayif
T=$(mktemp -d "${TMPDIR:-/tmp}/kadayif-test.XXXXXX")
trap 'rm -rf "$T"' EXIT
pass=0 fail=0
for src in test/cases/*.kr; do
    name=${src%.kr}
    if [ -f "$name.fail" ] || [ "${src#*_err}" != "$src" ]; then
        if $K -y "$src" 2> "$T/out"; then
            echo "FAIL $src: translation succeeded"; fail=$((fail + 1)); continue
        fi
        [ "$1" = --update ] && cp "$T/out" "$name.fail"
        if cmp -s "$T/out" "$name.fail"; then pass=$((pass + 1))
        else echo "FAIL $src: diagnostics differ"; diff "$name.fail" "$T/out"; fail=$((fail + 1)); fi
    else
        if ! $K "$src" -o "$T/a.out" 2> "$T/err"; then
            echo "FAIL $src: translation failed"; cat "$T/err"; fail=$((fail + 1)); continue
        fi
        "$T/a.out" > "$T/out"
        [ "$1" = --update ] && cp "$T/out" "$name.expected"
        if cmp -s "$T/out" "$name.expected"; then pass=$((pass + 1))
        else echo "FAIL $src: output differs"; diff "$name.expected" "$T/out"; fail=$((fail + 1)); fi
    fi
done
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
