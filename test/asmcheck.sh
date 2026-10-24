#!/bin/sh
# 인코더 검증: 실행 시험(NAME.expected가 있는 것)마다 kadayif가 직접 만든
# 오브젝트와, 같은 프로그램의 -S 출력을 시스템 어셈블러로 만든 오브젝트를
# 디스어셈블해 명령을 비교한다. 심볼 이름 차이는 무시한다.
# macOS의 cc와 objdump가 필요하다. 저장소 최상위에서 실행한다.
cd "$(dirname "$0")/.." || exit 1
K=./bin/kadayif
T=$(mktemp -d "${TMPDIR:-/tmp}/kadayif-asm.XXXXXX")
trap 'rm -rf "$T"' EXIT
pass=0 fail=0
dis() {
    objdump -d --no-leading-addr "$1" | sed -n '/<.*>:/,$p' \
        | grep -v '>:$' | awk '{$1=""; print}' | sed 's/<[^>]*>//'
}
for src in test/cases/*.kr; do
    [ -f "${src%.kr}.expected" ] || continue
    flags=$(cat "${src%.kr}.flags" 2>/dev/null)
    $K -S "$src" -o "$T/t.s" 2>/dev/null \
        && cc -arch arm64 -c "$T/t.s" -o "$T/ref.o" \
        && KURT_KEEP_OBJECT="$T/own.o" $K "$src" -o "$T/a.out" $flags 2>/dev/null \
        || { echo "FAIL $src: build"; fail=$((fail + 1)); continue; }
    dis "$T/ref.o" > "$T/ref.dis"; dis "$T/own.o" > "$T/own.dis"
    if cmp -s "$T/ref.dis" "$T/own.dis"; then pass=$((pass + 1))
    else echo "FAIL $src"; diff "$T/ref.dis" "$T/own.dis" | head -20; fail=$((fail + 1)); fi
done
echo "$pass identical, $fail differ"
[ "$fail" -eq 0 ]
