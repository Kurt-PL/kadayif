# Kadayif 구현 정의 문서

KPLSS 0.1이 구현 정의(implementation defined)로 남겨 문서화를 요구하는 선택과, KCSS가 구현에 맡긴 선택을 적습니다. 구현이 늘면 함께 늘어납니다.

## 환경

| 항목 | 선택 |
| --- | --- |
| 프로그램 기계 환경 (`-T`) | `aarch64-apple`: AArch64, Apple arm64 호출 규약, Mach-O |
| 셀 폭 | 8비트 |
| 주소 폭, 참조 폭 | 64비트 |
| 소스 인코딩 (§3.1) | UTF-8. 줄 끝은 LF 또는 CR LF. 글자(letter)와 숫자(digit)는 기본 소스 문자 집합의 것만 |
| 리터럴 인코딩 (§3.1) | UTF-8, 문자 값 8비트. `\xH`는 16진 두 자리 |

## 번역

| 항목 | 선택 |
| --- | --- |
| 외부 이름이 없는 정의의 이름 (§4.2.2) | `kf_` + 식별자. Mach-O에서는 앞에 `_`가 붙는다 |
| 외부 이름의 표현 (§4.2.2) | Mach-O 관례대로 `_` + 이름 |
| 호출 인터페이스 (§10.10.1) | `native` 하나. Apple arm64 호출 규약을 뜻한다 |
| 번역 한계 (§2.8.1) | 식 하나가 동시에 쓰는 임시 레지스터 7개 |
| 자동 객체 배치 (§2.2.7) | 매개변수, 그다음 `let`과 집합체 임시값을 나온 순서대로 쌓는다. 영역을 재사용하지 않는다. 집합체 자리는 8바이트 단위로 잡는다 |
| wild construction의 값 (§6.2.4) | 어느 변형도 갖지 않은 가장 작은 비음수 판별자 값 |
| `repr(native)` (§5.11) | Kurt standard alignment와 같은 배치. 다른 `repr` 식별자는 없다 |
| 집합체의 호출 규약 (§10.10.1) | `native`는 AAPCS64(Apple)의 복합 타입 규칙을 따른다: 16바이트 이하는 범용 레지스터 1–2개, 모자라면 전부 스택. 넘으면 호출자가 만든 복사본의 주소. 반환은 x0/x1, 16바이트를 넘으면 x8이 가리키는 곳 |

## 진단 (KCSS §10)

형식은 `severity - message at path on line:col`입니다. KPLSS의 advisory diagnostic은 `warning`으로 냅니다. 아직 구현하지 않은 요소는 `error - unimplemented: …`로 해당 KPLSS 절을 밝힙니다.

## 환경 변수 (KCSS §8)

| 변수 | 뜻 |
| --- | --- |
| `KURT_KEEP_OBJECT` | 디버깅용. 경로를 주면 링크 전 오브젝트를 Mach-O `.o`로 그 경로에 쓴다 |

## 링크 (KPLSS §10.5, §10.10, KCSS §4.9)

| 항목 | 선택 |
| --- | --- |
| 링크 방식 기본값 (`-B`) | `dynamic` |
| 시스템 기본 라이브러리 위치 | `SDKROOT`가 있으면 `$SDKROOT/usr/lib`, 없으면 Command Line Tools 또는 Xcode SDK의 `usr/lib`. 그다음 `/usr/local/lib` |
| KCSS §4.9의 "libname.so" | macOS 관례대로 `libname.dylib`(Mach-O), 그다음 `libname.tbd`(텍스트 스텁)로 읽는다 |
| 링크할 수 있는 라이브러리 | 동적 라이브러리만. `name.dl`, `name.sl`, `libname.a`를 먼저 찾으면 미구현 오류로 멈춘다 |
| libSystem | 다른 라이브러리와 같다. `-l System`으로 요청해야 싣는다. 아무 라이브러리도 싣지 않은 실행 파일도 dyld가 실행하고 종료한다 |
| 외부 심볼 해석 | `#dyn` 서브루틴은 실을 라이브러리를 순서대로 보아 처음 내보내는 것에 바인딩한다(2단계 네임스페이스, chained fixups). 어디에도 없으면 링크가 실패한다. 다른 라이브러리를 다시 내보내는 dylib처럼 내보내기를 다 알 수 없는 라이브러리는 다른 데서 찾지 못한 심볼의 마지막 후보가 된다 |
| opaque code의 배치 | arm64 Mach-O `MH_EXECUTE`, PIE. 세그먼트는 `__PAGEZERO`, `__TEXT`(`__text`, `__stubs`, `__const`), `__DATA_CONST`(`__got`), `__LINKEDIT` |
| 진입점 | `extern fn main`(`LC_MAIN`) |
| 코드 서명 | ad-hoc, linker-signed, SHA-256, 4KiB 페이지 |

## 임시 사항

- 어셈블러와 링커 모두 kadayif가 직접 합니다. 시스템 도구는 시험 스크립트(`test/asmcheck.sh`)의 대조용으로만 씁니다.
- `-T`는 `aarch64-apple`만 받습니다. AMD64와 ELF는 모듈 자리만 있습니다.
