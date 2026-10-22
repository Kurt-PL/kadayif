# Kadayif

뇌 스로틀링하면서 만드는 쿠어트 프로그래밍 언어의 레퍼런스 컴파일러

`.kr` 소스 파일을 읽어들이고 `aarch64+Apple` 타깃으로 바이너리를 뱉습니다. 나중에 다른 타깃이나 라이브러리로 확장해야 해요

> **DISCLOSURE**: Kadayif는 컴파일러 이론이고 SSA고 뭐고 아무것도 모르는 놈이 Claude Code로 바이브코딩하는 겁니다. 기여하고 싶다고요? 좋습니다. 컴파일러 이론 교재 추천하겠다고요? 너무 좋습니다. 직접 가르쳐드린다고요? 사랑합니다.

IR이나 IL도 없고 최적화도 거의 안 하는 순진한 구현입니다. 쿠어트에는 일관성 규칙이라는 게 있는데, 그냥 1:1로 구현하면 자명하게 만족하거든요. 반은 제가 멍청한 거고 반은 의도된 거에요.

## 이건 뭔가요

[쿠어트 프로그래밍 언어 표준 규격서](https://github.com/Kurt-PL/std-spec) 0.1을 따릅니다. 취미...라기엔 엄청 큰 스케일의 언어입니다.

<!-- 제발 스펙 변경할 일 더 없었으면 좋겠어요 이상한 게 너무 많이 발견돼 -->

## 사용하는 방법

일단 [여기](https://alire.ada.dev/)에서 `Alire`라는 걸 받아야 합니다. 그 다음 `git`이 있으면:

```sh
git clone https://github.com/Kurt-PL/kadayif.git
cd kadayif
alr build # 이러면 `./bin/kadayif` 실행 파일이 생성돼요
```

그 다음 쿠어트 코드를 대충

```kurt
// 이건 #include <stdio.h> 내지는 int printf(const char*, ...);
#dyn io {
    variadic fn printf(%ui1) -> si4;
}

// 이건 int main(int argc, char *argv[]) {}
extern fn main(argc: uaddr, argv: %%ui1) -> ui1 {
    airside {
        io::printf("Hello, world!\n\0".ptr);
    } // 이건 printf("Hello, world!\n");

    return 0;
}
```

이딴 식으로 만든 뒤

```sh
./bin/kadayif -S file.kr
clang -arch arm64 file.s -o a.out
./a.out # Hello, world!
```

이러면 됩니다.

왜 Ada냐고요? 묻지 마세요. 궁금하다고요? 아니요, 궁금하지 않을 거에요.

## 기여하기

코드는 기여 안 해주셔도 돼요 아니 해 주시면 감사하겠지만 그거보다도 컴파일러 이론 책이나 참고할 만한 컴파일러들 이슈 열어서 알려주세요,, 저도 다른 거@물들 처럼 컴파일러 손으로 만들어보고 싶어요

규칙 딱 둘: LLVM + RIIR은 안 됩니다, LLVM은 C의 의미론 위에 지어졌고 Kurt는 그걸 ***실로 개좆같다***고 평가하거든요 모든 언어가 결국 LLVM의 위성 언어가 되는 게 진짜 너무 싫어서 언어를 만든 거니까요

## 라이선스

[ISC](LICENCE)
