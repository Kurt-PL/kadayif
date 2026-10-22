--  번역 다섯 단계 구동 (§10.2): 소스 처리 → #add 수집 → 선언 수집 →
--  의미 분석·번역 시점 평가 → opaque code 방출
package Pipeline is

   type Stop_After is
     (Analysis,     --  -y: 4단계까지
      Instructions, --  -S: 어셈블리 텍스트
      Artefact);    --  실행 파일

   --  성공하면 True. 실패하면 출력을 남기지 않는다 (§2.8.1).
   function Translate
     (Input : String; Output : String; Stop : Stop_After) return Boolean;

end Pipeline;
