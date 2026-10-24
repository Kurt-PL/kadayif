--  흐름 분석: 옮김(transfer)과 무효화 추적 (§8.7)
--
--  복사할 수 없는 값을 적재하면 그 값을 옮기고 원천의 바깥 객체를
--  무효로 만든다. 무효가 된 객체는 바인딩에 직접 다시 저장하기
--  전까지 적재할 수도, 구성 객체에 저장할 수도 없다. 어떤 trace에서든
--  그런 접근이 일어나면 진단한다.
with AST;

package Flow is

   --  의미 분석을 마친 서브루틴 정의 하나를 검사한다
   procedure Check_Transfers (Fn : AST.Node_Id);

end Flow;
