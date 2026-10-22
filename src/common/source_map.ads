--  소스 파일과 위치 관리
--
--  소스 인코딩은 UTF-8이고, 줄 끝은 LF 또는 CR LF다 (§3.1, 구현 정의).
package Source_Map is

   type Source_Id is new Natural;
   No_Source : constant Source_Id := 0;

   --  Offset은 소스 텍스트의 바이트 인덱스(1부터). 텍스트 끝 바로
   --  다음(Length + 1)도 위치로 쓸 수 있다.
   type Source_Pos is record
      Source : Source_Id := No_Source;
      Offset : Natural   := 0;
   end record;
   No_Pos : constant Source_Pos := (No_Source, 0);

   type Text_Access is access constant String;

   --  읽을 수 없으면 No_Source
   function Load (Path : String) return Source_Id;

   function Path (Id : Source_Id) return String;
   function Text (Id : Source_Id) return Text_Access;

   --  열은 문자 단위(UTF-8 선행 바이트 수)
   procedure Line_Col (Pos : Source_Pos; Line, Col : out Positive);

end Source_Map;
