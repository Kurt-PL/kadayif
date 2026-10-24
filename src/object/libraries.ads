--  링크할 라이브러리 찾기와 읽기 (KCSS §4.9)
--
--  디렉터리마다 name.dl, name.sl, 시스템 동적 라이브러리, libname.a
--  순서로 찾는다. macOS의 시스템 동적 라이브러리는 libname.dylib(실제
--  Mach-O), 그다음 libname.tbd(SDK의 텍스트 스텁)다. 동적 라이브러리만
--  링크할 수 있고, 나머지는 찾으면 미구현으로 거절한다.
with Ada.Containers.Indefinite_Hashed_Sets;
with Ada.Containers.Indefinite_Vectors;
with Ada.Containers.Vectors;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded;
with Interfaces;

package Libraries is

   package Name_Sets is new Ada.Containers.Indefinite_Hashed_Sets
     (String, Ada.Strings.Hash, "=");
   package String_Vectors is new Ada.Containers.Indefinite_Vectors
     (Positive, String);

   type Library is record
      Path         : Ada.Strings.Unbounded.Unbounded_String;
      Install_Name : Ada.Strings.Unbounded.Unbounded_String;
      Current      : Interfaces.Unsigned_32 := 16#0001_0000#;
      Compat       : Interfaces.Unsigned_32 := 16#0001_0000#;
      Exports      : Name_Sets.Set;
      --  내보내는 심볼을 다 알지 못한다(다른 라이브러리를 다시
      --  내보내거나, 스텁을 찾지 못한 경우)
      Partial      : Boolean := False;
   end record;

   package Library_Vectors is new Ada.Containers.Vectors (Positive, Library);

   type Linkage is (Dynamic, Static);

   --  시스템 기본 위치: SDK의 usr/lib, 그다음 /usr/local/lib
   function Default_Dirs return String_Vectors.Vector;

   --  -l Name. Dirs를 순서대로 본 뒤 기본 위치를 본다. 찾지 못하거나
   --  읽을 수 없으면 진단을 내고 False.
   function Find
     (Name : String;
      Dirs : String_Vectors.Vector;
      Mode : Linkage;
      Lib  : out Library) return Boolean;

end Libraries;
