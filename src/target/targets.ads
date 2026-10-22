--  타깃 = ISA × 호출 규약 × 오브젝트 형식의 조합,
--  그리고 세 Kurt machine의 환경 (§1.2)
package Targets is

   type ISA_Kind is (ISA_AArch64, ISA_AMD64);
   type ABI_Kind is (ABI_Apple_Arm64, ABI_SysV_AMD64);
   type Format_Kind is (Format_MachO, Format_ELF);

   type Target is record
      ISA    : ISA_Kind;
      ABI    : ABI_Kind;
      Format : Format_Kind;
   end record;

   AArch64_Apple : constant Target :=
     (ISA_AArch64, ABI_Apple_Arm64, Format_MachO);
   AMD64_SysV    : constant Target :=
     (ISA_AMD64, ABI_SysV_AMD64, Format_ELF);

   type Machine_Kind is
     (Programme_Machine, Translation_Machine, Arbiter_Machine);

   --  폭은 모두 비트 단위
   type Environment is record
      Platform        : Target;
      Cell_Width      : Positive;
      Address_Width   : Positive;
      Reference_Width : Positive;
   end record;

   --  arbiter machine: 환경은 translation machine이 제공하고,
   --  폭은 두 기계 중 큰 쪽 (§6.11.2)
   function Arbiter_Of
     (Programme, Translation : Environment) return Environment;

end Targets;
