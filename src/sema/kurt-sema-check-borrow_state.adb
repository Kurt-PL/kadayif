separate (Kurt.Sema.Check)
   procedure Borrow_State
     (Sigil   : Ref_Sigil;
      Store   : Ref_Store;
      State   : out Kurt.Borrow.Perm_State;
      Tracked : out Boolean)
   is
   begin
      Tracked := True;
      case Sigil is
         when R_Raw =>
            Tracked := False;
            State   := Kurt.Borrow.Shared_RO;
         when R_Excl =>
            State := Kurt.Borrow.Idle;            --  $T
         when R_Shared =>
            case Store is
               when RS_None => State := Kurt.Borrow.Shared_RO;
               when RS_Mut  => State := Kurt.Borrow.Shared_RW;
               when RS_Atomic | RS_Guard =>
                  State := Kurt.Borrow.Atomic_Ref;
            end case;
      end case;
   end Borrow_State;
