--  Kurt.Borrow body — see the spec for the model (§8.2, §8.3).

package body Kurt.Borrow is

   --  Node_Id is the 1-based vector index (0 = No_Node).
   function Get (T : Tree; N : Node_Id) return Node_Rec is
     (T.Nodes.Element (Positive (N)));

   procedure Clear (T : in out Tree) is
   begin
      T.Nodes.Clear;
   end Clear;

   function Create
     (T         : in out Tree;
      Referent  : String;
      Bound_To  : String;
      State     : Perm_State;
      Parent    : Node_Id := No_Node;
      Scope_Len : Natural := 0) return Node_Id
   is
   begin
      T.Nodes.Append
        ((Referent  => SU.To_Unbounded_String (Referent),
          Bound_To  => SU.To_Unbounded_String (Bound_To),
          State     => State,
          Parent    => Parent,
          Live      => True,
          Scope_Len => Scope_Len));
      return Node_Id (T.Nodes.Last_Index);
   end Create;

   function Of_Binding (T : Tree; Name : String) return Node_Id is
   begin
      --  Most recent live binding of this name wins (shadowing).
      for I in reverse T.Nodes.First_Index .. T.Nodes.Last_Index loop
         if T.Nodes.Element (I).Live
           and then SU.To_String (T.Nodes.Element (I).Bound_To) = Name
         then
            return Node_Id (I);
         end if;
      end loop;
      return No_Node;
   end Of_Binding;

   procedure Record_Store (T : in out Tree; N : Node_Id) is
   begin
      if N = No_Node then
         return;
      end if;
      declare
         R : Node_Rec := Get (T, N);
      begin
         --  §8.3: Idle + local store -> AssertExcl.
         if R.State = Idle then
            R.State := Assert_Excl;
            T.Nodes.Replace_Element (Positive (N), R);
         end if;
      end;
   end Record_Store;

   --  Whether A is N or a descendant of N (within the derivation subtree).
   function In_Subtree (T : Tree; N, A : Node_Id) return Boolean;

   procedure Apply_Foreign_Store
     (T : in out Tree; By : Node_Id; Atomic : Boolean)
   is
      --  §8.3: an Atomic_Ref keeps its state under both a foreign atomic and
      --  a foreign non-atomic store (only the lapse flag, which the bootstrap
      --  does not act on, differs), so Atomic does not affect the transition.
      pragma Unreferenced (Atomic);
   begin
      if By = No_Node then
         return;
      end if;
      declare
         Ref : constant String := SU.To_String (Get (T, By).Referent);
      begin
         for I in T.Nodes.First_Index .. T.Nodes.Last_Index loop
            declare
               M : constant Node_Id  := Node_Id (I);
               R : Node_Rec          := T.Nodes.Element (I);
            begin
               --  Foreign := live, distinct referent-overlapping node that is
               --  neither an ancestor nor a descendant of By.
               if R.Live and then M /= By
                 and then SU.To_String (R.Referent) = Ref
                 and then not In_Subtree (T, By, M)
                 and then not In_Subtree (T, M, By)
               then
                  case R.State is
                     when Idle | Assert_Excl =>
                        R.State := Shared_RW;        --  lapse
                        T.Nodes.Replace_Element (I, R);
                     when Atomic_Ref =>
                        null;  --  lapse only; state unchanged (and none at
                               --  all for a foreign atomic store)
                     when Shared_RO | Shared_RW | Proven_Excl =>
                        null;  --  lapse in place; no state change
                  end case;
               end if;
            end;
         end loop;
      end;
   end Apply_Foreign_Store;

   procedure Kill_Above (T : in out Tree; Keep_Len : Natural) is
   begin
      for I in T.Nodes.First_Index .. T.Nodes.Last_Index loop
         declare
            R : Node_Rec := T.Nodes.Element (I);
         begin
            if R.Live and then R.Scope_Len > Keep_Len then
               R.Live := False;
               T.Nodes.Replace_Element (I, R);
            end if;
         end;
      end loop;
   end Kill_Above;

   --  Whether A is N or a descendant of N (within the derivation subtree).
   function In_Subtree (T : Tree; N, A : Node_Id) return Boolean is
      Cur : Node_Id := A;
   begin
      while Cur /= No_Node loop
         if Cur = N then
            return True;
         end if;
         Cur := Get (T, Cur).Parent;
      end loop;
      return False;
   end In_Subtree;

   function Has_Live_Alias (T : Tree; N : Node_Id) return Boolean is
   begin
      if N = No_Node then
         return False;
      end if;
      declare
         Ref : constant String := SU.To_String (Get (T, N).Referent);
      begin
         for I in T.Nodes.First_Index .. T.Nodes.Last_Index loop
            declare
               M : constant Node_Id := Node_Id (I);
               R : constant Node_Rec := T.Nodes.Element (I);
            begin
               if R.Live
                 and then M /= N
                 and then SU.To_String (R.Referent) = Ref
                 and then not In_Subtree (T, N, M)
                 and then not In_Subtree (T, M, N)
               then
                  return True;
               end if;
            end;
         end loop;
      end;
      return False;
   end Has_Live_Alias;

   function Has_Asserted_Excl (T : Tree; Referent : String) return Boolean is
   begin
      for I in T.Nodes.First_Index .. T.Nodes.Last_Index loop
         declare
            R : constant Node_Rec := T.Nodes.Element (I);
         begin
            if R.Live and then R.State = Assert_Excl
              and then SU.To_String (R.Referent) = Referent
            then
               return True;
            end if;
         end;
      end loop;
      return False;
   end Has_Asserted_Excl;

   function State_Of (T : Tree; N : Node_Id) return Perm_State is
     (Get (T, N).State);

   function Referent_Of (T : Tree; N : Node_Id) return String is
     (SU.To_String (Get (T, N).Referent));

end Kurt.Borrow;
