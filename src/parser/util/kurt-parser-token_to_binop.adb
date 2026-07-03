separate (Kurt.Parser)
   function Token_To_Binop (K : Token_Kind; Op : out Binary_Op) return Boolean is
   begin
      case K is
         when Op_Plus     => Op := B_Add;
         when Op_Minus    => Op := B_Sub;
         when Op_Star     => Op := B_Mul;
         when Op_Slash    => Op := B_Div;
         when Op_Percent  => Op := B_Mod;
         when Op_PlusBar  => Op := B_Sat_Add;
         when Op_MinusBar => Op := B_Sat_Sub;
         when Op_StarBar  => Op := B_Sat_Mul;
         when Op_SlashBar => Op := B_Sat_Div;
         when Op_Amp      => Op := B_And;
         when Op_Bar      => Op := B_Or;
         when Op_Caret    => Op := B_Xor;
         when Op_Shl      => Op := B_Shl;
         when Op_Shr      => Op := B_Shr;
         when Op_PlusAt   => Op := B_Wide_Add;
         when Op_StarAt   => Op := B_Wide_Mul;
         when Op_EqEq    => Op := B_Eq;
         when Op_BangEq  => Op := B_Ne;
         when Op_Lt      => Op := B_Lt;
         when Op_Gt      => Op := B_Gt;
         when Op_Le      => Op := B_Le;
         when Op_Ge      => Op := B_Ge;
         when Op_AmpAmp  => Op := B_LAnd;
         when Op_BarBar  => Op := B_LOr;
         when Op_CaretCaret => Op := B_LXor;
         when others     => return False;
      end case;
      return True;
   end Token_To_Binop;
