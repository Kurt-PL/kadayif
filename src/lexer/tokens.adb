with Ada.Characters.Handling;

package body Tokens is

   function Lower_Name (K : Token_Kind) return String is
      Img : constant String := Ada.Characters.Handling.To_Lower (K'Image);
   begin
      return Img (Img'First + 2 .. Img'Last);
   end Lower_Name;

   function Keyword (S : String) return Token_Kind is
   begin
      for K in Keyword_Kind loop
         if Lower_Name (K) = S then
            return K;
         end if;
      end loop;
      return T_Ident;
   end Keyword;

   function Directive (S : String) return Token_Kind is
   begin
      for K in Directive_Kind loop
         if Lower_Name (K) = S then
            return K;
         end if;
      end loop;
      return T_EOF;
   end Directive;

   function Spelling (K : Token_Kind) return String is
   begin
      case K is
         when T_EOF        => return "end of source unit";
         when T_Ident      => return "identifier";
         when T_Int        => return "integer literal";
         when T_Float      => return "floating radix point number literal";
         when T_Char       => return "character literal";
         when T_String     => return "string literal";
         when T_Raw_String => return "raw string literal";
         when T_Annotation => return "annotation";
         when Keyword_Kind => return Lower_Name (K);
         when Directive_Kind => return "#" & Lower_Name (K);
         when P_Bang       => return "!";
         when P_Dollar     => return "$";
         when P_Percent    => return "%";
         when P_Amp        => return "&";
         when P_Apos       => return "'";
         when P_LParen     => return "(";
         when P_RParen     => return ")";
         when P_Star       => return "*";
         when P_Plus       => return "+";
         when P_Comma      => return ",";
         when P_Minus      => return "-";
         when P_Dot        => return ".";
         when P_Slash      => return "/";
         when P_Colon      => return ":";
         when P_Semi       => return ";";
         when P_Lt         => return "<";
         when P_Eq         => return "=";
         when P_Gt         => return ">";
         when P_Question   => return "?";
         when P_At         => return "@";
         when P_LBracket   => return "[";
         when P_RBracket   => return "]";
         when P_Caret      => return "^";
         when P_LBrace     => return "{";
         when P_Pipe       => return "|";
         when P_RBrace     => return "}";
         when P_Tilde      => return "~";
         when P_Ne         => return "!=";
         when P_Percent_Eq => return "%=";
         when P_Amp_Eq     => return "&=";
         when P_Star_Eq    => return "*=";
         when P_Star_At    => return "*@";
         when P_Star_Pipe  => return "*|";
         when P_Plus_Eq    => return "+=";
         when P_Plus_At    => return "+@";
         when P_Plus_Pipe  => return "+|";
         when P_Minus_Eq   => return "-=";
         when P_Arrow      => return "->";
         when P_Minus_Pipe => return "-|";
         when P_Dot_Dot    => return "..";
         when P_Slash_Eq   => return "/=";
         when P_Slash_Pipe => return "/|";
         when P_Colon_Colon => return "::";
         when P_Shl        => return "<<";
         when P_Le         => return "<=";
         when P_Eq_Eq      => return "==";
         when P_Ge         => return ">=";
         when P_Shr        => return ">>";
         when P_Caret_Eq   => return "^=";
         when P_Pipe_Eq    => return "|=";
         when P_Star_Pipe_Eq  => return "*|=";
         when P_Plus_Pipe_Eq  => return "+|=";
         when P_Minus_Pipe_Eq => return "-|=";
         when P_Ellipsis   => return "...";
         when P_Dot_Dot_Eq => return "..=";
         when P_Slash_Pipe_Eq => return "/|=";
         when P_Shl_Eq     => return "<<=";
         when P_Shr_Eq     => return ">>=";
         when P_Cas        => return ">.<";
      end case;
   end Spelling;

end Tokens;
