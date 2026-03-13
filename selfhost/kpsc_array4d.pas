program kpsc_array4d;
(* $I selfhost/types.inc *)
(* $I string_utils.pas *)
(* $I selfhost/source.inc *)
(* $I selfhost/lexer.inc *)
(* $I selfhost/parser.inc *)
begin
  LoadArray4dSource();
  ParseProgram()
end.
