program kpsc_array2d;
(* $I selfhost/types.inc *)
(* $I string_utils.pas *)
(* $I selfhost/source.inc *)
(* $I selfhost/lexer.inc *)
(* $I selfhost/parser.inc *)
begin
  LoadArray2dSource();
  ParseProgram()
end.
