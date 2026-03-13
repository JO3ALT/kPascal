program kpsc_arith;
(* $I selfhost/types.inc *)
(* $I string_utils.pas *)
(* $I selfhost/source.inc *)
(* $I selfhost/lexer.inc *)
(* $I selfhost/parser.inc *)
begin
  LoadArithmeticSource();
  ParseProgram()
end.
