program kpsc_string_edit;
(* $I selfhost/types.inc *)
(* $I string_utils.pas *)
(* $I selfhost/source.inc *)
(* $I selfhost/lexer.inc *)
(* $I selfhost/parser.inc *)
begin
  LoadStringEditSource();
  ParseProgram()
end.
