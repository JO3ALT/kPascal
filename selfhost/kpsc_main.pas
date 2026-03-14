program kpsc_main;
(* $I selfhost/types_streaming.inc *)
(* $I selfhost/mini_string.inc *)
(* $I selfhost/source_runtime.inc *)
(* $I selfhost/lexer.inc *)
(* $I selfhost/parser.inc *)
begin
  ReadSourceFromStdin();
  ParseProgram()
end.
