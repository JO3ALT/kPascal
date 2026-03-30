program kpsc_main;
(* $I selfhost/string_utils.pas *)
(* $I selfhost/types.inc *)
(* $I selfhost/source_runtime.inc *)
(* $I selfhost/compiler_lexer.inc *)
(* $I selfhost/compiler_expr.inc *)
(* $I selfhost/compiler_stmt.inc *)
(* $I selfhost/compiler_decl.inc *)
(* $I selfhost/compiler_codegen.inc *)
begin
  InitStringUtils();
  InitCompilerState();
  ReadSourceFromStdin();
  ReadToken();
  ParseProgram();
  EmitProgram();
end.
