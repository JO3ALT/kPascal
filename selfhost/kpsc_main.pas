program kpsc_main;
(* $I string_utils.pas *)
(* $I types.inc *)
(* $I compiler_lexer.inc *)
(* $I compiler_expr.inc *)
(* $I compiler_stmt.inc *)
(* $I compiler_decl.inc *)
(* $I compiler_codegen.inc *)
(* $I source_runtime.inc *)
begin
  ReadSourceFromStdin();
  ParseProgram();
  EmitHeader();
  EmitIntLine(0);
  EmitFooter();
end.
