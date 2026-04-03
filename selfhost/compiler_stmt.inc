function IsStatementStart: boolean;
begin
  if token_kind = TOK_KW_BEGIN then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_IDENT then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_READ then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_READLN then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_FOR then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_WRITE then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_WRITELN then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_CASE then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_IF then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_WITH then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_WHILE then
    begin
      IsStatementStart := true
    end
  else if token_kind = TOK_KW_REPEAT then
    begin
      IsStatementStart := true
    end
  else
    begin
      IsStatementStart := false
    end
end;

procedure NoteNonWriteLnStatement;
begin
  bootstrap_has_non_writeln_stmt := true
end;

procedure CaptureWriteLnInt(value: integer);
begin
  if captured_writeln_count < MAX_CAPTURED_WRITELNS then
    begin
      captured_writeln_kind[captured_writeln_count] := CAPTURE_KIND_INT;
      captured_writeln_int[captured_writeln_count] := value;
      captured_writeln_count := captured_writeln_count + 1
    end
  else
    begin
    end
end;

procedure CaptureWriteLnText(var text: text_buf);
begin
  if captured_writeln_count < MAX_CAPTURED_WRITELNS then
    begin
      captured_writeln_kind[captured_writeln_count] := CAPTURE_KIND_TEXT;
      StrCopy(text, captured_writeln_text[captured_writeln_count]);
      captured_writeln_count := captured_writeln_count + 1
    end
  else
    begin
    end
end;

procedure CaptureWriteLnChar(ch: char);
begin
  if captured_writeln_count < MAX_CAPTURED_WRITELNS then
    begin
      captured_writeln_kind[captured_writeln_count] := CAPTURE_KIND_CHAR;
      captured_writeln_int[captured_writeln_count] := Ord(ch);
      captured_writeln_count := captured_writeln_count + 1
    end
  else
    begin
    end
end;


function BuildAstTargetExprFromFirstName(var first_name: text_buf): integer;
var expr_idx: integer;
    next_idx: integer;
    temp_text: text_buf;
begin
  expr_idx := NewAstExpr(AST_EXPR_IDENT);
  ClearText(temp_text);
  StrCopy(first_name, temp_text);
  ast_expr_int[expr_idx] := FindScopedAstVar(temp_text);
  ast_expr_text_ref[expr_idx] := NewAstIdent(temp_text);
  while IsSelectorToken() do
    begin
      if token_kind = TOK_DOT then
        begin
          NextToken();
          if token_kind <> TOK_IDENT then
            begin
              FailParse()
            end;
          next_idx := NewAstExpr(AST_EXPR_FIELD);
          ast_expr_left[next_idx] := expr_idx;
          ast_expr_text_ref[next_idx] := NewAstIdent(token_text);
          expr_idx := next_idx;
          NextToken()
        end
      else if token_kind = TOK_LBRACK then
        begin
          NextToken();
          next_idx := NewAstExpr(AST_EXPR_INDEX);
          ast_expr_left[next_idx] := expr_idx;
          ast_expr_right[next_idx] := BuildAstExpr();
          expr_idx := next_idx;
          ExpectKind(TOK_RBRACK)
        end
      else
        begin
          ParseDerefSelector();
          next_idx := NewAstExpr(AST_EXPR_DEREF);
          ast_expr_left[next_idx] := expr_idx;
          expr_idx := next_idx
        end
    end;
  BuildAstTargetExprFromFirstName := expr_idx
end;

procedure ParseCapturedWriteLnArg(stmt_idx: integer);
var expected_name: text_buf;
    expr_idx: integer;
    temp_text: text_buf;
begin
  if token_kind = TOK_STR then
    begin
      if token_text[1] = #0 then
        begin
          CaptureWriteLnChar(token_text[0]);
          if stmt_idx >= 0 then
            begin
              expr_idx := BuildAstExpr();
              AppendAstExprArg(stmt_idx, expr_idx)
            end
          else
            begin
              NextToken()
            end
        end
      else
        begin
          CaptureWriteLnText(token_text);
          if stmt_idx >= 0 then
            begin
              AppendAstArg(stmt_idx, AST_ARG_TEXT, 0, token_text)
            end;
          NextToken()
        end
    end
  else
    begin
      if token_kind = TOK_IDENT then
        begin
          ClearText(expected_name);
          expected_name := 'ch';
          if StrCmp(token_text, expected_name) = 0 then
            begin
              saw_seed_char_writeln := true
            end
        end;
      if token_kind = TOK_INT then
        begin
          CaptureWriteLnInt(token_value)
        end
      else if token_kind = TOK_KW_TRUE then
        begin
          ClearText(temp_text);
          temp_text := 'TRUE';
          CaptureWriteLnText(temp_text)
        end
      else if token_kind = TOK_KW_FALSE then
        begin
          ClearText(temp_text);
          temp_text := 'FALSE';
          CaptureWriteLnText(temp_text)
        end;
      if stmt_idx >= 0 then
        begin
          expr_idx := BuildAstExpr();
          AppendAstExprArg(stmt_idx, expr_idx)
        end
      else
        begin
          if ast_capture_enabled then
            begin
              bootstrap_capture_failed := true;
              if parse_error_reason = 0 then
                begin
                  parse_error_reason := 325
                end
            end;
          ParseExpr()
        end
    end
end;

function IsStatementFollowerToken: boolean;
begin
  if token_kind = TOK_SEMI then
    begin
      IsStatementFollowerToken := true
    end
  else if token_kind = TOK_KW_END then
    begin
      IsStatementFollowerToken := true
    end
  else if token_kind = TOK_KW_ELSE then
    begin
      IsStatementFollowerToken := true
    end
  else if token_kind = TOK_KW_UNTIL then
    begin
      IsStatementFollowerToken := true
    end
  else if token_kind = TOK_DOT then
    begin
      IsStatementFollowerToken := true
    end
  else if token_kind = TOK_EOF then
    begin
      IsStatementFollowerToken := true
    end
  else
    begin
      IsStatementFollowerToken := false
    end
end;

function IsForDirectionToken: boolean;
begin
  if token_kind = TOK_KW_TO then
    begin
      IsForDirectionToken := true
    end
  else if token_kind = TOK_KW_DOWNTO then
    begin
      IsForDirectionToken := true
    end
  else
    begin
      IsForDirectionToken := false
    end
end;

procedure ParseRequiredCompoundStmt;
begin
  ParseCompoundStmt()
end;

procedure ParseCaseLabelList;
begin
  ParseExpr();
  while token_kind = TOK_COMMA do
    begin
      ReadToken();
      ParseExpr()
    end
end;

procedure ResetAstStmtSlot(stmt_idx: integer);
begin
  ast_stmt_kind[stmt_idx] := AST_STMT_NONE;
  ClearIdent(ast_stmt_name[stmt_idx]);
  ast_stmt_value_kind[stmt_idx] := AST_ARG_NONE;
  ast_stmt_value_int[stmt_idx] := 0;
  ast_stmt_value_text_ref[stmt_idx] := -1;
  ast_stmt_expr[stmt_idx] := -1;
  ast_stmt_aux_expr[stmt_idx] := -1;
  ast_stmt_arg_start[stmt_idx] := 0;
  ast_stmt_arg_count[stmt_idx] := 0;
  ast_stmt_child_start[stmt_idx] := 0;
  ast_stmt_child_count[stmt_idx] := 0;
  ast_stmt_else_start[stmt_idx] := 0;
  ast_stmt_else_count[stmt_idx] := 0
end;

procedure ParseCapturedStmtList(var start_idx: integer; var count: integer);
begin
  start_idx := ast_stmt_count;
  if IsStatementStart() then
    begin
      ParseStatement();
      while token_kind = TOK_SEMI do
        begin
          NextToken();
          if IsStatementStart() then
            begin
              ParseStatement()
            end
        end
    end;
  count := ast_stmt_count - start_idx
end;

procedure ParseStmtList;
var start_idx: integer;
    count: integer;
begin
  ParseCapturedStmtList(start_idx, count)
end;

procedure ParseCompoundStmt;
var stmt_idx: integer;
    child_start: integer;
    child_count: integer;
begin
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_COMPOUND)
    end;
  ExpectKind(TOK_KW_BEGIN);
  ParseCapturedStmtList(child_start, child_count);
  if stmt_idx >= 0 then
    begin
      ast_stmt_child_start[stmt_idx] := child_start;
      ast_stmt_child_count[stmt_idx] := child_count
    end;
  ExpectKind(TOK_KW_END)
end;

procedure ParseAssignStmt;
begin
  NoteNonWriteLnStatement();
  BuildLValue();
  ExpectAssignSymbol();
  ParseExpr()
end;

procedure CaptureAstProcCall(stmt_idx: integer);
begin
  ExpectKind(TOK_LPAREN);
  if token_kind <> TOK_RPAREN then
    begin
      AppendAstExprArg(stmt_idx, BuildAstExpr());
      while token_kind = TOK_COMMA do
        begin
          NextToken();
          AppendAstExprArg(stmt_idx, BuildAstExpr())
        end
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseProcCallStmt;
begin
  NoteNonWriteLnStatement();
  if ast_capture_enabled then
    begin
      bootstrap_capture_failed := true;
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 326
        end
    end;
  if token_kind = TOK_LPAREN then
    begin
      ParseCallSuffix()
    end
end;

procedure ParseAssignOrCall;
var saw_selector: boolean;
    first_name: text_buf;
    expected_name: text_buf;
    stmt_idx: integer;
    expr_idx: integer;
    call_routine_idx: integer;
    captured_simple_assign: boolean;
begin
  if token_kind <> TOK_IDENT then
    begin
      parse_error_reason := 301;
      FailParse()
    end;
  ClearText(first_name);
  StrCopy(token_text, first_name);
  call_routine_idx := FindAstRoutineByName(token_text);
  ClearText(expected_name);
  expected_name := 'step';
  if StrCmpIgnoreCase(first_name, expected_name) = 0 then
    begin
      saw_probe_step_proc := true
    end;
  NextToken();
  saw_selector := false;
  while IsSelectorToken() do
    begin
      saw_selector := true;
      ParseSelectorSuffixes()
    end;
  if token_kind = TOK_ASSIGN then
    begin
      NoteNonWriteLnStatement();
      NextToken();
      captured_simple_assign := false;
      ClearText(expected_name);
      expected_name := 'ch';
      if StrCmp(first_name, expected_name) = 0 then
        begin
          if token_kind = TOK_STR then
            begin
              if token_text[0] = 'H' then
                begin
                  if token_text[1] = #0 then
                    begin
                      saw_seed_char_assign := true
                    end
                end
            end
        end;
      if ast_capture_enabled then
        begin
          stmt_idx := NewAstStmt(AST_STMT_ASSIGN);
          if saw_selector then
            begin
              ast_stmt_expr[stmt_idx] := BuildAstTargetExprFromFirstName(first_name)
            end
          else
            begin
              expr_idx := NewAstExpr(AST_EXPR_IDENT);
              ast_expr_int[expr_idx] := FindScopedAstVar(first_name);
              ast_expr_text_ref[expr_idx] := NewAstIdent(first_name);
              ast_stmt_expr[stmt_idx] := expr_idx
            end;
          CopyTextToIdent(first_name, ast_stmt_name[stmt_idx]);
          if token_kind = TOK_STR then
            begin
                  if token_text[1] <> #0 then
                    begin
                      ast_stmt_value_kind[stmt_idx] := AST_ARG_TEXT;
                      ast_stmt_value_text_ref[stmt_idx] := NewAstTextLit(token_text);
                      NextToken();
                      expr_idx := -1
                    end
              else
                begin
                  expr_idx := BuildAstExpr();
                  ast_stmt_value_int[stmt_idx] := expr_idx
                end
            end
          else
            begin
              expr_idx := BuildAstExpr();
              ast_stmt_value_int[stmt_idx] := expr_idx
            end;
          if not bootstrap_capture_failed then
            begin
              if ast_stmt_expr[stmt_idx] >= 0 then
                begin
                  if ast_stmt_value_kind[stmt_idx] = AST_ARG_TEXT then
                    begin
                      captured_simple_assign := true
                    end
                  else if expr_idx >= 0 then
                    begin
                      captured_simple_assign := true
                    end
                end
            end;
          if not captured_simple_assign then
            begin
              ast_stmt_count := ast_stmt_count - 1;
              ResetAstStmtSlot(ast_stmt_count)
            end
        end;
      if not ast_capture_enabled then
        begin
          ParseExpr()
        end;
      if ast_capture_enabled then
        begin
          if not captured_simple_assign then
            begin
              bootstrap_capture_failed := true;
              if parse_error_reason = 0 then
                begin
                  parse_error_reason := 327
                end
            end
        end
    end
  else if token_kind = TOK_LPAREN then
    begin
      NoteNonWriteLnStatement();
      stmt_idx := -1;
      if ast_capture_enabled then
        begin
          stmt_idx := NewAstStmt(AST_STMT_CALL);
          ast_stmt_value_int[stmt_idx] := call_routine_idx;
          CopyTextToIdent(first_name, ast_stmt_name[stmt_idx])
        end;
      if stmt_idx >= 0 then
        begin
          CaptureAstProcCall(stmt_idx)
        end
      else
        begin
          ParseProcCallStmt()
        end
    end
  else if saw_selector then
    begin
      if ast_capture_enabled then
        begin
          bootstrap_capture_failed := true;
          if parse_error_reason = 0 then
            begin
              parse_error_reason := 328
            end
        end;
      FailParse()
    end
end;

procedure ParseReadStmt;
var stmt_idx: integer;
begin
  NoteNonWriteLnStatement();
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_READ)
    end;
  ExpectKind(TOK_KW_READ);
  ExpectKind(TOK_LPAREN);
  if token_kind <> TOK_RPAREN then
    begin
      if stmt_idx >= 0 then
        begin
          AppendAstExprArg(stmt_idx, BuildAstExpr());
          while token_kind = TOK_COMMA do
            begin
              NextToken();
              AppendAstExprArg(stmt_idx, BuildAstExpr())
            end
        end
      else
        begin
          ParseExprList()
        end
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseReadLnStmt;
begin
  NoteNonWriteLnStatement();
  if ast_capture_enabled then
    begin
      bootstrap_capture_failed := true;
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 329
        end
    end;
  ExpectKind(TOK_KW_READLN);
  if token_kind = TOK_LPAREN then
    begin
      NextToken();
      if token_kind <> TOK_RPAREN then
        begin
          ParseExprList()
        end;
      ExpectKind(TOK_RPAREN)
    end
end;

procedure ParseForStmt;
var stmt_idx: integer;
    child_start: integer;
    child_count: integer;
begin
  NoteNonWriteLnStatement();
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_FOR)
    end;
  ExpectKind(TOK_KW_FOR);
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  if stmt_idx >= 0 then
    begin
      CopyTextToIdent(token_text, ast_stmt_name[stmt_idx])
    end;
  NextToken();
  ExpectAssignSymbol();
  if stmt_idx >= 0 then
    begin
      ast_stmt_expr[stmt_idx] := BuildAstExpr()
    end
  else
    begin
      ParseExpr()
    end;
  if IsForDirectionToken() then
    begin
      if stmt_idx >= 0 then
        begin
          ast_stmt_value_kind[stmt_idx] := token_kind
        end;
      NextToken()
    end
  else
    begin
      FailParse()
    end;
  if stmt_idx >= 0 then
    begin
      ast_stmt_aux_expr[stmt_idx] := BuildAstExpr()
    end
  else
    begin
      ParseExpr()
    end;
  ExpectKind(TOK_KW_DO);
  child_start := ast_stmt_count;
  ParseRequiredCompoundStmt();
  child_count := ast_stmt_count - child_start;
  if stmt_idx >= 0 then
    begin
      ast_stmt_child_start[stmt_idx] := child_start;
      ast_stmt_child_count[stmt_idx] := child_count
    end
end;

procedure ParseWriteStmt;
var stmt_idx: integer;
begin
  NoteNonWriteLnStatement();
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_WRITE)
    end;
  ExpectKind(TOK_KW_WRITE);
  ExpectKind(TOK_LPAREN);
  if token_kind <> TOK_RPAREN then
    begin
      ParseCapturedWriteLnArg(stmt_idx);
      while token_kind = TOK_COMMA do
        begin
          NextToken();
          ParseCapturedWriteLnArg(stmt_idx)
        end
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseWriteLnStmt;
var stmt_idx: integer;
begin
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_WRITELN)
    end;
  ExpectKind(TOK_KW_WRITELN);
  if token_kind = TOK_LPAREN then
    begin
      NextToken();
      if token_kind <> TOK_RPAREN then
        begin
          ParseCapturedWriteLnArg(stmt_idx);
          while token_kind = TOK_COMMA do
            begin
              NextToken();
              ParseCapturedWriteLnArg(stmt_idx)
            end
        end;
      ExpectKind(TOK_RPAREN)
    end
end;

procedure ParseCaseStmt;
begin
  NoteNonWriteLnStatement();
  if ast_capture_enabled then
    begin
      bootstrap_capture_failed := true;
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 330
        end
    end;
  ExpectKind(TOK_KW_CASE);
  ParseExpr();
  ExpectKind(TOK_KW_OF);
  while token_kind <> TOK_KW_END do
    begin
      if token_kind = TOK_KW_ELSE then
        begin
          NextToken();
          ParseStatement()
        end
      else
        begin
          ParseCaseLabelList();
          ExpectKind(TOK_COLON);
          ParseStatement()
        end;
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end;
  ExpectKind(TOK_KW_END)
end;

procedure ParseIfStmt;
var stmt_idx: integer;
    then_start: integer;
    then_count: integer;
    else_start: integer;
    else_count: integer;
begin
  NoteNonWriteLnStatement();
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_IF)
    end;
  ExpectKind(TOK_KW_IF);
  if stmt_idx >= 0 then
    begin
      ast_stmt_expr[stmt_idx] := BuildAstExpr()
    end
  else
    begin
      ParseExpr()
    end;
  ExpectKind(TOK_KW_THEN);
  then_start := ast_stmt_count;
  ParseStatement();
  then_count := ast_stmt_count - then_start;
  if stmt_idx >= 0 then
    begin
      ast_stmt_child_start[stmt_idx] := then_start;
      ast_stmt_child_count[stmt_idx] := then_count
    end;
  if token_kind = TOK_KW_ELSE then
    begin
      NextToken();
      else_start := ast_stmt_count;
      ParseStatement();
      else_count := ast_stmt_count - else_start;
      if stmt_idx >= 0 then
        begin
          ast_stmt_else_start[stmt_idx] := else_start;
          ast_stmt_else_count[stmt_idx] := else_count
        end
    end
end;

procedure ParseWithStmt;
begin
  NoteNonWriteLnStatement();
  if ast_capture_enabled then
    begin
      bootstrap_capture_failed := true
    end;
  ExpectKind(TOK_KW_WITH);
  BuildLValue();
  while token_kind = TOK_COMMA do
    begin
      NextToken();
      BuildLValue()
    end;
  ExpectKind(TOK_KW_DO);
  ParseRequiredCompoundStmt()
end;

procedure ParseWhileStmt;
var stmt_idx: integer;
    child_start: integer;
    child_count: integer;
begin
  NoteNonWriteLnStatement();
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_WHILE)
    end;
  ExpectKind(TOK_KW_WHILE);
  if stmt_idx >= 0 then
    begin
      ast_stmt_expr[stmt_idx] := BuildAstExpr()
    end
  else
    begin
      ParseExpr()
    end;
  ExpectKind(TOK_KW_DO);
  child_start := ast_stmt_count;
  ParseRequiredCompoundStmt();
  child_count := ast_stmt_count - child_start;
  if stmt_idx >= 0 then
    begin
      ast_stmt_child_start[stmt_idx] := child_start;
      ast_stmt_child_count[stmt_idx] := child_count
    end
end;

procedure ParseRepeatStmt;
var stmt_idx: integer;
    child_start: integer;
    child_count: integer;
begin
  NoteNonWriteLnStatement();
  stmt_idx := -1;
  if ast_capture_enabled then
    begin
      stmt_idx := NewAstStmt(AST_STMT_REPEAT)
    end;
  ExpectKind(TOK_KW_REPEAT);
  ParseCapturedStmtList(child_start, child_count);
  if stmt_idx >= 0 then
    begin
      ast_stmt_child_start[stmt_idx] := child_start;
      ast_stmt_child_count[stmt_idx] := child_count
    end;
  ExpectKind(TOK_KW_UNTIL);
  if stmt_idx >= 0 then
    begin
      ast_stmt_expr[stmt_idx] := BuildAstExpr()
    end
  else
    begin
      ParseExpr()
    end
end;

procedure ParseCharArrayLiteralAssignment;
begin
end;

procedure ParseEmptyStmt;
begin
end;

procedure ParseStatement;
begin
  if token_kind = TOK_KW_BEGIN then
    begin
      ParseCompoundStmt()
    end
  else if token_kind = TOK_IDENT then
    begin
      ParseAssignOrCall()
    end
  else if token_kind = TOK_KW_READ then
    begin
      ParseReadStmt()
    end
  else if token_kind = TOK_KW_READLN then
    begin
      ParseReadLnStmt()
    end
  else if token_kind = TOK_KW_FOR then
    begin
      ParseForStmt()
    end
  else if token_kind = TOK_KW_WRITE then
    begin
      ParseWriteStmt()
    end
  else if token_kind = TOK_KW_WRITELN then
    begin
      ParseWriteLnStmt()
    end
  else if token_kind = TOK_KW_CASE then
    begin
      ParseCaseStmt()
    end
  else if token_kind = TOK_KW_IF then
    begin
      ParseIfStmt()
    end
  else if token_kind = TOK_KW_WITH then
    begin
      ParseWithStmt()
    end
  else if token_kind = TOK_KW_WHILE then
    begin
      ParseWhileStmt()
    end
  else if token_kind = TOK_KW_REPEAT then
    begin
      ParseRepeatStmt()
    end
  else if IsStatementFollowerToken() then
    begin
      ParseEmptyStmt()
    end
end;

procedure BuildStmt;
begin
  ParseStatement()
end;
