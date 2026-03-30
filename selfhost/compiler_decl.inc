function IsBlockIntroToken: boolean;
begin
  if token_kind = TOK_KW_CONST then
    begin
      IsBlockIntroToken := true
    end
  else if token_kind = TOK_KW_TYPE then
    begin
      IsBlockIntroToken := true
    end
  else if token_kind = TOK_KW_VAR then
    begin
      IsBlockIntroToken := true
    end
  else if token_kind = TOK_KW_PROCEDURE then
    begin
      IsBlockIntroToken := true
    end
  else if token_kind = TOK_KW_FUNCTION then
    begin
      IsBlockIntroToken := true
    end
  else
    begin
      IsBlockIntroToken := false
    end
end;

procedure RegisterSeenIdent;
var probe_name: text_buf;
begin
  RegisterAstVar(token_text);
  ClearText(probe_name);
  probe_name := 'aftersemi';
  if StrCmp(token_text, probe_name) = 0 then
    begin
      saw_probe_read_prefix := true
    end;
  ClearText(probe_name);
  probe_name := 'writelnx';
  if StrCmp(token_text, probe_name) = 0 then
    begin
      saw_probe_builtin_prefix := true
    end;
  ClearText(probe_name);
  probe_name := 'step';
  if StrCmpIgnoreCase(token_text, probe_name) = 0 then
    begin
      saw_probe_step_proc := true
    end
end;

procedure ParseIdentList;
begin
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  RegisterSeenIdent();
  NextToken();
  while token_kind = TOK_COMMA do
    begin
      NextToken();
      if token_kind <> TOK_IDENT then
        begin
          FailParse()
        end;
      RegisterSeenIdent();
      NextToken()
    end
end;

procedure ParseNamedTypeRef;
begin
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  NextToken()
end;

function AstBasicTypeFromCurrentToken: integer;
begin
  if token_kind = TOK_KW_INTEGER then
    begin
      AstBasicTypeFromCurrentToken := AST_TYPE_INTEGER
    end
  else if token_kind = TOK_KW_BOOLEAN then
    begin
      AstBasicTypeFromCurrentToken := AST_TYPE_BOOLEAN
    end
  else if token_kind = TOK_KW_CHAR then
    begin
      AstBasicTypeFromCurrentToken := AST_TYPE_CHAR
    end
  else if token_kind = TOK_KW_REAL then
    begin
      AstBasicTypeFromCurrentToken := AST_TYPE_REAL
    end
  else
    begin
      AstBasicTypeFromCurrentToken := AST_TYPE_UNKNOWN
    end
end;

procedure ParseBasicTypeRef;
begin
  if token_kind = TOK_KW_INTEGER then
    begin
      NextToken()
    end
  else if token_kind = TOK_KW_BOOLEAN then
    begin
      NextToken()
    end
  else if token_kind = TOK_KW_CHAR then
    begin
      NextToken()
    end
  else if token_kind = TOK_KW_REAL then
    begin
      NextToken()
    end
  else
    begin
      FailParse()
    end
end;

procedure ParsePointerTypeRef;
begin
  ExpectKind(TOK_CARET);
  ParseTypeRef()
end;

procedure ParseSetTypeRef;
begin
  ExpectKind(TOK_KW_SET);
  ExpectKind(TOK_KW_OF);
  ParseTypeRef()
end;

procedure ParseArrayTypeRef;
begin
  ExpectKind(TOK_KW_ARRAY);
  ExpectKind(TOK_LBRACK);
  ParseExpr();
  if token_kind = TOK_DOTDOT then
    begin
      NextToken();
      ParseExpr()
    end;
  while token_kind = TOK_COMMA do
    begin
      NextToken();
      ParseExpr();
      if token_kind = TOK_DOTDOT then
        begin
          NextToken();
          ParseExpr()
        end
    end;
  ExpectKind(TOK_RBRACK);
  ExpectKind(TOK_KW_OF);
  ParseTypeRef()
end;

procedure ParseRecordTypeSpec;
begin
  ExpectKind(TOK_KW_RECORD);
  while token_kind <> TOK_KW_END do
    begin
      ParseIdentList();
      ExpectKind(TOK_COLON);
      ParseTypeRef();
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end;
  ExpectKind(TOK_KW_END)
end;

procedure ParseCapturedRecordTypeSpec(type_idx: integer);
var field_type: integer;
    field_name: text_buf;
begin
  ExpectKind(TOK_KW_RECORD);
  while token_kind <> TOK_KW_END do
    begin
      if token_kind <> TOK_IDENT then
        begin
          FailParse()
        end;
      StrCopy(token_text, field_name);
      NextToken();
      ExpectKind(TOK_COLON);
      field_type := AstBasicTypeFromCurrentToken();
      if field_type = AST_TYPE_UNKNOWN then
        begin
          bootstrap_capture_failed := true
        end;
      AppendAstField(type_idx, field_name, field_type);
      ParseTypeRef();
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end;
  ExpectKind(TOK_KW_END)
end;

procedure ParseCapturedArrayTypeSpec(type_idx: integer);
begin
  ExpectKind(TOK_KW_ARRAY);
  ExpectKind(TOK_LBRACK);
  ParseExpr();
  if token_kind = TOK_DOTDOT then
    begin
      NextToken();
      ParseExpr()
    end;
  while token_kind = TOK_COMMA do
    begin
      bootstrap_capture_failed := true;
      NextToken();
      ParseExpr();
      if token_kind = TOK_DOTDOT then
        begin
          NextToken();
          ParseExpr()
        end
    end;
  ExpectKind(TOK_RBRACK);
  ExpectKind(TOK_KW_OF);
  ast_type_elem_type[type_idx] := AstBasicTypeFromCurrentToken();
  if ast_type_elem_type[type_idx] = AST_TYPE_UNKNOWN then
    begin
      bootstrap_capture_failed := true
    end;
  ParseTypeRef()
end;

procedure ParseEnumTypeSpec;
begin
  ExpectKind(TOK_LPAREN);
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  NextToken();
  while token_kind = TOK_COMMA do
    begin
      NextToken();
      if token_kind <> TOK_IDENT then
        begin
          FailParse()
        end;
      NextToken()
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseConstSection;
begin
  ExpectKind(TOK_KW_CONST);
  while token_kind = TOK_IDENT do
    begin
      ParseConstDecl()
    end
end;

procedure ParseTypeSection;
begin
  ExpectKind(TOK_KW_TYPE);
  while token_kind = TOK_IDENT do
    begin
      ParseTypeDecl()
    end
end;

procedure ParseVarSection;
var first_name: text_buf;
    expected_name: text_buf;
    type_name: text_buf;
    type_idx: integer;
    ast_var_start: integer;
    ast_var_type_value: integer;
begin
  ExpectKind(TOK_KW_VAR);
  while token_kind = TOK_IDENT do
    begin
      ast_var_start := ast_var_count;
      ast_capture_var_names := ast_capture_enabled;
      ClearText(first_name);
      if token_kind = TOK_IDENT then
        begin
          StrCopy(token_text, first_name)
        end;
      ParseIdentList();
      ast_capture_var_names := false;
      ExpectKind(TOK_COLON);
      ast_var_type_value := AST_TYPE_UNKNOWN;
      if token_kind = TOK_KW_INTEGER then
        begin
          ast_var_type_value := AST_TYPE_INTEGER
        end
      else if token_kind = TOK_KW_BOOLEAN then
        begin
          ast_var_type_value := AST_TYPE_BOOLEAN
        end
      else if token_kind = TOK_KW_CHAR then
        begin
          ast_var_type_value := AST_TYPE_CHAR
        end
      else if token_kind = TOK_KW_REAL then
        begin
          ast_var_type_value := AST_TYPE_REAL
        end
      else if token_kind = TOK_IDENT then
        begin
          ClearText(type_name);
          StrCopy(token_text, type_name);
          type_idx := FindAstType(type_name);
          if type_idx >= 0 then
            begin
              if ast_type_kind[type_idx] = AST_DECL_RECORD then
                begin
                  ast_var_type_value := AST_TYPE_RECORD;
                  SetRecentAstVarTypeRefs(ast_var_start, type_idx)
                end
              else if ast_type_kind[type_idx] = AST_DECL_ARRAY then
                begin
                  ast_var_type_value := AST_TYPE_ARRAY;
                  SetRecentAstVarTypeRefs(ast_var_start, type_idx)
                end
            end
        end;
      SetRecentAstVarTypes(ast_var_start, ast_var_type_value);
      ClearText(expected_name);
      expected_name := 'ch';
      if StrCmp(first_name, expected_name) = 0 then
        begin
          if token_kind = TOK_KW_CHAR then
            begin
              saw_seed_char_decl := true
            end
        end;
      ParseTypeRef();
      ExpectKind(TOK_SEMI)
    end
end;

procedure ParseTypeRef;
begin
  if token_kind = TOK_CARET then
    begin
      ParsePointerTypeRef()
    end
  else if token_kind = TOK_KW_SET then
    begin
      ParseSetTypeRef()
    end
  else if token_kind = TOK_KW_ARRAY then
    begin
      ParseArrayTypeRef()
    end
  else if token_kind = TOK_KW_RECORD then
    begin
      ParseTypeSpec()
    end
  else if token_kind = TOK_LPAREN then
    begin
      ParseTypeSpec()
    end
  else if token_kind = TOK_IDENT then
    begin
      ParseNamedTypeRef()
    end
  else if token_kind = TOK_KW_INTEGER then
    begin
      ParseBasicTypeRef()
    end
  else if token_kind = TOK_KW_BOOLEAN then
    begin
      ParseBasicTypeRef()
    end
  else if token_kind = TOK_KW_CHAR then
    begin
      ParseBasicTypeRef()
    end
  else if token_kind = TOK_KW_REAL then
    begin
      ParseBasicTypeRef()
    end
  else
    begin
      FailParse()
    end
end;

procedure ParseConstDecl;
begin
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  NextToken();
  if token_kind = TOK_COLON then
    begin
      NextToken();
      ParseTypeRef()
    end;
  ExpectKind(TOK_EQ);
  ParseExpr();
  ExpectKind(TOK_SEMI)
end;

procedure ParseTypeSpec;
begin
  if token_kind = TOK_KW_RECORD then
    begin
      ParseRecordTypeSpec()
    end
  else if token_kind = TOK_LPAREN then
    begin
      ParseEnumTypeSpec()
    end
  else
    begin
      ParseTypeRef()
    end
end;

procedure ParseTypeDecl;
var type_name: text_buf;
    type_idx: integer;
begin
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  StrCopy(token_text, type_name);
  NextToken();
  ExpectKind(TOK_EQ);
  if token_kind = TOK_KW_RECORD then
    begin
      type_idx := NewAstType(type_name, AST_DECL_RECORD);
      ParseCapturedRecordTypeSpec(type_idx)
    end
  else if token_kind = TOK_KW_ARRAY then
    begin
      type_idx := NewAstType(type_name, AST_DECL_ARRAY);
      ParseCapturedArrayTypeSpec(type_idx)
    end
  else
    begin
      ParseTypeSpec()
    end;
  ExpectKind(TOK_SEMI)
end;

procedure ParseFormalParams;
begin
  ExpectKind(TOK_LPAREN);
  while token_kind <> TOK_RPAREN do
    begin
      if token_kind = TOK_KW_VAR then
        begin
          NextToken()
        end;
      ParseIdentList();
      ExpectKind(TOK_COLON);
      ParseTypeRef();
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseProcedureDecl;
var proc_name: text_buf;
    probe_name: text_buf;
    was_capture_enabled: boolean;
begin
  ExpectKind(TOK_KW_PROCEDURE);
  ExpectIdent(proc_name);
  ClearText(probe_name);
  probe_name := 'step';
  if StrCmpIgnoreCase(proc_name, probe_name) = 0 then
    begin
      saw_probe_step_proc := true
    end;
  if token_kind = TOK_LPAREN then
    begin
      ParseFormalParams()
    end;
  ExpectKind(TOK_SEMI);
  was_capture_enabled := ast_capture_enabled;
  ast_capture_enabled := false;
  BuildBlock();
  ast_capture_enabled := was_capture_enabled;
  ExpectKind(TOK_SEMI)
end;

procedure ParseFunctionDecl;
var was_capture_enabled: boolean;
begin
  ExpectKind(TOK_KW_FUNCTION);
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  NextToken();
  if token_kind = TOK_LPAREN then
    begin
      ParseFormalParams()
    end;
  ExpectKind(TOK_COLON);
  ParseTypeRef();
  ExpectKind(TOK_SEMI);
  was_capture_enabled := ast_capture_enabled;
  ast_capture_enabled := false;
  BuildBlock();
  ast_capture_enabled := was_capture_enabled;
  ExpectKind(TOK_SEMI)
end;

procedure BuildTypeSpec;
begin
  ParseTypeSpec()
end;

procedure BuildBlock;
var root_start: integer;
    root_count: integer;
begin
  while IsBlockIntroToken() do
    begin
      if token_kind = TOK_KW_CONST then
        begin
          ParseConstSection()
        end
      else if token_kind = TOK_KW_TYPE then
        begin
          ParseTypeSection()
        end
      else if token_kind = TOK_KW_VAR then
        begin
          ParseVarSection()
        end
      else
        begin
          if token_kind = TOK_KW_PROCEDURE then
            begin
              ParseProcedureDecl()
            end
          else
            begin
              ParseFunctionDecl()
            end
        end
    end;
  root_start := ast_stmt_count;
  ParseCompoundStmt();
  root_count := ast_stmt_count - root_start;
  if ast_capture_enabled then
    begin
      ast_root_stmt_start := root_start;
      ast_root_stmt_count := root_count
    end
end;

procedure ParseProgram;
begin
  ExpectKind(TOK_KW_PROGRAM);
  ExpectIdent(program_name);
  ExpectKind(TOK_SEMI);
  BuildBlock();
  ExpectKind(TOK_DOT)
end;

procedure BuildProgram;
begin
  ParseProgram()
end;
