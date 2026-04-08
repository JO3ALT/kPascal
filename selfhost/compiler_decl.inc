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

procedure ParseVariantRecordTypeSpec;
begin
  ExpectKind(TOK_KW_CASE);
  if token_kind = TOK_IDENT then
    begin
      NextToken();
      ExpectKind(TOK_COLON);
      ParseTypeRef()
    end;
  ExpectKind(TOK_KW_OF);
  while token_kind <> TOK_KW_END do
    begin
      ParseExpr();
      while token_kind = TOK_COMMA do
        begin
          NextToken();
          ParseExpr()
        end;
      ExpectKind(TOK_COLON);
      ExpectKind(TOK_LPAREN);
      while token_kind <> TOK_RPAREN do
        begin
          ParseIdentList();
          ExpectKind(TOK_COLON);
          ParseTypeRef();
          if token_kind = TOK_SEMI then
            begin
              NextToken()
            end
        end;
      ExpectKind(TOK_RPAREN);
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end
end;

procedure ParseRecordTypeSpec;
begin
  ExpectKind(TOK_KW_RECORD);
  while token_kind <> TOK_KW_END do
    begin
      if token_kind = TOK_KW_CASE then
        begin
          ParseVariantRecordTypeSpec()
        end
      else
        begin
          ParseIdentList();
          ExpectKind(TOK_COLON);
          ParseTypeRef();
          if token_kind = TOK_SEMI then
            begin
              NextToken()
            end
        end
    end;
  ExpectKind(TOK_KW_END)
end;

procedure AppendAstFieldOnce(type_idx: integer; var name: text_buf; field_type: integer);
begin
  if FindAstField(type_idx, name) < 0 then
    begin
      AppendAstField(type_idx, name, field_type)
    end
end;

procedure ParseCapturedVariantRecordTypeSpec(type_idx: integer);
var field_type: integer;
    field_name: text_buf;
begin
  ExpectKind(TOK_KW_CASE);
  if token_kind = TOK_IDENT then
    begin
      StrCopy(token_text, field_name);
      NextToken();
      ExpectKind(TOK_COLON);
      field_type := AstBasicTypeFromCurrentToken();
      if field_type = AST_TYPE_UNKNOWN then
        begin
          bootstrap_capture_failed := true
        end;
      AppendAstFieldOnce(type_idx, field_name, field_type);
      ParseTypeRef()
    end;
  ExpectKind(TOK_KW_OF);
  while token_kind <> TOK_KW_END do
    begin
      ParseExpr();
      while token_kind = TOK_COMMA do
        begin
          NextToken();
          ParseExpr()
        end;
      ExpectKind(TOK_COLON);
      ExpectKind(TOK_LPAREN);
      while token_kind <> TOK_RPAREN do
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
          AppendAstFieldOnce(type_idx, field_name, field_type);
          ParseTypeRef();
          if token_kind = TOK_SEMI then
            begin
              NextToken()
            end
        end;
      ExpectKind(TOK_RPAREN);
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end
end;

procedure ParseCapturedRecordTypeSpec(type_idx: integer);
var field_type: integer;
    field_name: text_buf;
begin
  ExpectKind(TOK_KW_RECORD);
  while token_kind <> TOK_KW_END do
    begin
      if token_kind = TOK_KW_CASE then
        begin
          ParseCapturedVariantRecordTypeSpec(type_idx)
        end
      else
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
        end
    end;
  ExpectKind(TOK_KW_END)
end;

procedure ResolveCapturedTypeRef(var type_code: integer; var type_ref: integer);
var type_name: text_buf;
begin
  type_code := AstBasicTypeFromCurrentToken();
  type_ref := -1;
  if type_code = AST_TYPE_UNKNOWN then
    begin
      if token_kind = TOK_IDENT then
        begin
          ClearText(type_name);
          StrCopy(token_text, type_name);
          type_ref := FindAstType(type_name);
          if type_ref >= 0 then
            begin
              if ast_type_kind[type_ref] = AST_DECL_RECORD then
                begin
                  type_code := AST_TYPE_RECORD
                end
              else if ast_type_kind[type_ref] = AST_DECL_ARRAY then
                begin
                  type_code := AST_TYPE_ARRAY
                end
              else if ast_type_kind[type_ref] = AST_DECL_ENUM then
                begin
                  type_code := AST_TYPE_INTEGER
                end
              else if ast_type_kind[type_ref] = AST_DECL_SET then
                begin
                  type_code := AST_TYPE_INTEGER
                end
              else if ast_type_kind[type_ref] = AST_DECL_SUBRANGE then
                begin
                  type_code := AST_TYPE_INTEGER
                end
            end
        end
    end
end;

function AstNamedTypeValueCode(type_idx: integer): integer;
begin
  AstNamedTypeValueCode := AST_TYPE_UNKNOWN;
  if type_idx >= 0 then
    begin
      if ast_type_kind[type_idx] = AST_DECL_RECORD then
        begin
          AstNamedTypeValueCode := AST_TYPE_RECORD
        end
      else if ast_type_kind[type_idx] = AST_DECL_ARRAY then
        begin
          AstNamedTypeValueCode := AST_TYPE_ARRAY
        end
      else if ast_type_kind[type_idx] = AST_DECL_ENUM then
        begin
          AstNamedTypeValueCode := AST_TYPE_INTEGER
        end
      else if ast_type_kind[type_idx] = AST_DECL_SET then
        begin
          AstNamedTypeValueCode := AST_TYPE_INTEGER
        end
      else if ast_type_kind[type_idx] = AST_DECL_SUBRANGE then
        begin
          AstNamedTypeValueCode := AST_TYPE_INTEGER
        end
    end
end;

procedure ParseCapturedArrayTypeSpec(type_idx: integer);
var low_vals: array[0..7] of integer;
    high_vals: array[0..7] of integer;
    dim_count: integer;
    actual_dim_count: integer;
    lo_val: integer;
    hi_val: integer;
    elem_type: integer;
    elem_type_ref: integer;
    dim_idx: integer;
    current_type: integer;
    next_type_ref: integer;
    next_type_code: integer;
    empty_name: text_buf;
begin
  ExpectKind(TOK_KW_ARRAY);
  ExpectKind(TOK_LBRACK);
  dim_count := 0;
  while dim_count < 8 do
    begin
      low_vals[dim_count] := 0;
      high_vals[dim_count] := 0;
      dim_count := dim_count + 1
    end;
  dim_count := 0;
  actual_dim_count := 0;
  while actual_dim_count < 8 do
    begin
      lo_val := 0;
      hi_val := 0;
      if token_kind = TOK_INT then
        begin
          lo_val := token_value
        end;
      ParseExpr();
      if token_kind = TOK_DOTDOT then
        begin
          NextToken();
          if token_kind = TOK_INT then
            begin
              hi_val := token_value
            end;
          ParseExpr()
        end
      else
        begin
          hi_val := lo_val - 1;
          lo_val := 0
        end;
      low_vals[actual_dim_count] := lo_val;
      high_vals[actual_dim_count] := hi_val;
      actual_dim_count := actual_dim_count + 1;
      if token_kind <> TOK_COMMA then
        begin
          actual_dim_count := 8
        end
      else
        begin
          NextToken()
        end
    end;
  dim_count := 1;
  while dim_count < 8 do
    begin
      if low_vals[dim_count] = 0 then
        begin
          if high_vals[dim_count] = 0 then
            begin
              dim_count := 8
            end
          else
            begin
              dim_count := dim_count + 1
            end
        end
      else
        begin
          dim_count := dim_count + 1
        end
    end;
  if dim_count = 8 then
    begin
      dim_count := 1;
      while dim_count < 8 do
        begin
          if low_vals[dim_count] = 0 then
            begin
              if high_vals[dim_count] = 0 then
                begin
                  actual_dim_count := dim_count;
                  dim_count := 8
                end
              else
                begin
                  dim_count := dim_count + 1
                end
            end
          else
            begin
              dim_count := dim_count + 1
            end
        end
    end;
  if actual_dim_count = 8 then
    begin
      actual_dim_count := 1
    end;
  dim_count := actual_dim_count;
  ExpectKind(TOK_RBRACK);
  ExpectKind(TOK_KW_OF);
  ResolveCapturedTypeRef(elem_type, elem_type_ref);
  if elem_type = AST_TYPE_UNKNOWN then
    begin
      bootstrap_capture_failed := true
    end;
  ParseTypeRef();
  next_type_code := elem_type;
  next_type_ref := elem_type_ref;
  dim_idx := dim_count - 1;
  while dim_idx >= 0 do
    begin
      if dim_idx = 0 then
        begin
          current_type := type_idx
        end
      else
        begin
          ClearText(empty_name);
          current_type := NewAstType(empty_name, AST_DECL_ARRAY)
        end;
      ast_type_array_low[current_type] := low_vals[dim_idx];
      ast_type_array_high[current_type] := high_vals[dim_idx];
      ast_type_array_len[current_type] := high_vals[dim_idx] - low_vals[dim_idx] + 1;
      ast_type_elem_type[current_type] := next_type_code;
      ast_type_elem_type_ref[current_type] := next_type_ref;
      ast_type_array_size[current_type] := ast_type_array_len[current_type] * AstTypeCellCount(next_type_code, next_type_ref);
      next_type_code := AST_TYPE_ARRAY;
      next_type_ref := current_type;
      dim_idx := dim_idx - 1
    end
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

procedure ParseCapturedEnumTypeSpec(type_idx: integer);
var value: integer;
    member_name: text_buf;
begin
  value := 0;
  ExpectKind(TOK_LPAREN);
  while token_kind = TOK_IDENT do
    begin
      ClearText(member_name);
      StrCopy(token_text, member_name);
      AppendAstEnumConst(type_idx, member_name, value);
      value := value + 1;
      NextToken();
      if token_kind = TOK_COMMA then
        begin
          NextToken()
        end
    end;
  ast_type_array_low[type_idx] := 0;
  ast_type_array_high[type_idx] := value - 1;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseCapturedSetTypeSpec(type_idx: integer);
var elem_type: integer;
    elem_type_ref: integer;
begin
  ExpectKind(TOK_KW_SET);
  ExpectKind(TOK_KW_OF);
  ResolveCapturedTypeRef(elem_type, elem_type_ref);
  ast_type_elem_type[type_idx] := elem_type;
  ast_type_elem_type_ref[type_idx] := elem_type_ref;
  ParseTypeRef()
end;

procedure ParseCapturedSubrangeTypeSpec(type_idx: integer);
var low_value: integer;
    high_value: integer;
begin
  low_value := 0;
  high_value := 0;
  if token_kind = TOK_INT then
    begin
      low_value := token_value
    end
  else
    begin
      bootstrap_capture_failed := true
    end;
  ParseExpr();
  ExpectKind(TOK_DOTDOT);
  if token_kind = TOK_INT then
    begin
      high_value := token_value
    end
  else
    begin
      bootstrap_capture_failed := true
    end;
  ParseExpr();
  ast_type_array_low[type_idx] := low_value;
  ast_type_array_high[type_idx] := high_value
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
      else if token_kind = TOK_CARET then
        begin
          NextToken();
          if token_kind = TOK_IDENT then
            begin
              ClearText(type_name);
              StrCopy(token_text, type_name);
              type_idx := FindAstType(type_name);
              if type_idx >= 0 then
                begin
                  if ast_type_kind[type_idx] = AST_DECL_RECORD then
                    begin
                      ast_var_type_value := AST_TYPE_POINTER;
                      SetRecentAstVarTypeRefs(ast_var_start, type_idx)
                    end
                end
            end
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
              else if ast_type_kind[type_idx] = AST_DECL_ENUM then
                begin
                  ast_var_type_value := AST_TYPE_INTEGER;
                  SetRecentAstVarTypeRefs(ast_var_start, type_idx)
                end
              else if ast_type_kind[type_idx] = AST_DECL_SET then
                begin
                  ast_var_type_value := AST_TYPE_INTEGER;
                  SetRecentAstVarTypeRefs(ast_var_start, type_idx)
                end
              else if ast_type_kind[type_idx] = AST_DECL_SUBRANGE then
                begin
                  ast_var_type_value := AST_TYPE_INTEGER;
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
  else if token_kind = TOK_LPAREN then
    begin
      type_idx := NewAstType(type_name, AST_DECL_ENUM);
      ParseCapturedEnumTypeSpec(type_idx)
    end
  else if token_kind = TOK_KW_ARRAY then
    begin
      type_idx := NewAstType(type_name, AST_DECL_ARRAY);
      ParseCapturedArrayTypeSpec(type_idx)
    end
  else if token_kind = TOK_KW_SET then
    begin
      type_idx := NewAstType(type_name, AST_DECL_SET);
      ParseCapturedSetTypeSpec(type_idx)
    end
  else if token_kind = TOK_INT then
    begin
      type_idx := NewAstType(type_name, AST_DECL_SUBRANGE);
      ParseCapturedSubrangeTypeSpec(type_idx)
    end
  else
    begin
      ParseTypeSpec()
    end;
  ExpectKind(TOK_SEMI)
end;

procedure ParseFormalParams(routine_idx: integer);
var by_ref: integer;
    type_code: integer;
    type_name: text_buf;
    type_idx: integer;
    param_start: integer;
    visible_param_idx: integer;
    bound_start: integer;
    dim_count: integer;
    low_name: text_buf;
    high_name: text_buf;
    elem_type: integer;
    elem_type_ref: integer;
    dim_idx: integer;
    current_type: integer;
    next_type_ref: integer;
    next_type_code: integer;
    empty_name: text_buf;
    parsed_type_ref: integer;
begin
  ExpectKind(TOK_LPAREN);
  while token_kind <> TOK_RPAREN do
    begin
      by_ref := 0;
      if token_kind = TOK_KW_VAR then
        begin
          by_ref := 1;
          NextToken()
        end;
      param_start := ast_param_count;
      if token_kind <> TOK_IDENT then
        begin
          FailParse()
        end;
      AppendAstParam(routine_idx, token_text, AST_TYPE_UNKNOWN, by_ref <> 0);
      NextToken();
      while token_kind = TOK_COMMA do
        begin
          NextToken();
          if token_kind <> TOK_IDENT then
            begin
              FailParse()
            end;
          AppendAstParam(routine_idx, token_text, AST_TYPE_UNKNOWN, by_ref <> 0);
          NextToken()
        end;
      ExpectKind(TOK_COLON);
      type_code := AST_TYPE_UNKNOWN;
      type_idx := -1;
      parsed_type_ref := 0;
      if token_kind = TOK_KW_ARRAY then
        begin
          if ast_param_count <> param_start + 1 then
            begin
              bootstrap_capture_failed := true
            end;
          visible_param_idx := param_start;
          ast_param_by_ref[visible_param_idx] := 1;
          bound_start := ast_param_count;
          dim_count := 0;
          ExpectKind(TOK_KW_ARRAY);
          ExpectKind(TOK_LBRACK);
          while token_kind <> TOK_RBRACK do
            begin
              if token_kind <> TOK_IDENT then
                begin
                  FailParse()
                end;
              ClearText(low_name);
              StrCopy(token_text, low_name);
              AppendAstParam(routine_idx, low_name, AST_TYPE_INTEGER, false);
              ast_param_hidden[ast_param_count - 1] := 1;
              NextToken();
              ExpectKind(TOK_DOTDOT);
              if token_kind <> TOK_IDENT then
                begin
                  FailParse()
                end;
              ClearText(high_name);
              StrCopy(token_text, high_name);
              AppendAstParam(routine_idx, high_name, AST_TYPE_INTEGER, false);
              ast_param_hidden[ast_param_count - 1] := 1;
              NextToken();
              ExpectKind(TOK_COLON);
              ParseTypeRef();
              dim_count := dim_count + 1;
              if token_kind = TOK_SEMI then
                begin
                  NextToken()
                end
            end;
          ExpectKind(TOK_RBRACK);
          ExpectKind(TOK_KW_OF);
          ResolveCapturedTypeRef(elem_type, elem_type_ref);
          ParseTypeRef();
          ClearText(empty_name);
          type_idx := NewAstType(empty_name, AST_DECL_ARRAY);
          next_type_code := elem_type;
          next_type_ref := elem_type_ref;
          dim_idx := dim_count - 1;
          while dim_idx >= 0 do
            begin
              if dim_idx = 0 then
                begin
                  current_type := type_idx
                end
              else
                begin
                  ClearText(empty_name);
                  current_type := NewAstType(empty_name, AST_DECL_ARRAY)
                end;
              ast_type_array_low[current_type] := 0;
              ast_type_array_high[current_type] := 0;
              ast_type_array_len[current_type] := 0;
              ast_type_elem_type[current_type] := next_type_code;
              ast_type_elem_type_ref[current_type] := next_type_ref;
              ast_type_array_size[current_type] := 0;
              next_type_code := AST_TYPE_ARRAY;
              next_type_ref := current_type;
              dim_idx := dim_idx - 1
            end;
          ast_param_type[visible_param_idx] := AST_TYPE_ARRAY;
          ast_param_type_ref[visible_param_idx] := type_idx;
          ast_param_conformant_bound_start[visible_param_idx] := bound_start;
          ast_param_conformant_dim_count[visible_param_idx] := dim_count;
          type_code := AST_TYPE_ARRAY;
          parsed_type_ref := 1
        end
      else if token_kind = TOK_KW_INTEGER then
        begin
          type_code := AST_TYPE_INTEGER
        end
      else if token_kind = TOK_KW_BOOLEAN then
        begin
          type_code := AST_TYPE_BOOLEAN
        end
      else if token_kind = TOK_KW_CHAR then
        begin
          type_code := AST_TYPE_CHAR
        end
      else if token_kind = TOK_KW_REAL then
        begin
          type_code := AST_TYPE_REAL
        end
      else if token_kind = TOK_IDENT then
        begin
          ClearText(type_name);
          StrCopy(token_text, type_name);
          type_idx := FindAstType(type_name);
          if type_idx >= 0 then
            begin
              type_code := AstNamedTypeValueCode(type_idx)
            end
        end;
      while param_start < ast_param_count do
        begin
          if ast_param_hidden[param_start] = 0 then
            begin
              ast_param_type[param_start] := type_code;
              if type_code = AST_TYPE_RECORD then
                begin
                  ast_param_type_ref[param_start] := type_idx
                end
              else if type_code = AST_TYPE_ARRAY then
                begin
                  if ast_param_type_ref[param_start] < 0 then
                    begin
                      ast_param_type_ref[param_start] := type_idx
                    end
                end
              else if type_idx >= 0 then
                begin
                  ast_param_type_ref[param_start] := type_idx
                end
            end;
          param_start := param_start + 1
        end;
      if parsed_type_ref = 0 then
        begin
          ParseTypeRef()
        end;
      if token_kind = TOK_SEMI then
        begin
          NextToken()
        end
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseProcedureDecl;
var probe_name: text_buf;
    was_capture_enabled: boolean;
    was_capture_routine: integer;
    routine_idx: integer;
begin
  ExpectKind(TOK_KW_PROCEDURE);
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  routine_idx := NewAstRoutine(token_text, AST_ROUTINE_PROCEDURE);
  ClearText(probe_name);
  probe_name := 'step';
  if StrCmpIgnoreCase(token_text, probe_name) = 0 then
    begin
      saw_probe_step_proc := true
    end;
  NextToken();
  if token_kind = TOK_LPAREN then
    begin
      ParseFormalParams(routine_idx)
    end;
  ExpectKind(TOK_SEMI);
  ast_routine_var_start[routine_idx] := ast_var_count;
  was_capture_enabled := ast_capture_enabled;
  was_capture_routine := ast_current_routine;
  ast_current_routine := routine_idx;
  BuildBlock();
  ast_current_routine := was_capture_routine;
  ast_capture_enabled := was_capture_enabled;
  ast_routine_var_count[routine_idx] := ast_var_count - ast_routine_var_start[routine_idx];
  ExpectKind(TOK_SEMI)
end;

procedure ParseFunctionDecl;
var was_capture_enabled: boolean;
    was_capture_routine: integer;
    routine_idx: integer;
    ret_type_code: integer;
begin
  ExpectKind(TOK_KW_FUNCTION);
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  routine_idx := NewAstRoutine(token_text, AST_ROUTINE_FUNCTION);
  NextToken();
  if token_kind = TOK_LPAREN then
    begin
      ParseFormalParams(routine_idx)
    end;
  ExpectKind(TOK_COLON);
  ret_type_code := AST_TYPE_UNKNOWN;
  if token_kind = TOK_KW_INTEGER then
    begin
      ret_type_code := AST_TYPE_INTEGER
    end
  else if token_kind = TOK_KW_BOOLEAN then
    begin
      ret_type_code := AST_TYPE_BOOLEAN
    end
  else if token_kind = TOK_KW_CHAR then
    begin
      ret_type_code := AST_TYPE_CHAR
    end
  else if token_kind = TOK_KW_REAL then
    begin
      ret_type_code := AST_TYPE_REAL
    end;
  ast_routine_ret_type[routine_idx] := ret_type_code;
  ParseTypeRef();
  ExpectKind(TOK_SEMI);
  ast_routine_var_start[routine_idx] := ast_var_count;
  was_capture_enabled := ast_capture_enabled;
  was_capture_routine := ast_current_routine;
  ast_current_routine := routine_idx;
  BuildBlock();
  ast_current_routine := was_capture_routine;
  ast_capture_enabled := was_capture_enabled;
  ast_routine_var_count[routine_idx] := ast_var_count - ast_routine_var_start[routine_idx];
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
      if ast_current_routine >= 0 then
        begin
          ast_routine_stmt_start[ast_current_routine] := root_start;
          ast_routine_stmt_count[ast_current_routine] := root_count
        end
      else
        begin
          ast_root_stmt_start := root_start;
          ast_root_stmt_count := root_count
        end
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
