function IsUnaryToken: boolean;
begin
  if token_kind = TOK_MINUS then
    begin
      IsUnaryToken := true
    end
  else if token_kind = TOK_KW_NOT then
    begin
      IsUnaryToken := true
    end
  else
    begin
      IsUnaryToken := false
    end
end;

function IsLiteralKeywordToken: boolean;
begin
  if token_kind = TOK_KW_TRUE then
    begin
      IsLiteralKeywordToken := true
    end
  else if token_kind = TOK_KW_FALSE then
    begin
      IsLiteralKeywordToken := true
    end
  else if token_kind = TOK_KW_NIL then
    begin
      IsLiteralKeywordToken := true
    end
  else
    begin
      IsLiteralKeywordToken := false
    end
end;

function IsSelectorToken: boolean;
begin
  if token_kind = TOK_DOT then
    begin
      IsSelectorToken := true
    end
  else if token_kind = TOK_LBRACK then
    begin
      IsSelectorToken := true
    end
  else if token_kind = TOK_CARET then
    begin
      IsSelectorToken := true
    end
  else
    begin
      IsSelectorToken := false
    end
end;

function IsMulOpToken: boolean;
begin
  if token_kind = TOK_STAR then
    begin
      IsMulOpToken := true
    end
  else if token_kind = TOK_SLASH then
    begin
      IsMulOpToken := true
    end
  else if token_kind = TOK_KW_DIV then
    begin
      IsMulOpToken := true
    end
  else if token_kind = TOK_KW_MOD then
    begin
      IsMulOpToken := true
    end
  else if token_kind = TOK_KW_AND then
    begin
      IsMulOpToken := true
    end
  else
    begin
      IsMulOpToken := false
    end
end;

function IsAddOpToken: boolean;
begin
  if token_kind = TOK_PLUS then
    begin
      IsAddOpToken := true
    end
  else if token_kind = TOK_MINUS then
    begin
      IsAddOpToken := true
    end
  else if token_kind = TOK_KW_OR then
    begin
      IsAddOpToken := true
    end
  else if token_kind = TOK_KW_XOR then
    begin
      IsAddOpToken := true
    end
  else
    begin
      IsAddOpToken := false
    end
end;

function IsRelOpToken: boolean;
begin
  if token_kind = TOK_EQ then
    begin
      IsRelOpToken := true
    end
  else if token_kind = TOK_NE then
    begin
      IsRelOpToken := true
    end
  else if token_kind = TOK_LT then
    begin
      IsRelOpToken := true
    end
  else if token_kind = TOK_LE then
    begin
      IsRelOpToken := true
    end
  else if token_kind = TOK_GT then
    begin
      IsRelOpToken := true
    end
  else if token_kind = TOK_GE then
    begin
      IsRelOpToken := true
    end
  else if token_kind = TOK_KW_IN then
    begin
      IsRelOpToken := true
    end
  else
    begin
      IsRelOpToken := false
    end
end;

procedure ParseCallSuffix;
begin
  ExpectKind(TOK_LPAREN);
  if token_kind <> TOK_RPAREN then
    begin
      ParseExprList()
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure BuildAstCallArgs(call_expr_idx: integer);
begin
  ExpectKind(TOK_LPAREN);
  ast_expr_left[call_expr_idx] := ast_arg_count;
  ast_expr_right[call_expr_idx] := 0;
  if token_kind <> TOK_RPAREN then
    begin
      AppendAstCallExprArg(call_expr_idx, BuildAstExpr());
      while token_kind = TOK_COMMA do
        begin
          NextToken();
          AppendAstCallExprArg(call_expr_idx, BuildAstExpr())
        end
    end;
  ExpectKind(TOK_RPAREN)
end;

procedure ParseFieldSelector;
begin
  ExpectKind(TOK_DOT);
  if token_kind <> TOK_IDENT then
    begin
      FailParse()
    end;
  NextToken()
end;

procedure ParseIndexSelector;
begin
  ExpectKind(TOK_LBRACK);
  ParseExprList();
  ExpectKind(TOK_RBRACK)
end;

procedure ParseDerefSelector;
begin
  ExpectKind(TOK_CARET)
end;

procedure ParseSelectorSuffixes;
begin
  while IsSelectorToken() do
    begin
      if token_kind = TOK_DOT then
        begin
          ParseFieldSelector()
        end
      else if token_kind = TOK_LBRACK then
        begin
          ParseIndexSelector()
        end
      else
        begin
          ParseDerefSelector()
        end
    end
end;

procedure ParseExprList;
begin
  ParseExpr();
  while token_kind = TOK_COMMA do
    begin
      NextToken();
      ParseExpr()
    end
end;

procedure ParsePrimaryExpr;
begin
  if token_kind = TOK_INT then
    begin
      NextToken()
    end
  else if token_kind = TOK_STR then
    begin
      NextToken()
    end
  else if IsLiteralKeywordToken() then
    begin
      NextToken()
    end
  else if token_kind = TOK_LPAREN then
    begin
      NextToken();
      ParseExpr();
      ExpectKind(TOK_RPAREN)
    end
  else if token_kind = TOK_IDENT then
    begin
      NextToken();
      if token_kind = TOK_LPAREN then
        begin
          ParseCallSuffix()
        end
      else
        begin
          ParseSelectorSuffixes()
        end
    end
  else
    begin
      FailParse()
    end
end;

procedure ParseUnaryExpr;
begin
  if IsUnaryToken() then
    begin
      NextToken()
    end;
  ParsePrimaryExpr()
end;

procedure ParseMulExpr;
begin
  ParseUnaryExpr();
  while IsMulOpToken() do
    begin
      NextToken();
      ParseUnaryExpr()
    end
end;

procedure ParseAddExpr;
begin
  ParseMulExpr();
  while IsAddOpToken() do
    begin
      NextToken();
      ParseMulExpr()
    end
end;

procedure ParseRelExpr;
begin
  ParseAddExpr();
  if IsRelOpToken() then
    begin
      NextToken();
      ParseAddExpr()
    end
end;

procedure ParseExpr;
begin
  ParseRelExpr()
end;

function BuiltinExprKindByName(var name: text_buf): integer;
var expected_name: text_buf;
begin
  BuiltinExprKindByName := 0;
  ClearText(expected_name);
  expected_name := 'addr';
  if StrCmpIgnoreCase(name, expected_name) = 0 then
    begin
      BuiltinExprKindByName := 1
    end
  else
    begin
      ClearText(expected_name);
      expected_name := 'ord';
      if StrCmpIgnoreCase(name, expected_name) = 0 then
        begin
          BuiltinExprKindByName := 2
        end
      else
        begin
          ClearText(expected_name);
          expected_name := 'chr';
          if StrCmpIgnoreCase(name, expected_name) = 0 then
            begin
              BuiltinExprKindByName := 3
            end
          else
            begin
              ClearText(expected_name);
              expected_name := 'abs';
              if StrCmpIgnoreCase(name, expected_name) = 0 then
                begin
                  BuiltinExprKindByName := 4
                end
              else
                begin
                  ClearText(expected_name);
                  expected_name := 'sqr';
                  if StrCmpIgnoreCase(name, expected_name) = 0 then
                    begin
                      BuiltinExprKindByName := 5
                    end
                  else
                    begin
                      ClearText(expected_name);
                      expected_name := 'odd';
                      if StrCmpIgnoreCase(name, expected_name) = 0 then
                        begin
                          BuiltinExprKindByName := 6
                        end
                      else
                        begin
                          ClearText(expected_name);
                          expected_name := 'upcase';
                          if StrCmpIgnoreCase(name, expected_name) = 0 then
                            begin
                              BuiltinExprKindByName := 7
                            end
                          else
                            begin
                              ClearText(expected_name);
                              expected_name := 'pos';
                              if StrCmpIgnoreCase(name, expected_name) = 0 then
                                begin
                                  BuiltinExprKindByName := 8
                                end
                              else
                                begin
                                  ClearText(expected_name);
                                  expected_name := 'hextoint';
                                  if StrCmpIgnoreCase(name, expected_name) = 0 then
                                    begin
                                      BuiltinExprKindByName := 9
                                    end
                                  else
                                    begin
                                      ClearText(expected_name);
                                      expected_name := 'low';
                                      if StrCmpIgnoreCase(name, expected_name) = 0 then
                                        begin
                                          BuiltinExprKindByName := 10
                                        end
                                  else
                                    begin
                                      ClearText(expected_name);
                                      expected_name := 'high';
                                      if StrCmpIgnoreCase(name, expected_name) = 0 then
                                        begin
                                          BuiltinExprKindByName := 11
                                        end
                                      else
                                        begin
                                          ClearText(expected_name);
                                          expected_name := 'round';
                                          if StrCmpIgnoreCase(name, expected_name) = 0 then
                                            begin
                                              BuiltinExprKindByName := 13
                                            end
                                          else
                                            begin
                                              ClearText(expected_name);
                                              expected_name := 'trunc';
                                              if StrCmpIgnoreCase(name, expected_name) = 0 then
                                                begin
                                                  BuiltinExprKindByName := 14
                                                end
                                            end
                                        end
                                    end
                                end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
end;

function BuildAstSetBitExpr(value_idx: integer): integer;
var expr_idx: integer;
begin
  expr_idx := NewAstExpr(AST_EXPR_CALL);
  ast_expr_op[expr_idx] := 12;
  ast_expr_left[expr_idx] := ast_arg_count;
  ast_expr_right[expr_idx] := 0;
  AppendAstCallExprArg(expr_idx, value_idx);
  BuildAstSetBitExpr := expr_idx
end;

function BuildAstSetRangeExpr(lo_idx: integer; hi_idx: integer): integer;
var expr_idx: integer;
begin
  expr_idx := NewAstExpr(AST_EXPR_CALL);
  ast_expr_op[expr_idx] := 16;
  ast_expr_left[expr_idx] := ast_arg_count;
  ast_expr_right[expr_idx] := 0;
  AppendAstCallExprArg(expr_idx, lo_idx);
  AppendAstCallExprArg(expr_idx, hi_idx);
  BuildAstSetRangeExpr := expr_idx
end;

function BuildAstPrimaryExpr: integer;
var expr_idx: integer;
    index_idx: integer;
    field_idx: integer;
    with_base_idx: integer;
    const_value: integer;
    enum_const_idx: integer;
    temp_text: text_buf;
    set_expr_idx: integer;
    zero_expr_idx: integer;
begin
  BuildAstPrimaryExpr := -1;
  if token_kind = TOK_LBRACK then
    begin
      NextToken();
      zero_expr_idx := NewAstExpr(AST_EXPR_INT);
      ast_expr_int[zero_expr_idx] := 0;
      set_expr_idx := zero_expr_idx;
      while token_kind <> TOK_RBRACK do
        begin
          expr_idx := BuildAstExpr();
          if token_kind = TOK_DOTDOT then
            begin
              NextToken();
              expr_idx := BuildAstSetRangeExpr(expr_idx, BuildAstExpr())
            end
          else
            begin
              expr_idx := BuildAstSetBitExpr(expr_idx)
            end;
          if set_expr_idx = zero_expr_idx then
            begin
              set_expr_idx := expr_idx
            end
          else
            begin
              set_expr_idx := BuildAstBinOpExpr(set_expr_idx, TOK_KW_OR, expr_idx)
            end;
          if token_kind = TOK_COMMA then
            begin
              NextToken()
            end
        end;
      ExpectKind(TOK_RBRACK);
      BuildAstPrimaryExpr := set_expr_idx
    end
  else if token_kind = TOK_REAL_LIT then
    begin
      expr_idx := NewAstExpr(AST_EXPR_REAL);
      ast_expr_text_ref[expr_idx] := NewAstTextLit(token_text);
      NextToken();
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_INT then
    begin
      expr_idx := NewAstExpr(AST_EXPR_INT);
      ast_expr_int[expr_idx] := token_value;
      NextToken();
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_STR then
    begin
      if token_text[1] = #0 then
        begin
          expr_idx := NewAstExpr(AST_EXPR_CHAR);
          ast_expr_int[expr_idx] := Ord(token_text[0]);
          NextToken();
          BuildAstPrimaryExpr := expr_idx
        end
      else
        begin
          bootstrap_capture_failed := true;
          parse_error_reason := 201;
          FailParse()
        end
    end
  else if token_kind = TOK_KW_TRUE then
    begin
      expr_idx := NewAstExpr(AST_EXPR_BOOL);
      ast_expr_int[expr_idx] := 1;
      NextToken();
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_KW_FALSE then
    begin
      expr_idx := NewAstExpr(AST_EXPR_BOOL);
      ast_expr_int[expr_idx] := 0;
      NextToken();
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_KW_NIL then
    begin
      expr_idx := NewAstExpr(AST_EXPR_NIL);
      ast_expr_int[expr_idx] := 0;
      NextToken();
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_LPAREN then
    begin
      NextToken();
      expr_idx := BuildAstExpr();
      ExpectKind(TOK_RPAREN);
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_IDENT then
    begin
      ClearText(temp_text);
      StrCopy(token_text, temp_text);
      NextToken();
      if token_kind = TOK_LPAREN then
        begin
          expr_idx := NewAstExpr(AST_EXPR_CALL);
          ast_expr_op[expr_idx] := BuiltinExprKindByName(temp_text);
          ast_expr_text_ref[expr_idx] := NewAstIdent(temp_text);
          BuildAstCallArgs(expr_idx);
          BuildAstPrimaryExpr := expr_idx
        end
      else
        begin
          if TryResolveBuiltinConst(temp_text, const_value) then
            begin
              expr_idx := NewAstExpr(AST_EXPR_INT);
              ast_expr_int[expr_idx] := const_value
            end
          else
            begin
              enum_const_idx := FindAstEnumConst(temp_text);
              if enum_const_idx >= 0 then
                begin
                  expr_idx := NewAstExpr(AST_EXPR_INT);
                  ast_expr_int[expr_idx] := ast_enum_const_value[enum_const_idx]
                end
              else
                begin
                  expr_idx := NewAstExpr(AST_EXPR_IDENT);
                  ast_expr_int[expr_idx] := FindScopedAstVar(temp_text);
                  ast_expr_text_ref[expr_idx] := NewAstIdent(temp_text);
                  if ast_expr_int[expr_idx] < 0 then
                    begin
                      if ast_with_type_ref >= 0 then
                        begin
                          if FindAstFieldByIdent(ast_with_type_ref, ast_ident_pool[ast_expr_text_ref[expr_idx]]) >= 0 then
                            begin
                              with_base_idx := NewAstExpr(AST_EXPR_IDENT);
                              ast_expr_int[with_base_idx] := ast_with_var;
                              ast_expr_kind[expr_idx] := AST_EXPR_FIELD;
                              ast_expr_left[expr_idx] := with_base_idx
                            end
                        end
                    end
                end
            end;
          while IsSelectorToken() do
            begin
              if token_kind = TOK_DOT then
                begin
                  NextToken();
                  if token_kind <> TOK_IDENT then
                    begin
                      parse_error_reason := 202;
                      FailParse()
                    end;
                  field_idx := NewAstExpr(AST_EXPR_FIELD);
                  ast_expr_left[field_idx] := expr_idx;
                  ast_expr_text_ref[field_idx] := NewAstIdent(token_text);
                  expr_idx := field_idx;
                  NextToken()
                end
              else if token_kind = TOK_LBRACK then
                begin
                  NextToken();
                  index_idx := BuildAstExpr();
                  field_idx := NewAstExpr(AST_EXPR_INDEX);
                  ast_expr_left[field_idx] := expr_idx;
                  ast_expr_right[field_idx] := index_idx;
                  expr_idx := field_idx;
                  while token_kind = TOK_COMMA do
                    begin
                      NextToken();
                      index_idx := BuildAstExpr();
                      field_idx := NewAstExpr(AST_EXPR_INDEX);
                      ast_expr_left[field_idx] := expr_idx;
                      ast_expr_right[field_idx] := index_idx;
                      expr_idx := field_idx
                    end;
                  ExpectKind(TOK_RBRACK)
                end
              else
                begin
                  ParseDerefSelector();
                  field_idx := NewAstExpr(AST_EXPR_DEREF);
                  ast_expr_left[field_idx] := expr_idx;
                  expr_idx := field_idx
                end
            end;
          BuildAstPrimaryExpr := expr_idx
        end
    end
  else if IsLiteralKeywordToken() then
    begin
      bootstrap_capture_failed := true;
      if parse_error_reason = 0 then
        begin
          parse_error_reason := 205
        end;
      NextToken()
    end
  else
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 203;
      FailParse()
    end
end;

function BuildAstSetMembershipExpr(left_idx: integer; right_idx: integer): integer;
var bit_expr_idx: integer;
    and_expr_idx: integer;
    zero_expr_idx: integer;
begin
  bit_expr_idx := NewAstExpr(AST_EXPR_CALL);
  ast_expr_op[bit_expr_idx] := 12;
  ast_expr_left[bit_expr_idx] := ast_arg_count;
  ast_expr_right[bit_expr_idx] := 0;
  AppendAstCallExprArg(bit_expr_idx, left_idx);
  and_expr_idx := BuildAstBinOpExpr(right_idx, TOK_KW_AND, bit_expr_idx);
  zero_expr_idx := NewAstExpr(AST_EXPR_INT);
  ast_expr_int[zero_expr_idx] := 0;
  BuildAstSetMembershipExpr := BuildAstBinOpExpr(and_expr_idx, TOK_NE, zero_expr_idx)
end;

function BuildAstUnaryExpr: integer;
var op_kind: integer;
    expr_idx: integer;
    unary_idx: integer;
begin
  if IsUnaryToken() then
    begin
      op_kind := token_kind;
      NextToken();
      expr_idx := BuildAstUnaryExpr();
      unary_idx := NewAstExpr(AST_EXPR_UNARY);
      ast_expr_op[unary_idx] := op_kind;
      ast_expr_left[unary_idx] := expr_idx;
      BuildAstUnaryExpr := unary_idx
    end
  else
    begin
      BuildAstUnaryExpr := BuildAstPrimaryExpr()
    end
end;

function BuildAstBinOpExpr(left_idx: integer; op_kind: integer; right_idx: integer): integer;
var expr_idx: integer;
begin
  expr_idx := NewAstExpr(AST_EXPR_BINOP);
  ast_expr_op[expr_idx] := op_kind;
  ast_expr_left[expr_idx] := left_idx;
  ast_expr_right[expr_idx] := right_idx;
  BuildAstBinOpExpr := expr_idx
end;

function BuildAstMulExpr: integer;
var expr_idx: integer;
    right_idx: integer;
    op_kind: integer;
begin
  expr_idx := BuildAstUnaryExpr();
  while IsMulOpToken() do
    begin
      op_kind := token_kind;
      NextToken();
      right_idx := BuildAstUnaryExpr();
      expr_idx := BuildAstBinOpExpr(expr_idx, op_kind, right_idx)
    end;
  BuildAstMulExpr := expr_idx
end;

function BuildAstAddExpr: integer;
var expr_idx: integer;
    right_idx: integer;
    op_kind: integer;
begin
  expr_idx := BuildAstMulExpr();
  while IsAddOpToken() do
    begin
      op_kind := token_kind;
      NextToken();
      right_idx := BuildAstMulExpr();
      expr_idx := BuildAstBinOpExpr(expr_idx, op_kind, right_idx)
    end;
  BuildAstAddExpr := expr_idx
end;

function BuildAstRelExpr: integer;
var expr_idx: integer;
    right_idx: integer;
    op_kind: integer;
begin
  expr_idx := BuildAstAddExpr();
  if IsRelOpToken() then
    begin
      op_kind := token_kind;
      NextToken();
      right_idx := BuildAstAddExpr();
      if op_kind = TOK_KW_IN then
        begin
          expr_idx := BuildAstSetMembershipExpr(expr_idx, right_idx)
        end
      else
        begin
          expr_idx := BuildAstBinOpExpr(expr_idx, op_kind, right_idx)
        end
    end;
  BuildAstRelExpr := expr_idx
end;

function BuildAstExpr: integer;
begin
  BuildAstExpr := BuildAstRelExpr()
end;

procedure BuildExpr;
begin
  ParseExpr()
end;

procedure BuildLValue;
begin
  if token_kind <> TOK_IDENT then
    begin
      parse_error_reason := 204;
      FailParse()
    end;
  NextToken();
  ParseSelectorSuffixes()
end;
