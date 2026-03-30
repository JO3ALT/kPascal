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

function BuildAstPrimaryExpr: integer;
var expr_idx: integer;
    index_idx: integer;
    field_idx: integer;
    temp_text: text_buf;
begin
  BuildAstPrimaryExpr := -1;
  if token_kind = TOK_INT then
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
  else if token_kind = TOK_LPAREN then
    begin
      NextToken();
      expr_idx := BuildAstExpr();
      ExpectKind(TOK_RPAREN);
      BuildAstPrimaryExpr := expr_idx
    end
  else if token_kind = TOK_IDENT then
    begin
      expr_idx := NewAstExpr(AST_EXPR_IDENT);
      ClearText(temp_text);
      StrCopy(token_text, temp_text);
      ast_expr_int[expr_idx] := FindAstVar(temp_text);
      StrCopy(temp_text, ast_expr_text[expr_idx]);
      NextToken();
      if token_kind = TOK_LPAREN then
        begin
          bootstrap_capture_failed := true;
          ParseCallSuffix();
          BuildAstPrimaryExpr := -1
        end
      else
        begin
          while IsSelectorToken() do
            begin
              if token_kind = TOK_DOT then
                begin
                  NextToken();
                  if token_kind <> TOK_IDENT then
                    begin
                      FailParse()
                    end;
                  field_idx := NewAstExpr(AST_EXPR_FIELD);
                  ast_expr_left[field_idx] := expr_idx;
                  StrCopy(token_text, ast_expr_text[field_idx]);
                  expr_idx := field_idx;
                  NextToken()
                end
              else if token_kind = TOK_LBRACK then
                begin
                  NextToken();
                  index_idx := BuildAstExpr();
                  ExpectKind(TOK_RBRACK);
                  field_idx := NewAstExpr(AST_EXPR_INDEX);
                  ast_expr_left[field_idx] := expr_idx;
                  ast_expr_right[field_idx] := index_idx;
                  expr_idx := field_idx
                end
              else
                begin
                  bootstrap_capture_failed := true;
                  ParseDerefSelector();
                  expr_idx := -1
                end
            end;
          BuildAstPrimaryExpr := expr_idx
        end
    end
  else if IsLiteralKeywordToken() then
    begin
      bootstrap_capture_failed := true;
      NextToken()
    end
  else
    begin
      bootstrap_capture_failed := true;
      FailParse()
    end
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
      expr_idx := BuildAstBinOpExpr(expr_idx, op_kind, right_idx)
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
      FailParse()
    end;
  NextToken();
  ParseSelectorSuffixes()
end;
