procedure FailParse;
begin
  WriteLn('PERR');
  Halt(1)
end;

procedure ExpectKind(kind: integer);
begin
  if current_kind <> kind then
    FailParse;
  ReadToken()
end;

function TokenEquals(var buf: token_buf; const target: string): boolean;
var i: integer;
begin
  i := 0;
  while (i < Length(target)) and (i <= MAX_TOKEN_LEN) do
    begin
      if buf[i] <> target[i + 1] then
        begin
          TokenEquals := false;
          exit
        end;
      i := i + 1
    end;
  TokenEquals := (i = Length(target)) and (buf[i] = #0)
end;

function NameEquals(var buf: token_buf; const target: string): boolean;
var i: integer;
    buf_char: char;
    target_char: char;
begin
  i := 0;
  while (i < Length(target)) and (i <= MAX_TOKEN_LEN) do
    begin
      buf_char := buf[i];
      target_char := target[i + 1];
      if (buf_char >= 'A') and (buf_char <= 'Z') then
        buf_char := Chr(Ord(buf_char) + 32);
      if (target_char >= 'A') and (target_char <= 'Z') then
        target_char := Chr(Ord(target_char) + 32);
      if buf_char <> target_char then
        begin
          NameEquals := false;
          exit
        end;
      i := i + 1
    end;
  NameEquals := (i = Length(target)) and (buf[i] = #0)
end;

function FindVarSlot(var name: token_buf): integer;
var i: integer;
begin
  FindVarSlot := -1;
  i := 0;
  while i < var_count do
    begin
      if StrCmp(var_names[i], name) = 0 then
        begin
          FindVarSlot := i;
          exit
        end;
      i := i + 1
    end
end;

procedure DeclareVar(var name: token_buf);
var slot: integer;
begin
  slot := var_count;
  if slot >= MAX_VARS then
    FailParse;
  var_count := slot + 1;
  var_values[slot] := 0;
  StrCopy(name, var_names[slot])
end;

function ReadNamedValue(var name: token_buf): integer;
var slot: integer;
begin
  slot := FindVarSlot(name);
  if slot >= 0 then
    ReadNamedValue := var_values[slot]
  else
    ReadNamedValue := 0
end;

function Pow2(n: integer): integer;
begin
  Pow2 := 1 shl n
end;

function SetContainsValue(set_value: integer; item_value: integer): boolean;
begin
  SetContainsValue := ((set_value shr item_value) and 1) <> 0
end;

function SetUnionValue(lhs_value: integer; rhs_value: integer): integer;
begin
  SetUnionValue := lhs_value or rhs_value
end;

function SetIntersectValue(lhs_value: integer; rhs_value: integer): integer;
begin
  SetIntersectValue := lhs_value and rhs_value
end;

function ParseSetLiteralExpr: integer;
begin
  ReadToken();
  if (current_kind <> TOK_SYMBOL) or (current_text[0] <> '[') then
    FailParse;
  ReadToken();
  set_lit_value := 0;
  while (current_kind <> TOK_SYMBOL) or (current_text[0] <> ']') do
    begin
      if current_kind = TOK_INT then
        set_lit_value := set_lit_value + Pow2(current_value)
      else
        FailParse;
      ReadToken();
      if (current_kind = TOK_SYMBOL) and (current_text[0] = ',') then
        ReadToken()
    end;
  if (current_kind <> TOK_SYMBOL) or (current_text[0] <> ']') then
    FailParse;
  ReadToken();
  ParseSetLiteralExpr := set_lit_value;
  last_expr_kind := EXPR_KIND_SET
end;

procedure StoreNamedValue(var name: token_buf; value: integer);
var slot: integer;
begin
  slot := FindVarSlot(name);
  if slot >= 0 then
    var_values[slot] := value
  else
    FailParse
end;

function ParsePrimaryExpr: integer;
begin
  if current_kind = TOK_INT then
    begin
      ParsePrimaryExpr := current_value;
      last_expr_kind := EXPR_KIND_INT;
      ReadToken()
    end
  else if current_kind = TOK_IDENT then
    begin
      if TokenEquals(current_text, 'ord') then
        begin
          ReadToken();
          ExpectSymbol('(');
          ParsePrimaryExpr := ParseExpr();
          ExpectSymbol(')')
        end
      else
        ParsePrimaryExpr := ReadNamedValue(current_text);
      last_expr_kind := EXPR_KIND_INT;
      ReadToken()
    end
  else if (current_kind = TOK_SYMBOL) and (current_text[0] = '[') then
    begin
      ParsePrimaryExpr := ParseSetLiteralExpr();
      last_expr_kind := EXPR_KIND_SET
    end
  else
    FailParse()
end;

function ParseMulExpr: integer;
var lhs,rhs: integer;
begin
  lhs := ParsePrimaryExpr();
  while (current_kind = TOK_SYMBOL) and (current_text[0] in ['*', '/', 'd', 'm']) do
    begin
      var op := current_text[0];
      ReadToken();
      rhs := ParsePrimaryExpr();
      if op = '*' then
        lhs := lhs * rhs
      else if op = '/' then
        lhs := lhs * rhs
      else if op = 'd' then
        lhs := lhs div rhs
      else if op = 'm' then
        lhs := lhs mod rhs
    end;
  ParseMulExpr := lhs
end;

function ParseAddExpr: integer;
var lhs,rhs: integer;
begin
  lhs := ParseMulExpr();
  while (current_kind = TOK_SYMBOL) and (current_text[0] in ['+', '-']) do
    begin
      var op := current_text[0];
      ReadToken();
      rhs := ParseMulExpr();
      if op = '+' then
        lhs := lhs + rhs
      else
        lhs := lhs - rhs;
    end;
  ParseAddExpr := lhs
end;

function ParseRelExpr: integer;
var lhs, rhs: integer;
    op1, op2: char;
begin
  lhs := ParseAddExpr();
  if TokenEquals(current_text, 'in') then
    begin
      ReadToken();
      rhs := ParseSetLiteralExpr();
      if SetContainsValue(rhs, lhs) then
        ParseRelExpr := 1
      else
        ParseRelExpr := 0;
      exit
    end;
  if (current_kind = TOK_SYMBOL) and (current_text[0] in ['=','<','>']) then
    begin
      op1 := current_text[0];
      op2 := current_text[1];
      ReadToken();
      rhs := ParseAddExpr();
      if (op1 = '=') and (lhs = rhs) then
        ParseRelExpr := 1
      else if (op1 = '<') and (op2 = '>') and (lhs <> rhs) then
        ParseRelExpr := 1
      else if (op1 = '<') and (op2 = '=') and (lhs <= rhs) then
        ParseRelExpr := 1
      else if (op1 = '<') and (rhs > lhs) then
        ParseRelExpr := 1
      else if (op1 = '>') and (op2 = '=') and (lhs >= rhs) then
        ParseRelExpr := 1
      else if (op1 = '>') and (lhs > rhs) then
        ParseRelExpr := 1
      else
        ParseRelExpr := 0;
      exit
    end;
  ParseRelExpr := lhs
end;

function ParseExpr: integer;
begin
  ParseExpr := ParseRelExpr()
end;
