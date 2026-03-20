procedure ParseVarDecl;
var namebuf: token_buf;
begin
  StrCopy(current_text, namebuf);
  ReadToken();
  ExpectSymbol(':');
  if current_kind <> TOK_IDENT then
    FailParse;
  ReadToken();
  ExpectSymbol(';');
  DeclareVar(namebuf)
end;

procedure ParseVarSection;
begin
  ReadToken(); // consume 'var'
  while current_kind = TOK_IDENT do
    ParseVarDecl()
end;

procedure ParseBlock;
begin
  while TokenEquals(current_text, 'var') do
    ParseVarSection()
end;

procedure SkipStatement;
begin
  ReadToken()
end;

procedure ParseVarDecl;
var namebuf: token_buf;
begin
  StrCopy(current_text, namebuf);
  ReadToken();
  ExpectSymbol(':');
  if current_kind <> TOK_IDENT then
    FailParse;
  ReadToken();
  ExpectSymbol(';');
  DeclareVar(namebuf)
end;

procedure ParseVarSection;
begin
  ReadToken(); // var
  while current_kind = TOK_IDENT do
    ParseVarDecl()
end;

procedure ParseConstSection;
var namebuf: token_buf;
    value: integer;
begin
  ReadToken(); // const
  while current_kind = TOK_IDENT do
    begin
      StrCopy(current_text, namebuf);
      ReadToken();
      ExpectSymbol('=');
      value := ParseExpr();
      if FindVarSlot(namebuf) < 0 then
        DeclareVar(namebuf);
      StoreNamedValue(namebuf, value);
      ExpectSymbol(';')
    end
end;

procedure DeclareTypeEntry(var name: token_buf; kind: integer);
var slot: integer;
begin
  slot := type_count;
  if slot >= MAX_VARS then
    FailParse;
  StrCopy(name, type_names[slot]);
  type_kinds[slot] := kind;
  type_count := slot + 1
end;

procedure ParseEnumType(var namebuf: token_buf);
var values: array[0..MAX_VARS - 1] of token_buf;
    valcount: integer;
    i: integer;
begin
  ExpectSymbol('(');
  ReadToken();
  valcount := 0;
  while current_kind = TOK_IDENT do
    begin
      StrCopy(current_text, values[valcount]);
      valcount := valcount + 1;
      ReadToken();
      if TokenEquals(current_text, ',') then
        ReadToken()
    end;
  ExpectSymbol(')');
  DeclareTypeEntry(namebuf, 1);
  for i := 0 to valcount - 1 do
    begin
      if FindVarSlot(values[i]) < 0 then
        DeclareVar(values[i]);
      StoreNamedValue(values[i], i)
    end
end;

procedure ParseSetType(var namebuf: token_buf);
begin
  ReadToken(); // 'set'
  if not NameEquals(current_text, 'of') then
    FailParse;
  ReadToken();
  if current_kind <> TOK_IDENT then
    FailParse;
  DeclareTypeEntry(namebuf, 2);
  ReadToken()
end;

procedure ParseSubrangeType(var namebuf: token_buf);
var low, high: integer;
begin
  ReadToken(); // low
  low := current_value;
  ExpectSymbol('.');
  ExpectSymbol('.');
  ReadToken();
  high := current_value;
  DeclareTypeEntry(namebuf, 3);
  ReadToken()
end;

procedure ParseTypeSection;
var namebuf: token_buf;
begin
  ReadToken(); // type
  while current_kind = TOK_IDENT do
    begin
      StrCopy(current_text, namebuf);
      ReadToken();
      ExpectSymbol('=');
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '(' then
            ParseEnumType(namebuf)
          else
            FailParse
        end
      else if NameEquals(current_text, 'set') then
        ParseSetType(namebuf)
      else if current_kind = TOK_INT then
        ParseSubrangeType(namebuf)
      else
        FailParse;
      ExpectSymbol(';')
    end
end;

procedure ParseProgram;
begin
  ReadToken();
  if not NameEquals(current_text, 'program') then
    FailParse;
  ReadToken();
  if current_kind <> TOK_IDENT then
    FailParse;
  ReadToken();
  ExpectSymbol(';');
  ReadToken();
  while not TokenEquals(current_text, '.') do
    begin
      if NameEquals(current_text, 'type') then
        ParseTypeSection()
      else if NameEquals(current_text, 'const') then
        ParseConstSection()
      else if NameEquals(current_text, 'var') then
        ParseVarSection()
      else if NameEquals(current_text, 'begin') then
        ParseCompoundStmt()
      else
        FailParse;
    end;
  ExpectSymbol('.');
  ReadToken()
end;
