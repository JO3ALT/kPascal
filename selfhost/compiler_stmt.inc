procedure ExpectSymbol(ch: char);
begin
  if (current_kind <> TOK_SYMBOL) or (current_text[0] <> ch) then
    FailParse;
  ReadToken()
end;

procedure ParseWriteLn;
var value: integer;
begin
  ReadToken(); // consume writeln
  ExpectSymbol('(');
  value := ParseExpr();
  EmitIntLine(value);
  ExpectSymbol(')')
end;

procedure ParseAssignment;
var namebuf: token_buf;
    value: integer;
begin
  StrCopy(current_text, namebuf);
  ReadToken();
  ExpectSymbol(':');
  ExpectSymbol('=');
  value := ParseExpr();
  if FindVarSlot(namebuf) < 0 then
    DeclareVar(namebuf);
  StoreNamedValue(namebuf, value)
end;

procedure ParseCompoundStmt;
begin
  if not NameEquals(current_text, 'begin') then
    FailParse;
  ReadToken();
  while not NameEquals(current_text, 'end') do
    begin
      ParseStatement();
      if TokenEquals(current_text, ';') then
        ReadToken()
      else
        break
    end;
  if not NameEquals(current_text, 'end') then
    FailParse;
  ReadToken()
end;

procedure ParseIfStmt;
var cond: integer;
begin
  ReadToken();
  cond := ParseExpr();
  if not NameEquals(current_text, 'then') then
    FailParse;
  ReadToken();
  if cond <> 0 then
    ParseStatement()
  else
    SkipStatement();
  if TokenEquals(current_text, 'else') then
    begin
      ReadToken();
      if cond = 0 then
        ParseStatement()
      else
        SkipStatement()
    end
end;

procedure ParseWhileStmt;
var cond: integer;
begin
  ReadToken();
  cond := ParseExpr();
  if not NameEquals(current_text, 'do') then
    FailParse;
  ReadToken();
  while cond <> 0 do
    begin
      ParseStatement();
      cond := ParseExpr()
    end
end;

procedure ParseRepeatStmt;
begin
  ReadToken();
  repeat
    ParseStatement();
    if TokenEquals(current_text, ';') then
      ReadToken();
  until TokenEquals(current_text, 'until');
  ReadToken();
  ParseExpr()
end;

procedure ParseForStmt;
var namebuf: token_buf;
    startv, limitv: integer;
begin
  ReadToken();
  StrCopy(current_text, namebuf);
  ReadToken();
  ExpectSymbol(':');
  ExpectSymbol('=');
  startv := ParseExpr();
  if not NameEquals(current_text, 'to') then
    FailParse;
  ReadToken();
  limitv := ParseExpr();
  if not NameEquals(current_text, 'do') then
    FailParse;
  ReadToken();
  StoreNamedValue(namebuf, startv);
  while ReadNamedValue(namebuf) <= limitv do
    begin
      ParseStatement();
      StoreNamedValue(namebuf, ReadNamedValue(namebuf) + 1)
    end
end;

procedure ParseCaseStmt;
var sel: integer;
begin
  ReadToken();
  sel := ParseExpr();
  if not NameEquals(current_text, 'of') then
    FailParse;
  ReadToken();
  while not TokenEquals(current_text, 'end') do
    begin
      if current_kind = TOK_INT then
        begin
          if current_value = sel then
            ParseStatement()
          else
            SkipStatement();
          ReadToken()
        end
      else
        ReadToken()
    end;
  ExpectSymbol('e');
  ReadToken()
end;

procedure ParseStatement;
begin
  if NameEquals(current_text, 'writeln') then
    ParseWriteLn()
  else if NameEquals(current_text, 'if') then
    ParseIfStmt()
  else if NameEquals(current_text, 'while') then
    ParseWhileStmt()
  else if NameEquals(current_text, 'repeat') then
    ParseRepeatStmt()
  else if NameEquals(current_text, 'for') then
    ParseForStmt()
  else if NameEquals(current_text, 'case') then
    ParseCaseStmt()
  else
    ParseAssignment()
end;
