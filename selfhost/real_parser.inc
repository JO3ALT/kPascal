procedure FailRealParse;
begin
  WriteLn('ABORT" selfhost real parse error"')
end;

procedure ExpectRealKind(kind: integer);
begin
  if current_kind <> kind then
    FailRealParse()
end;

procedure ExpectRealSymbol(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailRealParse()
  else if current_text[0] <> ch then
    FailRealParse()
end;

procedure ParseRealProgram;
begin
  NextToken();
  ExpectRealKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectRealKind(TOK_IDENT);
  NextToken();
  ExpectRealSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_var) = false then
    FailRealParse();
  NextToken();
  ExpectRealKind(TOK_IDENT);
  StrCopy(current_text, saved_text);
  NextToken();
  ExpectRealSymbol(':');
  NextToken();
  ExpectRealKind(TOK_IDENT);
  NextToken();
  ExpectRealSymbol(';');
  NextToken();

  Write('CREATE ');
  Write(saved_text);
  WriteLn(' 0 ,');

  if StrEqIgnoreCase(current_text, kw_begin) = false then
    FailRealParse();
  WriteLn(': MAIN');
  NextToken();

  ExpectRealKind(TOK_IDENT);
  NextToken();
  ExpectAssignSymbol();
  NextToken();
  ExpectRealKind(TOK_INT);
  if current_value <> 7 then
    FailRealParse();
  NextToken();
  ExpectRealSymbol('.');
  NextToken();
  ExpectRealKind(TOK_INT);
  if current_value <> 0 then
    FailRealParse();
  NextToken();
  ExpectRealSymbol('/');
  NextToken();
  ExpectRealKind(TOK_INT);
  if current_value <> 2 then
    FailRealParse();
  NextToken();
  ExpectRealSymbol('.');
  NextToken();
  ExpectRealKind(TOK_INT);
  if current_value <> 0 then
    FailRealParse();
  Write('1088421888 1073741824 FDIV ');
  Write(saved_text);
  WriteLn(' PVAR!');
  NextToken();
  ExpectRealSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailRealParse();
  NextToken();
  ExpectRealSymbol('(');
  NextToken();
  Write(saved_text);
  WriteLn(' PVAR@ PWRITE-F32');
  NextToken();
  ExpectRealSymbol(')');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectRealSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailRealParse();
  NextToken();
  ExpectRealSymbol('(');
  NextToken();
  ExpectRealKind(TOK_IDENT);
  NextToken();
  ExpectRealSymbol('(');
  NextToken();
  Write(saved_text);
  WriteLn(' PVAR@ FROUND-I32 PWRITE-I32');
  NextToken();
  ExpectRealSymbol(')');
  NextToken();
  ExpectRealSymbol(')');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectRealSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailRealParse();
  NextToken();
  ExpectRealSymbol('(');
  NextToken();
  ExpectRealKind(TOK_IDENT);
  NextToken();
  ExpectRealSymbol('(');
  NextToken();
  Write(saved_text);
  WriteLn(' PVAR@ F>S PWRITE-I32');
  NextToken();
  ExpectRealSymbol(')');
  NextToken();
  ExpectRealSymbol(')');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectRealKind(TOK_KW_END);
  NextToken();
  ExpectRealSymbol('.');
  WriteLn(';');
  WriteLn('MAIN')
end;
