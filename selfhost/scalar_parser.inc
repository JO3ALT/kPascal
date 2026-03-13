procedure FailScalarParse;
begin
  WriteLn('ABORT" selfhost scalar parse error"')
end;

procedure ExpectScalarKind(kind: integer);
begin
  if current_kind <> kind then
    FailScalarParse()
end;

procedure ExpectScalarSymbol(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailScalarParse()
  else if current_text[0] <> ch then
    FailScalarParse()
end;

procedure ParseScalarProgram;
begin
  NextToken();
  ExpectScalarKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol(';');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_begin) = false then
    FailScalarParse();
  WriteLn(': MAIN');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailScalarParse();
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarSymbol('-');
  NextToken();
  ExpectScalarKind(TOK_INT);
  Write(current_value);
  WriteLn(' NEGATE DUP 0< IF NEGATE THEN PWRITE-I32');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailScalarParse();
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_INT);
  Write(current_value);
  WriteLn(' DUP * PWRITE-I32');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailScalarParse();
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_INT);
  Write(current_value);
  WriteLn(' 1 AND 0= 0= PWRITE-BOOL');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailScalarParse();
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_STR);
  Write(Ord(current_text[0]));
  WriteLn(' DUP 97 >= OVER 122 <= AND IF 32 - THEN PWRITE-CHAR');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailScalarParse();
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_IDENT);
  NextToken();
  ExpectScalarSymbol('(');
  NextToken();
  ExpectScalarKind(TOK_INT);
  Write(current_value);
  WriteLn(' PWRITE-I32');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarSymbol(')');
  NextToken();
  ExpectScalarKind(TOK_KW_END);
  NextToken();
  ExpectScalarSymbol('.');
  WriteLn(';');
  WriteLn('MAIN')
end;
