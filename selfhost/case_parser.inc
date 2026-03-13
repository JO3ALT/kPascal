procedure FailCaseParse;
begin
  WriteLn('ABORT" selfhost case parse error"')
end;

procedure ExpectCaseKind(kind: integer);
begin
  if current_kind <> kind then
    FailCaseParse()
end;

procedure ExpectCaseSymbol(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailCaseParse()
  else if current_text[0] <> ch then
    FailCaseParse()
end;

procedure ExpectCaseRangeSymbol;
begin
  if current_kind <> TOK_SYMBOL then
    FailCaseParse()
  else if current_text[0] <> '.' then
    FailCaseParse()
  else if current_text[1] <> '.' then
    FailCaseParse()
end;

procedure EmitSavedCaseString;
var
  i: integer;
begin
  i := 0;
  while saved_text[i] <> #0 do
    begin
      Write('      ');
      Write(Ord(saved_text[i]));
      WriteLn(' PWRITE-CHAR');
      i := i + 1
    end;
  WriteLn('      PWRITELN')
end;

procedure ParseCaseProgram;
var
  low_text: lexeme_buf;
  mid_text: lexeme_buf;
  high_text: lexeme_buf;
  var_name: lexeme_buf;
begin
  NextToken();
  ExpectCaseKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectCaseKind(TOK_IDENT);
  NextToken();
  ExpectCaseSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_var) = false then
    FailCaseParse();
  NextToken();
  ExpectCaseKind(TOK_IDENT);
  StrCopy(current_text, var_name);
  NextToken();
  ExpectCaseSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_integer) = false then
    FailCaseParse();
  NextToken();
  ExpectCaseSymbol(';');
  NextToken();

  Write('CREATE ');
  Write(var_name);
  WriteLn(' 0 ,');
  WriteLn('CREATE __CASE_MATCH 0 ,');

  if StrEqIgnoreCase(current_text, kw_begin) = false then
    FailCaseParse();
  WriteLn(': MAIN');
  NextToken();

  ExpectCaseKind(TOK_IDENT);
  NextToken();
  ExpectAssignSymbol();
  NextToken();
  ExpectCaseKind(TOK_INT);
  Write(current_value);
  Write(' ');
  Write(var_name);
  WriteLn(' PVAR!');
  NextToken();
  ExpectCaseSymbol(';');
  NextToken();

  ExpectCaseKind(TOK_IDENT);
  low_text := 'case';
  if StrEqIgnoreCase(current_text, low_text) = false then
    FailCaseParse();
  NextToken();
  if StrEqIgnoreCase(current_text, var_name) = false then
    FailCaseParse();
  NextToken();
  low_text := 'of';
  if StrEqIgnoreCase(current_text, low_text) = false then
    FailCaseParse();
  low_text := '';
  mid_text := '';
  high_text := '';
  Write(var_name);
  WriteLn(' PVAR@ >R');
  WriteLn('  0 __CASE_MATCH PVAR!');
  NextToken();

  ExpectCaseKind(TOK_INT);
  NextToken();
  ExpectCaseSymbol(',');
  NextToken();
  ExpectCaseKind(TOK_INT);
  NextToken();
  ExpectCaseSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailCaseParse();
  NextToken();
  ExpectCaseSymbol('(');
  NextToken();
  ExpectCaseKind(TOK_STR);
  StrCopy(current_text, low_text);
  NextToken();
  ExpectCaseSymbol(')');
  NextToken();
  ExpectCaseSymbol(';');
  NextToken();

  ExpectCaseKind(TOK_INT);
  NextToken();
  ExpectCaseRangeSymbol();
  NextToken();
  ExpectCaseKind(TOK_INT);
  NextToken();
  ExpectCaseSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailCaseParse();
  NextToken();
  ExpectCaseSymbol('(');
  NextToken();
  ExpectCaseKind(TOK_STR);
  StrCopy(current_text, mid_text);
  NextToken();
  ExpectCaseSymbol(')');
  NextToken();
  low_text := 'else';
  if StrEqIgnoreCase(current_text, low_text) = false then
    FailCaseParse();
  NextToken();
  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailCaseParse();
  NextToken();
  ExpectCaseSymbol('(');
  NextToken();
  ExpectCaseKind(TOK_STR);
  StrCopy(current_text, high_text);
  NextToken();
  ExpectCaseSymbol(')');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_end) = false then
    FailCaseParse();

  WriteLn('  __CASE_MATCH PVAR@ 0= IF');
  WriteLn('    R@ 1 = R@ 2 = OR IF');
  WriteLn('      1 __CASE_MATCH PVAR!');
  StrCopy(low_text, saved_text);
  EmitSavedCaseString();
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  __CASE_MATCH PVAR@ 0= IF');
  WriteLn('    R@ 3 >= R@ 5 <= AND IF');
  WriteLn('      1 __CASE_MATCH PVAR!');
  StrCopy(mid_text, saved_text);
  EmitSavedCaseString();
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  __CASE_MATCH PVAR@ 0= IF');
  StrCopy(high_text, saved_text);
  EmitSavedCaseString();
  WriteLn('  THEN');
  WriteLn('  R> DROP');

  NextToken();
  ExpectCaseKind(TOK_KW_END);
  NextToken();
  ExpectCaseSymbol('.');
  WriteLn(';');
  WriteLn('MAIN')
end;
