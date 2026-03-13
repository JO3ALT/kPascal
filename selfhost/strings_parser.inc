procedure FailStringParse;
begin
  WriteLn('ABORT" selfhost string parse error"')
end;

procedure ExpectStringKind(kind: integer);
begin
  if current_kind <> kind then
    FailStringParse()
end;

procedure ExpectStringSymbol(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailStringParse()
  else if current_text[0] <> ch then
    FailStringParse()
end;

procedure ParseStringProgram;
begin
  NextToken();
  ExpectStringKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectStringKind(TOK_IDENT);
  NextToken();
  ExpectStringSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_type) = false then
    FailStringParse();
  NextToken();
  ExpectStringKind(TOK_IDENT);
  StrCopy(current_text, string_type_name);
  NextToken();
  ExpectStringSymbol('=');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_array) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol('[');
  NextToken();
  ExpectStringKind(TOK_INT);
  char_array_len := current_value;
  NextToken();
  ExpectStringSymbol(']');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_of) = false then
    FailStringParse();
  NextToken();
  if StrEqIgnoreCase(current_text, kw_char) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_var) = false then
    FailStringParse();
  NextToken();
  ExpectStringKind(TOK_IDENT);
  StrCopy(current_text, string_var1_name);
  NextToken();
  ExpectStringSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol(';');
  NextToken();
  ExpectStringKind(TOK_IDENT);
  StrCopy(current_text, string_var2_name);
  NextToken();
  ExpectStringSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol(';');
  NextToken();

  WriteLn('CREATE __WSTR_STOP 0 ,');
  WriteLn('CREATE __STR_SRC 0 ,');
  WriteLn('CREATE __STR_A 0 ,');
  WriteLn('CREATE __STR_B 0 ,');
  WriteLn('CREATE __STR_I 0 ,');
  WriteLn('CREATE __STR_J 0 ,');
  WriteLn('CREATE __STR_LEN 0 ,');
  WriteLn('CREATE __STR_POS 0 ,');
  WriteLn('CREATE __STR_MATCH 0 ,');
  WriteLn(': __STRLEN');
  WriteLn('  0 __STR_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= IF');
  WriteLn('      1');
  WriteLn('    ELSE');
  WriteLn('      __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('      0');
  WriteLn('    THEN');
  WriteLn('  UNTIL');
  WriteLn('  __STR_I PVAR@');
  WriteLn(';');
  WriteLn(': __STRPOS');
  WriteLn('  __STR_A PVAR@ __STR_SRC PVAR!');
  WriteLn('  __STRLEN __STR_LEN PVAR!');
  WriteLn('  __STR_LEN PVAR@ 0= IF');
  WriteLn('    1');
  WriteLn('  ELSE');
  WriteLn('    0 __STR_POS PVAR!');
  WriteLn('    0 __STR_I PVAR!');
  WriteLn('    BEGIN');
  WriteLn('      __STR_POS PVAR@ 0= __STR_B PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= 0= AND WHILE');
  WriteLn('        0 __STR_J PVAR!');
  WriteLn('        1 __STR_MATCH PVAR!');
  WriteLn('        BEGIN');
  WriteLn('          __STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= 0= AND WHILE');
  WriteLn('            __STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@');
  WriteLn('            __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ = 0= IF');
  WriteLn('              0 __STR_MATCH PVAR!');
  WriteLn('            THEN');
  WriteLn('            __STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@ 0= IF');
  WriteLn('              0 __STR_MATCH PVAR!');
  WriteLn('            THEN');
  WriteLn('            __STR_J PVAR@ 1 + __STR_J PVAR!');
  WriteLn('        REPEAT');
  WriteLn('        __STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= AND IF');
  WriteLn('          __STR_I PVAR@ 1 + __STR_POS PVAR!');
  WriteLn('        THEN');
  WriteLn('        __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('    REPEAT');
  WriteLn('    __STR_POS PVAR@');
  WriteLn('  THEN');
  WriteLn(';');
  Write('CREATE ');
  Write(string_var1_name);
  Write(' 0 , ');
  Write((char_array_len - 1) * 4);
  WriteLn(' ALLOT');
  Write('CREATE ');
  Write(string_var2_name);
  Write(' 0 , ');
  Write((char_array_len - 1) * 4);
  WriteLn(' ALLOT');

  if StrEqIgnoreCase(current_text, kw_begin) = false then
    FailStringParse();
  WriteLn(': MAIN');
  NextToken();
  ExpectStringKind(TOK_IDENT);
  NextToken();
  ExpectStringSymbol(':');
  NextToken();
  ExpectStringKind(TOK_STR);
  assign_text := string_var1_name;
  EmitStringStore();
  NextToken();
  ExpectStringSymbol(';');
  NextToken();

  ExpectStringKind(TOK_IDENT);
  NextToken();
  ExpectStringSymbol(':');
  NextToken();
  ExpectStringKind(TOK_STR);
  assign_text := string_var2_name;
  EmitStringStore();
  NextToken();
  ExpectStringSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol('(');
  NextToken();
  EmitStringWrite();
  NextToken();
  ExpectStringSymbol(')');
  NextToken();
  ExpectStringSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol('(');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_pos) = false then
    FailStringParse();
  NextToken();
  ExpectStringSymbol('(');
  NextToken();
  Write(current_text);
  Write(' __STR_A PVAR! ');
  NextToken();
  ExpectStringSymbol(',');
  NextToken();
  Write(current_text);
  WriteLn(' __STR_B PVAR! __STRPOS PWRITE-I32');
  NextToken();
  ExpectStringSymbol(')');
  NextToken();
  ExpectStringSymbol(')');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectStringKind(TOK_KW_END);
  NextToken();
  ExpectStringSymbol('.');
  WriteLn(';');
  WriteLn('MAIN')
end;
