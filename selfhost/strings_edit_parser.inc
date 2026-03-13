procedure FailStringEditParse;
begin
  WriteLn('ABORT" selfhost string edit parse error"')
end;

procedure ExpectStringEditKind(kind: integer);
begin
  if current_kind <> kind then
    FailStringEditParse()
end;

procedure ExpectStringEditSymbol(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailStringEditParse()
  else if current_text[0] <> ch then
    FailStringEditParse()
end;

procedure EmitStringVarCreate(name: lexeme_buf);
begin
  Write('CREATE ');
  Write(name);
  Write(' 0 , ');
  Write((char_array_len - 1) * 4);
  WriteLn(' ALLOT')
end;

procedure EmitStringCopy;
begin
  WriteLn(': __STRCPY');
  WriteLn('  0 __STR_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ DUP __STR_DST PVAR@ __STR_I PVAR@ 4 * + PVAR!');
  WriteLn('    0= IF');
  WriteLn('      1');
  WriteLn('    ELSE');
  WriteLn('      __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('      0');
  WriteLn('    THEN');
  WriteLn('  UNTIL');
  WriteLn(';')
end;

procedure EmitStringDelete;
begin
  WriteLn(': __STRDELETE');
  WriteLn('  __STR_CNT PVAR@ 0 <= IF');
  WriteLn('    ( no-op )');
  WriteLn('  ELSE');
  WriteLn('    __STR_IDX PVAR@ 1 < IF');
  WriteLn('      1 __STR_IDX PVAR!');
  WriteLn('    THEN');
  WriteLn('    __STR_IDX PVAR@ 1 - __STR_I PVAR!');
  WriteLn('    __STR_I PVAR@ __STR_CNT PVAR@ + __STR_J PVAR!');
  WriteLn('    BEGIN');
  WriteLn('      __STR_DST PVAR@ __STR_J PVAR@ 4 * + PVAR@ DUP __STR_DST PVAR@ __STR_I PVAR@ 4 * + PVAR!');
  WriteLn('      0= IF');
  WriteLn('        1');
  WriteLn('      ELSE');
  WriteLn('        __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('        __STR_J PVAR@ 1 + __STR_J PVAR!');
  WriteLn('        0');
  WriteLn('      THEN');
  WriteLn('    UNTIL');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitStringInsert;
begin
  WriteLn(': __STRINSERT');
  WriteLn('  __STR_SRC PVAR@ __STR_A PVAR!');
  WriteLn('  __STR_DST PVAR@ __STR_B PVAR!');
  WriteLn('  __STR_A PVAR@ __STR_SRC PVAR!');
  WriteLn('  __STRLEN __STR_LEN PVAR!');
  WriteLn('  __STR_IDX PVAR@ 1 < IF');
  WriteLn('    1 __STR_IDX PVAR!');
  WriteLn('  THEN');
  WriteLn('  __STR_B PVAR@ __STR_SRC PVAR!');
  WriteLn('  __STRLEN __STR_J PVAR!');
  WriteLn('  __STR_IDX PVAR@ 1 - __STR_I PVAR!');
  WriteLn('  __STR_I PVAR@ __STR_J PVAR@ > IF');
  WriteLn('    __STR_J PVAR@ __STR_I PVAR!');
  WriteLn('  THEN');
  WriteLn('  __STR_J PVAR@ __STR_K PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __STR_DST PVAR@ __STR_K PVAR@ 4 * + PVAR@ __STR_DST PVAR@ __STR_K PVAR@ __STR_LEN PVAR@ + 4 * + PVAR!');
  WriteLn('    __STR_K PVAR@ __STR_I PVAR@ = IF');
  WriteLn('      1');
  WriteLn('    ELSE');
  WriteLn('      __STR_K PVAR@ 1 - __STR_K PVAR!');
  WriteLn('      0');
  WriteLn('    THEN');
  WriteLn('  UNTIL');
  WriteLn('  0 __STR_K PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __STR_A PVAR@ __STR_K PVAR@ 4 * + PVAR@ DUP 0= IF');
  WriteLn('      DROP');
  WriteLn('      1');
  WriteLn('    ELSE');
  WriteLn('      __STR_DST PVAR@ __STR_I PVAR@ __STR_K PVAR@ + 4 * + PVAR!');
  WriteLn('      __STR_K PVAR@ 1 + __STR_K PVAR!');
  WriteLn('      0');
  WriteLn('    THEN');
  WriteLn('  UNTIL');
  WriteLn(';')
end;

procedure EmitStringEditHelpers;
begin
  EmitStringHelpers();
  WriteLn('CREATE __STR_DST 0 ,');
  WriteLn('CREATE __STR_K 0 ,');
  WriteLn('CREATE __STR_IDX 0 ,');
  WriteLn('CREATE __STR_CNT 0 ,');
  EmitStringCopy();
  EmitStringDelete();
  EmitStringInsert()
end;

procedure ParseStringEditProgram;
begin
  NextToken();
  ExpectStringEditKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectStringEditKind(TOK_IDENT);
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_type) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditKind(TOK_IDENT);
  StrCopy(current_text, string_type_name);
  NextToken();
  ExpectStringEditSymbol('=');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_array) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('[');
  NextToken();
  ExpectStringEditKind(TOK_INT);
  char_array_len := current_value;
  NextToken();
  ExpectStringEditSymbol(']');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_of) = false then
    FailStringEditParse();
  NextToken();
  if StrEqIgnoreCase(current_text, kw_char) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_var) = false then
    FailStringEditParse();
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  StrCopy(current_text, string_var1_name);
  NextToken();
  ExpectStringEditSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  StrCopy(current_text, string_var2_name);
  NextToken();
  ExpectStringEditSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  StrCopy(current_text, string_var3_name);
  NextToken();
  ExpectStringEditSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  StrCopy(current_text, string_var4_name);
  NextToken();
  ExpectStringEditSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  EmitStringEditHelpers();
  EmitStringVarCreate(string_var1_name);
  EmitStringVarCreate(string_var2_name);
  EmitStringVarCreate(string_var3_name);
  EmitStringVarCreate(string_var4_name);

  if StrEqIgnoreCase(current_text, kw_begin) = false then
    FailStringEditParse();
  WriteLn(': MAIN');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  NextToken();
  ExpectAssignSymbol();
  NextToken();
  ExpectStringEditKind(TOK_STR);
  assign_text := string_var1_name;
  EmitStringStore();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  NextToken();
  ExpectAssignSymbol();
  NextToken();
  ExpectStringEditKind(TOK_STR);
  assign_text := string_var2_name;
  EmitStringStore();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  NextToken();
  ExpectAssignSymbol();
  NextToken();
  ExpectStringEditKind(TOK_STR);
  assign_text := string_var4_name;
  EmitStringStore();
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  saved_text := 'Concat';
  if StrEqIgnoreCase(current_text, saved_text) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('(');
  NextToken();
  Write(current_text);
  WriteLn(' __STR_SRC PVAR!');
  NextToken();
  ExpectStringEditSymbol(',');
  Write(string_var3_name);
  WriteLn(' __STR_DST PVAR!');
  WriteLn('__STRCPY');
  Write(string_var1_name);
  WriteLn(' __STR_SRC PVAR!');
  WriteLn('__STRLEN __STR_LEN PVAR!');
  NextToken();
  Write(current_text);
  WriteLn(' __STR_SRC PVAR!');
  Write(string_var3_name);
  WriteLn(' __STR_LEN PVAR@ 4 * + __STR_DST PVAR!');
  WriteLn('__STRCPY');
  NextToken();
  ExpectStringEditSymbol(',');
  NextToken();
  if StrEqIgnoreCase(current_text, string_var3_name) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol(')');
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('(');
  NextToken();
  EmitStringWrite();
  NextToken();
  ExpectStringEditSymbol(')');
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  saved_text := 'Delete';
  if StrEqIgnoreCase(current_text, saved_text) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('(');
  NextToken();
  Write(current_text);
  WriteLn(' __STR_DST PVAR!');
  NextToken();
  ExpectStringEditSymbol(',');
  NextToken();
  ExpectStringEditKind(TOK_INT);
  Write(current_value);
  WriteLn(' __STR_IDX PVAR!');
  NextToken();
  ExpectStringEditSymbol(',');
  NextToken();
  ExpectStringEditKind(TOK_INT);
  Write(current_value);
  WriteLn(' __STR_CNT PVAR!');
  WriteLn('__STRDELETE');
  NextToken();
  ExpectStringEditSymbol(')');
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('(');
  NextToken();
  EmitStringWrite();
  NextToken();
  ExpectStringEditSymbol(')');
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  ExpectStringEditKind(TOK_IDENT);
  saved_text := 'Insert';
  if StrEqIgnoreCase(current_text, saved_text) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('(');
  NextToken();
  Write(current_text);
  WriteLn(' __STR_SRC PVAR!');
  NextToken();
  ExpectStringEditSymbol(',');
  NextToken();
  Write(current_text);
  WriteLn(' __STR_DST PVAR!');
  NextToken();
  ExpectStringEditSymbol(',');
  NextToken();
  ExpectStringEditKind(TOK_INT);
  Write(current_value);
  WriteLn(' __STR_IDX PVAR!');
  WriteLn('__STRINSERT');
  NextToken();
  ExpectStringEditSymbol(')');
  NextToken();
  ExpectStringEditSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailStringEditParse();
  NextToken();
  ExpectStringEditSymbol('(');
  NextToken();
  EmitStringWrite();
  NextToken();
  ExpectStringEditSymbol(')');
  NextToken();
  ExpectStringEditKind(TOK_KW_END);
  NextToken();
  ExpectStringEditSymbol('.');
  WriteLn(';');
  WriteLn('MAIN')
end;
