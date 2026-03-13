procedure FailHexParse;
begin
  WriteLn('ABORT" selfhost hex parse error"')
end;

procedure ExpectHexKind(kind: integer);
begin
  if current_kind <> kind then
    FailHexParse()
end;

procedure ExpectHexSymbol(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailHexParse()
  else if current_text[0] <> ch then
    FailHexParse()
end;

procedure EmitHexStringVarCreate(name: lexeme_buf);
begin
  Write('CREATE ');
  Write(name);
  Write(' 0 , ');
  Write((char_array_len - 1) * 4);
  WriteLn(' ALLOT')
end;

procedure EmitHexHelpers;
begin
  EmitStringHelpers();
  WriteLn('CREATE __HEX_PTR 0 ,');
  WriteLn('CREATE __HEX_LEN 0 ,');
  WriteLn('CREATE __HEX_ACC 0 ,');
  WriteLn('CREATE __HEX_I 0 ,');
  WriteLn('CREATE __HEX_STOP 0 ,');
  WriteLn('CREATE __I2H_VAL 0 ,');
  WriteLn('CREATE __I2H_PTR 0 ,');
  WriteLn('CREATE __I2H_MAX 0 ,');
  WriteLn('CREATE __I2H_FILL 0 ,');
  WriteLn('CREATE __I2H_REQ 0 ,');
  WriteLn('CREATE __I2H_WIDTH 0 ,');
  WriteLn('CREATE __I2H_I 0 ,');
  WriteLn('CREATE __I2H_SRC 0 ,');
  WriteLn(': __HEX_TO_I32');
  WriteLn('  0 __HEX_ACC PVAR!');
  WriteLn('  0 __HEX_I PVAR!');
  WriteLn('  0 __HEX_STOP PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __HEX_STOP PVAR@ 0= __HEX_I PVAR@ __HEX_LEN PVAR@ < AND WHILE');
  WriteLn('      __HEX_PTR PVAR@ __HEX_I PVAR@ 4 * + PVAR@ DUP 0= IF');
  WriteLn('        DROP');
  WriteLn('        1 __HEX_STOP PVAR!');
  WriteLn('      ELSE');
  WriteLn('        DUP 48 >= OVER 57 <= AND IF');
  WriteLn('          48 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!');
  WriteLn('        ELSE');
  WriteLn('          DUP 65 >= OVER 70 <= AND IF');
  WriteLn('            55 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!');
  WriteLn('          ELSE');
  WriteLn('            DUP 97 >= OVER 102 <= AND IF');
  WriteLn('              87 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!');
  WriteLn('            ELSE');
  WriteLn('              DROP');
  WriteLn('              1 __HEX_STOP PVAR!');
  WriteLn('            THEN');
  WriteLn('          THEN');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('      __HEX_I PVAR@ 1 + __HEX_I PVAR!');
  WriteLn('  REPEAT');
  WriteLn('  __HEX_ACC PVAR@');
  WriteLn(';');
  WriteLn(': __HEX_DIGIT');
  WriteLn('  DUP 10 < IF');
  WriteLn('    48 +');
  WriteLn('  ELSE');
  WriteLn('    55 +');
  WriteLn('  THEN');
  WriteLn(';');
  WriteLn(': __I32_TO_HEX_STR');
  WriteLn('  __I2H_MAX PVAR@ 0< IF');
  WriteLn('    0 __I2H_MAX PVAR!');
  WriteLn('  THEN');
  WriteLn('  1 __I2H_REQ PVAR!');
  WriteLn('  7 __I2H_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __I2H_I PVAR@ 0 >= WHILE');
  WriteLn('      __I2H_VAL PVAR@ __I2H_I PVAR@ 4 * RSHIFT 15 AND DUP 0= 0= IF');
  WriteLn('        __I2H_I PVAR@ 1 + __I2H_REQ PVAR!');
  WriteLn('        DROP');
  WriteLn('        -1 __I2H_I PVAR!');
  WriteLn('      ELSE');
  WriteLn('        DROP');
  WriteLn('        __I2H_I PVAR@ 1 - __I2H_I PVAR!');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn('  __I2H_FILL PVAR@ IF');
  WriteLn('    __I2H_MAX PVAR@ __I2H_WIDTH PVAR!');
  WriteLn('  ELSE');
  WriteLn('    __I2H_REQ PVAR@ __I2H_MAX PVAR@ < IF');
  WriteLn('      __I2H_REQ PVAR@ __I2H_WIDTH PVAR!');
  WriteLn('    ELSE');
  WriteLn('      __I2H_MAX PVAR@ __I2H_WIDTH PVAR!');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  0 __I2H_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __I2H_I PVAR@ __I2H_WIDTH PVAR@ < WHILE');
  WriteLn('      __I2H_FILL PVAR@ IF');
  WriteLn('        __I2H_WIDTH PVAR@ __I2H_I PVAR@ 1 + - __I2H_SRC PVAR!');
  WriteLn('      ELSE');
  WriteLn('        __I2H_REQ PVAR@ __I2H_WIDTH PVAR@ - __I2H_WIDTH PVAR@ __I2H_I PVAR@ 1 + - + __I2H_SRC PVAR!');
  WriteLn('      THEN');
  WriteLn('      __I2H_SRC PVAR@ 8 >= IF');
  WriteLn('        48');
  WriteLn('      ELSE');
  WriteLn('        __I2H_VAL PVAR@ __I2H_SRC PVAR@ 4 * RSHIFT 15 AND __HEX_DIGIT');
  WriteLn('      THEN');
  WriteLn('      __I2H_PTR PVAR@ __I2H_I PVAR@ 4 * + PVAR!');
  WriteLn('      __I2H_I PVAR@ 1 + __I2H_I PVAR!');
  WriteLn('  REPEAT');
  WriteLn('  0 __I2H_PTR PVAR@ __I2H_WIDTH PVAR@ 4 * + PVAR!');
  WriteLn(';')
end;

procedure ParseHexProgram;
begin
  NextToken();
  ExpectHexKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectHexKind(TOK_IDENT);
  NextToken();
  ExpectHexSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_type) = false then
    FailHexParse();
  NextToken();
  ExpectHexKind(TOK_IDENT);
  StrCopy(current_text, string_type_name);
  NextToken();
  ExpectHexSymbol('=');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_array) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol('[');
  NextToken();
  ExpectHexKind(TOK_INT);
  char_array_len := current_value;
  NextToken();
  ExpectHexSymbol(']');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_of) = false then
    FailHexParse();
  NextToken();
  if StrEqIgnoreCase(current_text, kw_char) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_var) = false then
    FailHexParse();
  NextToken();
  ExpectHexKind(TOK_IDENT);
  StrCopy(current_text, string_var1_name);
  NextToken();
  ExpectHexSymbol(':');
  NextToken();
  if StrEqIgnoreCase(current_text, string_type_name) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol(';');
  NextToken();

  EmitHexHelpers();
  EmitHexStringVarCreate(string_var1_name);

  if StrEqIgnoreCase(current_text, kw_begin) = false then
    FailHexParse();
  WriteLn(': MAIN');
  NextToken();

  ExpectHexKind(TOK_IDENT);
  saved_text := 'IntToHex';
  if StrEqIgnoreCase(current_text, saved_text) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol('(');
  NextToken();
  ExpectHexKind(TOK_INT);
  Write(current_value);
  WriteLn(' __I2H_VAL PVAR!');
  NextToken();
  ExpectHexSymbol(',');
  NextToken();
  Write(current_text);
  WriteLn(' __I2H_PTR PVAR!');
  NextToken();
  ExpectHexSymbol(',');
  NextToken();
  ExpectHexKind(TOK_INT);
  Write(current_value);
  WriteLn(' __I2H_MAX PVAR!');
  NextToken();
  ExpectHexSymbol(',');
  NextToken();
  ExpectHexKind(TOK_IDENT);
  saved_text := 'true';
  if StrEqIgnoreCase(current_text, saved_text) then
    WriteLn('1 __I2H_FILL PVAR!')
  else
    WriteLn('0 __I2H_FILL PVAR!');
  WriteLn('__I32_TO_HEX_STR');
  NextToken();
  ExpectHexSymbol(')');
  NextToken();
  ExpectHexSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol('(');
  NextToken();
  EmitStringWrite();
  NextToken();
  ExpectHexSymbol(')');
  NextToken();
  ExpectHexSymbol(';');
  NextToken();

  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol('(');
  NextToken();
  ExpectHexKind(TOK_IDENT);
  saved_text := 'HexToInt';
  if StrEqIgnoreCase(current_text, saved_text) = false then
    FailHexParse();
  NextToken();
  ExpectHexSymbol('(');
  NextToken();
  Write(current_text);
  Write(' __HEX_PTR PVAR! ');
  Write(char_array_len);
  WriteLn(' __HEX_LEN PVAR! __HEX_TO_I32 PWRITE-I32');
  NextToken();
  ExpectHexSymbol(')');
  NextToken();
  ExpectHexSymbol(')');
  WriteLn('  PWRITELN');
  NextToken();
  ExpectHexKind(TOK_KW_END);
  NextToken();
  ExpectHexSymbol('.');
  WriteLn(';');
  WriteLn('MAIN')
end;
