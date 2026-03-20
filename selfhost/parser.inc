procedure FailParse;
begin
  WriteLn('PERR')
end;

procedure ExpectKind(kind: integer);
begin
  if current_kind <> kind then
    FailParse()
end;

procedure ExpectSymbolChar(ch: char);
begin
  if current_kind <> TOK_SYMBOL then
    FailParse()
  else if current_text[0] <> ch then
    FailParse()
end;

procedure ExpectAssignSymbol;
begin
  if current_kind <> TOK_SYMBOL then
    FailParse()
  else if current_text[0] <> ':' then
    FailParse()
  else if current_text[1] <> '=' then
    FailParse()
end;

function ResolveFieldOffset(var name: lexeme_buf): integer;
begin
  if variant_active <> 0 then
    begin
      if StrEqIgnoreCase(variant_tag_name, name) then
        ResolveFieldOffset := 0
      else if StrEqIgnoreCase(variant_arm0_name, name) then
        ResolveFieldOffset := 4
      else if StrEqIgnoreCase(variant_arm1_name, name) then
        ResolveFieldOffset := 4
      else if StrEqIgnoreCase(variant_arm2_name, name) then
        ResolveFieldOffset := 8
      else
        ResolveFieldOffset := -1
    end
  else if StrEqIgnoreCase(field1_name, name) then
    ResolveFieldOffset := 0
  else if StrEqIgnoreCase(field2_name, name) then
    ResolveFieldOffset := 4
  else
    ResolveFieldOffset := -1
end;

function ResolveVariantExpectedTag(var name: lexeme_buf): integer;
begin
  if variant_active = 0 then
    ResolveVariantExpectedTag := -1
  else if StrEqIgnoreCase(variant_arm0_name, name) then
    ResolveVariantExpectedTag := 0
  else if StrEqIgnoreCase(variant_arm1_name, name) then
    ResolveVariantExpectedTag := 1
  else if StrEqIgnoreCase(variant_arm2_name, name) then
    ResolveVariantExpectedTag := 1
  else
    ResolveVariantExpectedTag := -1
end;

procedure EmitVariantTagCheck(expected_tag: integer; var base_name: lexeme_buf);
begin
  if expected_tag >= 0 then
    begin
      Write(base_name);
      WriteLn(' PVAR@ __VAR_TAG PVAR!');
      Write('__VAR_TAG PVAR@ ');
      Write(expected_tag);
      WriteLn(' = 0= IF __VARIANT_MISMATCH THEN')
    end;
end;

function HasName(var name: lexeme_buf): boolean;
begin
  if name[0] = #0 then
    HasName := false
  else
    HasName := true
end;

function HasRecordVarName: boolean;
begin
  HasRecordVarName := record_var_name[0] <> #0
end;

function IsSavedRecordVarName: boolean;
begin
  IsSavedRecordVarName := false;
  if record_var_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(record_var_name, saved_text) then
        IsSavedRecordVarName := true
    end
end;


function HasEnumVarName: boolean;
begin
  HasEnumVarName := enum_var_name[0] <> #0
end;

function HasSubrangeVarName: boolean;
begin
  HasSubrangeVarName := subrange_var_name[0] <> #0
end;

function HasRealVarName: boolean;
begin
  HasRealVarName := real_var_name[0] <> #0
end;

function HasEnumTypeName: boolean;
begin
  HasEnumTypeName := enum_type_name[0] <> #0
end;

function HasSetTypeName: boolean;
begin
  HasSetTypeName := set_type_name[0] <> #0
end;

function HasSubrangeTypeName: boolean;
begin
  HasSubrangeTypeName := subrange_type_name[0] <> #0
end;

function HasRecordTypeName: boolean;
begin
  HasRecordTypeName := record_type_name[0] <> #0
end;

function HasStringTypeName: boolean;
begin
  HasStringTypeName := string_type_name[0] <> #0
end;

function HasStringType2Name: boolean;
begin
  HasStringType2Name := string_type2_name[0] <> #0
end;

function HasIntArrayTypeName: boolean;
begin
  HasIntArrayTypeName := int_array_type_name[0] <> #0
end;

function HasIntArrayVarName: boolean;
begin
  HasIntArrayVarName := int_array_var_name[0] <> #0
end;

function IsIntArrayVar(var name: lexeme_buf): boolean;
begin
  IsIntArrayVar := false;
  if int_array_var_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(int_array_var_name, name) then
        IsIntArrayVar := true
    end;
end;

function IsPointerVar(var name: lexeme_buf): boolean;
begin
  IsPointerVar := false;
  if pointer_var1_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(pointer_var1_name, name) then
        IsPointerVar := true
    end;
  if pointer_var2_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(pointer_var2_name, name) then
        IsPointerVar := true
    end;
  if pointer_var3_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(pointer_var3_name, name) then
        IsPointerVar := true
    end;
  if pointer_var4_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(pointer_var4_name, name) then
        IsPointerVar := true
    end
end;

function IsStringVar(var name: lexeme_buf): boolean;
begin
  if HasName(string_var1_name) and StrEqIgnoreCase(name, string_var1_name) then
    IsStringVar := true
  else if HasName(string_var2_name) and StrEqIgnoreCase(name, string_var2_name) then
    IsStringVar := true
  else if HasName(string_var3_name) and StrEqIgnoreCase(name, string_var3_name) then
    IsStringVar := true
  else if HasName(string_var4_name) and StrEqIgnoreCase(name, string_var4_name) then
    IsStringVar := true
  else
    IsStringVar := false
end;

function IsSetVar(var name: lexeme_buf): boolean;
begin
  IsSetVar := false;
  if set_var1_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(set_var1_name, name) then
        IsSetVar := true
    end;
  if set_var2_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(set_var2_name, name) then
        IsSetVar := true
    end
end;

function AssignTargetIsSetVar: boolean;
begin
  AssignTargetIsSetVar := false;
  if set_var1_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(set_var1_name, assign_text) then
        AssignTargetIsSetVar := true
    end;
  if set_var2_name[0] <> #0 then
    begin
      if StrEqIgnoreCase(set_var2_name, assign_text) then
        AssignTargetIsSetVar := true
    end
end;

function ResolveEnumOrdinal(var name: lexeme_buf): integer;
begin
  ResolveEnumOrdinal := -1;
  if StrEqIgnoreCase(name, enum_name0) then
    ResolveEnumOrdinal := 0
  else if StrEqIgnoreCase(name, enum_name1) then
    ResolveEnumOrdinal := 1
  else if StrEqIgnoreCase(name, enum_name2) then
    ResolveEnumOrdinal := 2
  else if StrEqIgnoreCase(name, enum_name3) then
    ResolveEnumOrdinal := 3
  else if StrEqIgnoreCase(name, enum_name4) then
    ResolveEnumOrdinal := 4
  else if StrEqIgnoreCase(name, enum_name5) then
    ResolveEnumOrdinal := 5
  else if StrEqIgnoreCase(name, enum_name6) then
    ResolveEnumOrdinal := 6
  else if StrEqIgnoreCase(name, enum_name7) then
    ResolveEnumOrdinal := 7
end;

procedure ResolveCurrentEnumOrdinal;
begin
  set_mask_value := -1;
  if StrEqIgnoreCase(enum_name0, current_text) then
    set_mask_value := 0
  else if StrEqIgnoreCase(enum_name1, current_text) then
    set_mask_value := 1
  else if StrEqIgnoreCase(enum_name2, current_text) then
    set_mask_value := 2
  else if StrEqIgnoreCase(enum_name3, current_text) then
    set_mask_value := 3
  else if StrEqIgnoreCase(enum_name4, current_text) then
    set_mask_value := 4
  else if StrEqIgnoreCase(enum_name5, current_text) then
    set_mask_value := 5
  else if StrEqIgnoreCase(enum_name6, current_text) then
    set_mask_value := 6
  else if StrEqIgnoreCase(enum_name7, current_text) then
    set_mask_value := 7
end;

procedure ResolveSavedEnumOrdinal;
begin
  set_mask_value := -1;
  if StrEqIgnoreCase(enum_name0, saved_text) then
    set_mask_value := 0
  else if StrEqIgnoreCase(enum_name1, saved_text) then
    set_mask_value := 1
  else if StrEqIgnoreCase(enum_name2, saved_text) then
    set_mask_value := 2
  else if StrEqIgnoreCase(enum_name3, saved_text) then
    set_mask_value := 3
  else if StrEqIgnoreCase(enum_name4, saved_text) then
    set_mask_value := 4
  else if StrEqIgnoreCase(enum_name5, saved_text) then
    set_mask_value := 5
  else if StrEqIgnoreCase(enum_name6, saved_text) then
    set_mask_value := 6
  else if StrEqIgnoreCase(enum_name7, saved_text) then
    set_mask_value := 7
end;

function IsExactReadName: boolean;
begin
  IsExactReadName := false;
  if UpCase(current_text[0]) = 'R' then
    if UpCase(current_text[1]) = 'E' then
      if UpCase(current_text[2]) = 'A' then
        if UpCase(current_text[3]) = 'D' then
          if current_text[4] = #0 then
            IsExactReadName := true
end;

function IsExactWriteLnName: boolean;
begin
  IsExactWriteLnName := false;
  if UpCase(current_text[0]) = 'W' then
    if UpCase(current_text[1]) = 'R' then
      if UpCase(current_text[2]) = 'I' then
        if UpCase(current_text[3]) = 'T' then
          if UpCase(current_text[4]) = 'E' then
            if UpCase(current_text[5]) = 'L' then
              if UpCase(current_text[6]) = 'N' then
                if current_text[7] = #0 then
                  IsExactWriteLnName := true
end;

function IsExactWithName: boolean;
begin
  IsExactWithName := false;
  if UpCase(current_text[0]) = 'W' then
    if UpCase(current_text[1]) = 'I' then
      if UpCase(current_text[2]) = 'T' then
        if UpCase(current_text[3]) = 'H' then
          if current_text[4] = #0 then
            IsExactWithName := true
end;

function IsExactConcatName: boolean;
begin
  IsExactConcatName := false;
  if UpCase(current_text[0]) = 'C' then
    if UpCase(current_text[1]) = 'O' then
      if UpCase(current_text[2]) = 'N' then
        if UpCase(current_text[3]) = 'C' then
          if UpCase(current_text[4]) = 'A' then
            if UpCase(current_text[5]) = 'T' then
              if current_text[6] = #0 then
                IsExactConcatName := true
end;

function IsExactDeleteName: boolean;
begin
  IsExactDeleteName := false;
  if UpCase(current_text[0]) = 'D' then
    if UpCase(current_text[1]) = 'E' then
      if UpCase(current_text[2]) = 'L' then
        if UpCase(current_text[3]) = 'E' then
          if UpCase(current_text[4]) = 'T' then
            if UpCase(current_text[5]) = 'E' then
              if current_text[6] = #0 then
                IsExactDeleteName := true
end;

function IsExactInsertName: boolean;
begin
  IsExactInsertName := false;
  if UpCase(current_text[0]) = 'I' then
    if UpCase(current_text[1]) = 'N' then
      if UpCase(current_text[2]) = 'S' then
        if UpCase(current_text[3]) = 'E' then
          if UpCase(current_text[4]) = 'R' then
            if UpCase(current_text[5]) = 'T' then
              if current_text[6] = #0 then
                IsExactInsertName := true
end;

function IsExactIntToHexName: boolean;
begin
  IsExactIntToHexName := false;
  if UpCase(current_text[0]) = 'I' then
    if UpCase(current_text[1]) = 'N' then
      if UpCase(current_text[2]) = 'T' then
        if UpCase(current_text[3]) = 'T' then
          if UpCase(current_text[4]) = 'O' then
            if UpCase(current_text[5]) = 'H' then
              if UpCase(current_text[6]) = 'E' then
                if UpCase(current_text[7]) = 'X' then
                  if current_text[8] = #0 then
                    IsExactIntToHexName := true
end;

function IsExactNewName: boolean;
begin
  IsExactNewName := false;
  if UpCase(current_text[0]) = 'N' then
    if UpCase(current_text[1]) = 'E' then
      if UpCase(current_text[2]) = 'W' then
        if current_text[3] = #0 then
          IsExactNewName := true
end;

function IsExactDisposeName: boolean;
begin
  IsExactDisposeName := false;
  if UpCase(current_text[0]) = 'D' then
    if UpCase(current_text[1]) = 'I' then
      if UpCase(current_text[2]) = 'S' then
        if UpCase(current_text[3]) = 'P' then
          if UpCase(current_text[4]) = 'O' then
            if UpCase(current_text[5]) = 'S' then
              if UpCase(current_text[6]) = 'E' then
                if current_text[7] = #0 then
                  IsExactDisposeName := true
end;

function IsExactSetAddrName: boolean;
begin
  IsExactSetAddrName := false;
  if UpCase(current_text[0]) = 'S' then
    if UpCase(current_text[1]) = 'E' then
      if UpCase(current_text[2]) = 'T' then
        if UpCase(current_text[3]) = 'A' then
          if UpCase(current_text[4]) = 'D' then
            if UpCase(current_text[5]) = 'D' then
              if UpCase(current_text[6]) = 'R' then
                if current_text[7] = #0 then
                  IsExactSetAddrName := true
end;

function IsExactRoundName: boolean;
begin
  IsExactRoundName := false;
  if UpCase(current_text[0]) = 'R' then
    if UpCase(current_text[1]) = 'O' then
      if UpCase(current_text[2]) = 'U' then
        if UpCase(current_text[3]) = 'N' then
          if UpCase(current_text[4]) = 'D' then
            if current_text[5] = #0 then
              IsExactRoundName := true
end;

function IsExactAbsName: boolean;
begin
  IsExactAbsName := false;
  if UpCase(current_text[0]) = 'A' then
    if UpCase(current_text[1]) = 'B' then
      if UpCase(current_text[2]) = 'S' then
        if current_text[3] = #0 then
          IsExactAbsName := true
end;

function IsExactSqrName: boolean;
begin
  IsExactSqrName := false;
  if UpCase(current_text[0]) = 'S' then
    if UpCase(current_text[1]) = 'Q' then
      if UpCase(current_text[2]) = 'R' then
        if current_text[3] = #0 then
          IsExactSqrName := true
end;

function IsExactOddName: boolean;
begin
  IsExactOddName := false;
  if UpCase(current_text[0]) = 'O' then
    if UpCase(current_text[1]) = 'D' then
      if UpCase(current_text[2]) = 'D' then
        if current_text[3] = #0 then
          IsExactOddName := true
end;

function IsExactUpCaseName: boolean;
begin
  IsExactUpCaseName := false;
  if UpCase(current_text[0]) = 'U' then
    if UpCase(current_text[1]) = 'P' then
      if UpCase(current_text[2]) = 'C' then
        if UpCase(current_text[3]) = 'A' then
          if UpCase(current_text[4]) = 'S' then
            if UpCase(current_text[5]) = 'E' then
              if current_text[6] = #0 then
                IsExactUpCaseName := true
end;

function IsExactOrdName: boolean;
begin
  IsExactOrdName := false;
  if UpCase(current_text[0]) = 'O' then
    if UpCase(current_text[1]) = 'R' then
      if UpCase(current_text[2]) = 'D' then
        if current_text[3] = #0 then
          IsExactOrdName := true
end;

function IsExactTruncName: boolean;
begin
  IsExactTruncName := false;
  if UpCase(current_text[0]) = 'T' then
    if UpCase(current_text[1]) = 'R' then
      if UpCase(current_text[2]) = 'U' then
        if UpCase(current_text[3]) = 'N' then
          if UpCase(current_text[4]) = 'C' then
            if current_text[5] = #0 then
              IsExactTruncName := true
end;

function IsExactPosName: boolean;
begin
  IsExactPosName := false;
  if UpCase(current_text[0]) = 'P' then
    if UpCase(current_text[1]) = 'O' then
      if UpCase(current_text[2]) = 'S' then
        if current_text[3] = #0 then
          IsExactPosName := true
end;

function IsExactHexToIntName: boolean;
begin
  IsExactHexToIntName := false;
  if UpCase(current_text[0]) = 'H' then
    if UpCase(current_text[1]) = 'E' then
      if UpCase(current_text[2]) = 'X' then
        if UpCase(current_text[3]) = 'T' then
          if UpCase(current_text[4]) = 'O' then
            if UpCase(current_text[5]) = 'I' then
              if UpCase(current_text[6]) = 'N' then
                if UpCase(current_text[7]) = 'T' then
                  if current_text[8] = #0 then
                    IsExactHexToIntName := true
end;

function EnumBit(index_value: integer): integer;
var
  bit_value: integer;
begin
  bit_value := 1;
  while index_value > 0 do
    begin
      bit_value := bit_value * 2;
      index_value := index_value - 1
    end;
  EnumBit := bit_value
end;

procedure EmitCharLine(ch: char);
begin
  Write('  ');
  Write(Ord(ch));
  WriteLn(' PWRITE-CHAR')
end;

procedure EmitCurrentWord;
begin
  Write(current_text);
  Write(' ')
end;

procedure EmitPVarReadWord;
begin
  Write('PVAR@ ')
end;

procedure EmitCurrentStrSrcWord;
begin
  WriteLn('PVAR@ __STR_SRC PVAR!')
end;

procedure EmitStrLenWord;
begin
  Write('__STRLEN ')
end;

procedure EmitSourceAtWord;
begin
  Write('SourceAt ')
end;

procedure EmitMatchPairWord;
begin
  Write('MatchPair ')
end;

procedure EmitIsStringVarWord;
begin
  Write('IsStringVar ')
end;

procedure EmitIsIntArrayVarWord;
begin
  Write('IsIntArrayVar ')
end;

procedure EmitHasRecordVarNameWord;
begin
  Write('HasRecordVarName ')
end;

procedure EmitStrEqIgnoreCaseWord;
begin
  Write('StrEqIgnoreCase ')
end;

procedure EmitIsSavedRecordVarNameWord;
begin
  Write('IsSavedRecordVarName ')
end;


procedure EmitStringIndexScaleWord;
begin
  Write(' 4 * + ')
end;

procedure EmitAndWord;
begin
  Write(' AND ')
end;

procedure EmitMinusWord;
begin
  Write(' - ')
end;

procedure EmitMulAddWord;
begin
  Write(' * + ')
end;

procedure EmitSavedWord;
begin
  Write(saved_text);
  Write(' ')
end;

procedure EmitIntWord(value: integer);
begin
  Write(value);
  Write(' ')
end;

procedure EmitFieldRead(var base_name: lexeme_buf; offset: integer);
begin
  if offset = 0 then
    begin
      Write(base_name);
      Write(' PVAR@ ')
    end
  else
    begin
      Write(base_name);
      Write(' ');
      Write(offset);
      Write(' PFIELD@ ')
    end
end;

procedure EmitStringStore;
var
  i: integer;
  done: boolean;
begin
  i := 0;
  done := false;
  while done = false do
    begin
      if i >= char_array_len then
        done := true
      else if current_text[i] = #0 then
        begin
          if i = 0 then
            Write('0 ')
          else
            Write('0 ');
          if i = 0 then
            Write(assign_text)
          else
            begin
              Write(assign_text);
              Write(' ');
              Write(i * 4)
            end;
          if i = 0 then
            WriteLn(' PVAR!')
          else
            WriteLn(' PFIELD!');
          done := true
        end
      else
        begin
          Write(Ord(current_text[i]));
          Write(' ');
          if i = 0 then
            Write(assign_text)
          else
            begin
              Write(assign_text);
              Write(' ');
              Write(i * 4)
            end;
          if i = 0 then
            WriteLn(' PVAR!')
          else
            WriteLn(' PFIELD!');
          i := i + 1
        end
    end
end;

procedure EmitStringWriteBody;
begin
  WriteLn('0 __WSTR_STOP PVAR!');
  WriteLn('0 >R');
  WriteLn('BEGIN');
  Write('__WSTR_STOP PVAR@ 0= R@ ');
  EmitIntWord(char_array_len);
  WriteLn(' < AND WHILE');
  Write('  ');
  Write(current_text);
  WriteLn(' R@ 4 * + PVAR@ DUP 0= IF');
  WriteLn('    DROP');
  WriteLn('    1 __WSTR_STOP PVAR!');
  WriteLn('  ELSE');
  WriteLn('    PWRITE-CHAR');
  WriteLn('  THEN');
  WriteLn('  R> 1 + >R');
  WriteLn('REPEAT');
  WriteLn('R> DROP')
end;

procedure EmitStringWrite;
begin
  EmitStringWriteBody();
  WriteLn('PWRITELN')
end;

procedure EmitStringHelpers;
begin
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
  WriteLn(';')
end;

procedure EmitExtendedStringHelpers;
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
  WriteLn('CREATE __STR_DST 0 ,');
  WriteLn('CREATE __STR_K 0 ,');
  WriteLn('CREATE __STR_IDX 0 ,');
  WriteLn('CREATE __STR_CNT 0 ,');
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
  WriteLn(';');
  WriteLn(': __STRDELETE');
  WriteLn('  __STR_CNT PVAR@ 0 <= IF');
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
  WriteLn(';');
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
  WriteLn(';');
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

procedure SkipRoutineBody;
var
  depth: integer;
begin
  if current_kind = 11 then
    begin
      repeat
        NextToken()
      until current_kind = 12
    end;
  if current_kind <> 12 then
    begin
      WriteLn('PERR')
    end;
  depth := 1;
  NextToken();
  while depth > 0 do
    begin
      if current_kind = 12 then
        depth := depth + 1
      else if current_kind = 13 then
        depth := depth - 1;
      NextToken()
    end;
  if current_kind <> TOK_SYMBOL then
    begin
      WriteLn('PERR')
    end
  else
    begin
      if current_text[0] <> ';' then
        begin
          WriteLn('PERR')
        end
    end;
  NextToken()
end;

procedure EmitMiniClearStrRoutine;
begin
  WriteLn('CREATE __CLR_DST 0 ,');
  WriteLn('CREATE __CLR_I 0 ,');
  WriteLn(': ClearStr');
  WriteLn('  __CLR_DST PVAR!');
  WriteLn('  0 __CLR_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __CLR_I PVAR@ 32 < WHILE');
  WriteLn('      0 __CLR_DST PVAR@ __CLR_I PVAR@ 4 * + PVAR!');
  WriteLn('      __CLR_I PVAR@ 1 + __CLR_I PVAR!');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitMiniAppendCharRoutine;
begin
  WriteLn('CREATE __APP_DST 0 ,');
  WriteLn('CREATE __APP_CH 0 ,');
  WriteLn('CREATE __APP_I 0 ,');
  WriteLn(': AppendChar');
  WriteLn('  __APP_CH PVAR!');
  WriteLn('  __APP_DST PVAR!');
  WriteLn('  0 __APP_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __APP_I PVAR@ 32 < WHILE');
  WriteLn('      __APP_DST PVAR@ __APP_I PVAR@ 4 * + PVAR@ 0= IF');
  WriteLn('        __APP_CH PVAR@ __APP_DST PVAR@ __APP_I PVAR@ 4 * + PVAR!');
  WriteLn('        __APP_I PVAR@ 31 < IF');
  WriteLn('          0 __APP_DST PVAR@ __APP_I PVAR@ 1 + 4 * + PVAR!');
  WriteLn('        THEN');
  WriteLn('        32 __APP_I PVAR!');
  WriteLn('      ELSE');
  WriteLn('        __APP_I PVAR@ 1 + __APP_I PVAR!');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitMiniStrCopyRoutine;
begin
  WriteLn('CREATE __CPY_SRC 0 ,');
  WriteLn('CREATE __CPY_DST 0 ,');
  WriteLn('CREATE __CPY_I 0 ,');
  WriteLn('CREATE __CPY_DONE 0 ,');
  WriteLn(': StrCopy');
  WriteLn('  __CPY_DST PVAR!');
  WriteLn('  __CPY_SRC PVAR!');
  WriteLn('  0 __CPY_I PVAR!');
  WriteLn('  0 __CPY_DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __CPY_I PVAR@ 32 < WHILE');
  WriteLn('      __CPY_DONE PVAR@ IF');
  WriteLn('        0 __CPY_DST PVAR@ __CPY_I PVAR@ 4 * + PVAR!');
  WriteLn('      ELSE');
  WriteLn('        __CPY_SRC PVAR@ __CPY_I PVAR@ 4 * + PVAR@ DUP');
  WriteLn('        __CPY_DST PVAR@ __CPY_I PVAR@ 4 * + PVAR!');
  WriteLn('        0= IF 1 __CPY_DONE PVAR! THEN');
  WriteLn('      THEN');
  WriteLn('      __CPY_I PVAR@ 1 + __CPY_I PVAR!');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitMiniStrEqIgnoreCaseRoutine;
begin
  WriteLn('CREATE __SEQ_LHS 0 ,');
  WriteLn('CREATE __SEQ_RHS 0 ,');
  WriteLn('CREATE __SEQ_I 0 ,');
  WriteLn('CREATE __SEQ_OK 0 ,');
  WriteLn(': StrEqIgnoreCase');
  WriteLn('  __SEQ_RHS PVAR!');
  WriteLn('  __SEQ_LHS PVAR!');
  WriteLn('  0 __SEQ_I PVAR!');
  WriteLn('  1 __SEQ_OK PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __SEQ_I PVAR@ 32 < __SEQ_OK PVAR@ AND WHILE');
  WriteLn('      __SEQ_LHS PVAR@ __SEQ_I PVAR@ 4 * + PVAR@ >R');
  WriteLn('      __SEQ_RHS PVAR@ __SEQ_I PVAR@ 4 * + PVAR@ >R');
  WriteLn('      R@ UpCase R> UpCase = 0= IF');
  WriteLn('        0 __SEQ_OK PVAR!');
  WriteLn('      ELSE');
  WriteLn('        R> 0= IF');
  WriteLn('          32 __SEQ_I PVAR!');
  WriteLn('        ELSE');
  WriteLn('          __SEQ_I PVAR@ 1 + __SEQ_I PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn('  __SEQ_OK PVAR@');
  WriteLn(';')
end;

procedure EmitRuntimeIsLetterRoutine;
begin
  WriteLn(': IsLetter DUP 65 < IF DROP 0 ELSE DUP 90 <= IF DROP 1 ELSE DUP 97 < IF DROP 0 ELSE DUP 122 <= IF DROP 1 ELSE 95 = THEN THEN THEN THEN ;')
end;

procedure EmitRuntimeIsDigitRoutine;
begin
  WriteLn(': IsDigit DUP 48 < IF DROP 0 ELSE DUP 57 <= IF DROP 1 ELSE DROP 0 THEN THEN ;')
end;

procedure EmitRuntimeIsIdentCharRoutine;
begin
  WriteLn(': IsIdentChar DUP IsLetter IF DROP 1 ELSE IsDigit THEN ;')
end;

procedure EmitRuntimeIsSpaceRoutine;
begin
  WriteLn(': IsSpace DUP 32 = IF DROP 1 ELSE DUP 10 = IF DROP 1 ELSE DUP 13 = IF DROP 1 ELSE DUP 9 = IF DROP 1 ELSE DROP 0 THEN THEN THEN THEN ;')
end;

procedure EmitRuntimeMatchPairRoutine;
begin
  WriteLn('CREATE __MF 0 ,');
  WriteLn('CREATE __MS 0 ,');
  WriteLn(': MatchPair __MS PVAR! __MF PVAR! source_pos PVAR@ source_len PVAR@ >= IF 0 EXIT THEN source_pos PVAR@ SourceAt __MF PVAR@ <> IF 0 EXIT THEN source_pos PVAR@ 1 + source_len PVAR@ >= IF 0 EXIT THEN source_pos PVAR@ 1 + SourceAt __MS PVAR@ <> IF 0 ELSE 1 THEN ;')
end;

procedure EmitRuntimeSourceAtRoutine;
begin
  WriteLn(': SourceAt');
  WriteLn('  DUP 32768 < IF');
  WriteLn('    source SWAP 4 * + PVAR@');
  WriteLn('  ELSE');
  WriteLn('    DUP 65536 < IF');
  WriteLn('      32768 - 4 * source1 PVAR@ + PVAR@');
  WriteLn('    ELSE');
  WriteLn('      DUP 98304 < IF');
  WriteLn('        65536 - 4 * source2 PVAR@ + PVAR@');
  WriteLn('      ELSE');
  WriteLn('        DUP 131072 < IF');
  WriteLn('          98304 - 4 * source3 PVAR@ + PVAR@');
  WriteLn('        ELSE');
  WriteLn('          131072 - 4 * source4 PVAR@ + PVAR@');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeSetSourceAtRoutine;
begin
  WriteLn(': SetSourceAt');
  WriteLn('  SWAP');
  WriteLn('  DUP 32768 < IF');
  WriteLn('    source SWAP 4 * + PVAR!');
  WriteLn('  ELSE');
  WriteLn('    DUP 65536 < IF');
  WriteLn('      source1 PVAR@ 0= IF');
  WriteLn('        source1 PVAR@ __NEWP PVAR!');
  WriteLn('      THEN');
  WriteLn('      source1 PVAR@ SWAP 32768 - 4 * + PVAR!');
  WriteLn('    ELSE');
  WriteLn('      DUP 98304 < IF');
  WriteLn('        source2 PVAR@ 0= IF');
  WriteLn('          source2 PVAR@ __NEWP PVAR!');
  WriteLn('        THEN');
  WriteLn('        source2 PVAR@ SWAP 65536 - 4 * + PVAR!');
  WriteLn('      ELSE');
  WriteLn('        DUP 131072 < IF');
  WriteLn('          source3 PVAR@ 0= IF');
  WriteLn('            source3 PVAR@ __NEWP PVAR!');
  WriteLn('          THEN');
  WriteLn('          source3 PVAR@ SWAP 98304 - 4 * + PVAR!');
  WriteLn('        ELSE');
  WriteLn('          source4 PVAR@ 0= IF');
  WriteLn('            source4 PVAR@ __NEWP PVAR!');
  WriteLn('          THEN');
  WriteLn('          source4 PVAR@ SWAP 131072 - 4 * + PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeAdvanceCharRoutine;
begin
  WriteLn(': AdvanceChar source_pos PVAR@ source_len PVAR@ < IF source_pos PVAR@ 1 + source_pos PVAR! THEN ;')
end;

procedure EmitRuntimeSkipSpacesRoutine;
begin
  WriteLn('CREATE __SD 0 ,');
  WriteLn(': SkipSpaces 0 __SD PVAR! BEGIN __SD PVAR@ 0= WHILE source_pos PVAR@ source_len PVAR@ >= IF 1 __SD PVAR! ELSE source_pos PVAR@ SourceAt IsSpace IF AdvanceChar ELSE 1 __SD PVAR! THEN THEN REPEAT ;')
end;

procedure EmitRuntimeReadIdentifierRoutine;
begin
  WriteLn('CREATE __RD 0 ,');
  WriteLn('CREATE __RI 0 ,');
  WriteLn(': __RC source_pos PVAR@ SourceAt ;');
  WriteLn(': __RP DUP current_text __RI PVAR@ 4 * + PVAR! __RI PVAR@ 1 + __RI PVAR! ;');
  WriteLn(': ReadIdentifier');
  WriteLn('  0 __RI PVAR! 0 current_text PVAR! 0 __RD PVAR!');
  WriteLn('  BEGIN __RD PVAR@ 0= WHILE source_pos PVAR@ source_len PVAR@ >= IF 1 __RD PVAR! ELSE');
  WriteLn('    __RC DUP IsIdentChar IF __RI PVAR@ 31 < IF __RP ELSE DROP THEN DROP AdvanceChar ELSE DROP 1 __RD PVAR! THEN');
  WriteLn('  THEN REPEAT');
  WriteLn('  0 current_text __RI PVAR@ 4 * + PVAR!');
  WriteLn('  1 current_kind PVAR!');
  WriteLn('  __RI PVAR@ 7 > IF EXIT THEN');
  WriteLn('  current_text ResolveKeywordToken DUP 0<> IF current_kind PVAR! ELSE DROP THEN');
  WriteLn(';')
end;

procedure EmitRuntimeReadStringRoutine;
begin
  WriteLn('CREATE __XD 0 ,');
  WriteLn('CREATE __XI 0 ,');
  WriteLn(': ReadString');
  WriteLn('  0 __XI PVAR! 0 current_text PVAR! 4 current_kind PVAR! 0 current_value PVAR! AdvanceChar 0 __XD PVAR!');
  WriteLn('  BEGIN __XD PVAR@ 0= WHILE');
  WriteLn('    source_pos PVAR@ source_len PVAR@ >= IF 1 __XD PVAR! ELSE');
  WriteLn('      source_pos PVAR@ SourceAt 39 = IF AdvanceChar 1 __XD PVAR! ELSE');
  WriteLn('        __XI PVAR@ 31 < IF source_pos PVAR@ SourceAt current_text __XI PVAR@ 4 * + PVAR! __XI PVAR@ 1 + __XI PVAR! 0 current_text __XI PVAR@ 4 * + PVAR! THEN');
  WriteLn('        AdvanceChar');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitRuntimeReadNumberRoutine;
begin
  WriteLn('CREATE __ND 0 ,');
  WriteLn(': ReadNumber');
  WriteLn('  0 current_value PVAR!');
  WriteLn('  0 __ND PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __ND PVAR@ 0= WHILE');
  WriteLn('      source_pos PVAR@ source_len PVAR@ >= IF');
  WriteLn('        1 __ND PVAR!');
  WriteLn('      ELSE');
  WriteLn('        source_pos PVAR@ SourceAt DUP IsDigit IF');
  WriteLn('          48 - current_value PVAR@ 10 * + current_value PVAR!');
  WriteLn('          AdvanceChar');
  WriteLn('        ELSE');
  WriteLn('          DROP 1 __ND PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn('  2 current_kind PVAR!');
  WriteLn(';')
end;

procedure EmitRuntimeReadSymbolRoutine;
begin
  WriteLn(': __SETSYM1 0 current_text 4 + PVAR! current_text PVAR! ;');
  WriteLn(': __SETSYM2 0 current_text 8 + PVAR! current_text 4 + PVAR! current_text PVAR! ;');
  WriteLn(': ReadSymbol');
  WriteLn('  58 61 MatchPair IF 58 61 __SETSYM2 AdvanceChar AdvanceChar 3 current_kind PVAR! 0 current_value PVAR! EXIT THEN');
  WriteLn('  60 61 MatchPair IF 60 61 __SETSYM2 AdvanceChar AdvanceChar 3 current_kind PVAR! 0 current_value PVAR! EXIT THEN');
  WriteLn('  62 61 MatchPair IF 62 61 __SETSYM2 AdvanceChar AdvanceChar 3 current_kind PVAR! 0 current_value PVAR! EXIT THEN');
  WriteLn('  60 62 MatchPair IF 60 62 __SETSYM2 AdvanceChar AdvanceChar 3 current_kind PVAR! 0 current_value PVAR! EXIT THEN');
  WriteLn('  46 46 MatchPair IF 46 46 __SETSYM2 AdvanceChar AdvanceChar 3 current_kind PVAR! 0 current_value PVAR! EXIT THEN');
  WriteLn('  source_pos PVAR@ SourceAt __SETSYM1 AdvanceChar 3 current_kind PVAR! 0 current_value PVAR!');
  WriteLn(';')
end;

procedure EmitRuntimeNextTokenRoutine;
begin
  WriteLn('CREATE __NC 0 ,');
  WriteLn(': NextToken');
  WriteLn('  SkipSpaces');
  WriteLn('  source_pos PVAR@ source_len PVAR@ >= IF');
  WriteLn('    0 current_text PVAR!');
  WriteLn('    0 current_kind PVAR!');
  WriteLn('    0 current_value PVAR!');
  WriteLn('    EXIT');
  WriteLn('  THEN');
  WriteLn('  source_pos PVAR@ SourceAt __NC PVAR!');
  WriteLn('  __NC PVAR@ 39 = IF');
  WriteLn('    ReadString');
  WriteLn('    EXIT');
  WriteLn('  THEN');
  WriteLn('  __NC PVAR@ IsLetter IF');
  WriteLn('    ReadIdentifier');
  WriteLn('    EXIT');
  WriteLn('  THEN');
  WriteLn('  __NC PVAR@ 95 = IF');
  WriteLn('    ReadIdentifier');
  WriteLn('    EXIT');
  WriteLn('  THEN');
  WriteLn('  __NC PVAR@ IsDigit IF');
  WriteLn('    ReadNumber');
  WriteLn('  ELSE');
  WriteLn('    ReadSymbol');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeWriteTokenRoutine;
begin
  WriteLn(': WriteToken');
  WriteLn('  current_kind PVAR@ 1 = IF S" IDENT " PWRITE-STR current_text PWRITE-STR PWRITELN EXIT THEN');
  WriteLn('  current_kind PVAR@ 2 = IF S" INT " PWRITE-STR current_value PVAR@ PWRITE-I32 PWRITELN EXIT THEN');
  WriteLn('  current_kind PVAR@ 3 = IF S" SYM " PWRITE-STR current_text PWRITE-STR PWRITELN EXIT THEN');
  WriteLn('  current_kind PVAR@ 4 = IF S" STR " PWRITE-STR current_text PWRITE-STR PWRITELN EXIT THEN');
  WriteLn('  S" EOF" PWRITE-STR PWRITELN');
  WriteLn(';')
end;

procedure EmitRuntimeExpectKindRoutine;
begin
  WriteLn(': ExpectKind current_kind PVAR@ <> IF FailParse THEN ;')
end;

procedure EmitRuntimeExpectAssignSymbolRoutine;
begin
  WriteLn(': ExpectAssignSymbol current_kind PVAR@ 3 <> IF FailParse EXIT THEN current_text 0 4 * + PVAR@ 58 <> IF FailParse EXIT THEN current_text 1 4 * + PVAR@ 61 <> IF FailParse THEN ;')
end;

procedure EmitRuntimeExpectSymbolCharRoutine;
begin
  WriteLn(': ExpectSymbolChar current_kind PVAR@ 3 <> IF FailParse EXIT THEN current_text 0 4 * + PVAR@ <> IF FailParse THEN ;')
end;

procedure EmitRuntimeHasNameRoutine;
begin
  WriteLn(': HasName 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasRecordVarNameRoutine;
begin
  WriteLn(': HasRecordVarName record_var_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeIsSavedRecordVarNameRoutine;
begin
  WriteLn(': IsSavedRecordVarName');
  WriteLn('  record_var_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    record_var_name saved_text StrEqIgnoreCase');
  WriteLn('  ELSE');
  WriteLn('    0');
  WriteLn('  THEN');
  WriteLn(';');
end;


procedure EmitRuntimeHasEnumVarNameRoutine;
begin
  WriteLn(': HasEnumVarName enum_var_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasSubrangeVarNameRoutine;
begin
  WriteLn(': HasSubrangeVarName subrange_var_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasRealVarNameRoutine;
begin
  WriteLn(': HasRealVarName real_var_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasEnumTypeNameRoutine;
begin
  WriteLn(': HasEnumTypeName enum_type_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasSetTypeNameRoutine;
begin
  WriteLn(': HasSetTypeName set_type_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasSubrangeTypeNameRoutine;
begin
  WriteLn(': HasSubrangeTypeName subrange_type_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasRecordTypeNameRoutine;
begin
  WriteLn(': HasRecordTypeName record_type_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasStringTypeNameRoutine;
begin
  WriteLn(': HasStringTypeName string_type_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasStringType2NameRoutine;
begin
  WriteLn(': HasStringType2Name string_type2_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasIntArrayTypeNameRoutine;
begin
  WriteLn(': HasIntArrayTypeName int_array_type_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeHasIntArrayVarNameRoutine;
begin
  WriteLn(': HasIntArrayVarName int_array_var_name 0 4 * + PVAR@ 0<> ;')
end;

procedure EmitRuntimeIsIntArrayVarRoutine;
begin
  WriteLn(': IsIntArrayVar');
  WriteLn('  int_array_var_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    DUP int_array_var_name StrEqIgnoreCase IF');
  WriteLn('      DROP 1');
  WriteLn('    ELSE');
  WriteLn('      DROP 0');
  WriteLn('    THEN');
  WriteLn('  ELSE');
  WriteLn('    DROP 0');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeIsPointerVarRoutine;
begin
  WriteLn(': IsPointerVar');
  WriteLn('  0');
  WriteLn('  pointer_var1_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    DUP pointer_var1_name StrEqIgnoreCase IF');
  WriteLn('      DROP 1');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  DUP 0= IF');
  WriteLn('    pointer_var2_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('      DUP pointer_var2_name StrEqIgnoreCase IF');
  WriteLn('        DROP 1');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  DUP 0= IF');
  WriteLn('    pointer_var3_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('      DUP pointer_var3_name StrEqIgnoreCase IF');
  WriteLn('        DROP 1');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  DUP 0= IF');
  WriteLn('    pointer_var4_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('      DUP pointer_var4_name StrEqIgnoreCase IF');
  WriteLn('        DROP 1');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeIsStringVarRoutine;
begin
  WriteLn(': IsStringVar');
  WriteLn('  DUP string_var1_name HasName IF');
  WriteLn('    DUP string_var1_name StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  DUP string_var2_name HasName IF');
  WriteLn('    DUP string_var2_name StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  DUP string_var3_name HasName IF');
  WriteLn('    DUP string_var3_name StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  DUP string_var4_name HasName IF');
  WriteLn('    DUP string_var4_name StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  DROP 0');
  WriteLn(';')
end;

procedure EmitRuntimeIsSetVarRoutine;
begin
  WriteLn(': IsSetVar');
  WriteLn('  set_var1_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    DUP set_var1_name StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  set_var2_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    DUP set_var2_name StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  DROP 0');
  WriteLn(';')
end;

procedure EmitRuntimeAssignTargetIsSetVarRoutine;
begin
  WriteLn(': AssignTargetIsSetVar');
  WriteLn('  set_var1_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    assign_text set_var1_name StrEqIgnoreCase IF 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  set_var2_name 0 4 * + PVAR@ 0<> IF');
  WriteLn('    assign_text set_var2_name StrEqIgnoreCase IF 1 EXIT THEN');
  WriteLn('  THEN');
  WriteLn('  0');
  WriteLn(';')
end;

procedure EmitRuntimeResolveEnumOrdinalRoutine;
begin
  WriteLn(': ResolveEnumOrdinal');
  WriteLn('  DUP enum_name0 StrEqIgnoreCase IF DROP 0 EXIT THEN');
  WriteLn('  DUP enum_name1 StrEqIgnoreCase IF DROP 1 EXIT THEN');
  WriteLn('  DUP enum_name2 StrEqIgnoreCase IF DROP 2 EXIT THEN');
  WriteLn('  DUP enum_name3 StrEqIgnoreCase IF DROP 3 EXIT THEN');
  WriteLn('  DUP enum_name4 StrEqIgnoreCase IF DROP 4 EXIT THEN');
  WriteLn('  DUP enum_name5 StrEqIgnoreCase IF DROP 5 EXIT THEN');
  WriteLn('  DUP enum_name6 StrEqIgnoreCase IF DROP 6 EXIT THEN');
  WriteLn('  DUP enum_name7 StrEqIgnoreCase IF DROP 7 EXIT THEN');
  WriteLn('  DROP -1');
  WriteLn(';')
end;

procedure EmitRuntimeResolveKeywordTokenRoutine;
begin
  WriteLn(': ResolveKeywordToken');
  WriteLn('  DUP kw_var StrEqIgnoreCase IF DROP 11 EXIT THEN');
  WriteLn('  DUP kw_end StrEqIgnoreCase IF DROP 13 EXIT THEN');
  WriteLn('  DUP kw_begin StrEqIgnoreCase IF DROP 12 EXIT THEN');
  WriteLn('  DUP kw_program StrEqIgnoreCase IF DROP 10 EXIT THEN');
  WriteLn('  DUP kw_integer StrEqIgnoreCase IF DROP 14 EXIT THEN');
  WriteLn('  DROP 0');
  WriteLn(';')
end;

procedure EmitRuntimeResolveCurrentEnumOrdinalRoutine;
begin
  WriteLn(': ResolveCurrentEnumOrdinal');
  WriteLn('  current_text ResolveEnumOrdinal set_mask_value PVAR!');
  WriteLn(';')
end;

procedure EmitRuntimeResolveSavedEnumOrdinalRoutine;
begin
  WriteLn(': ResolveSavedEnumOrdinal');
  WriteLn('  saved_text ResolveEnumOrdinal set_mask_value PVAR!');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactReadNameRoutine;
begin
  WriteLn(': IsExactReadName');
  WriteLn('  current_text S" Read" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactWriteLnNameRoutine;
begin
  WriteLn(': IsExactWriteLnName');
  WriteLn('  current_text S" WriteLn" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactWithNameRoutine;
begin
  WriteLn(': IsExactWithName');
  WriteLn('  current_text S" with" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactConcatNameRoutine;
begin
  WriteLn(': IsExactConcatName');
  WriteLn('  current_text S" Concat" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactDeleteNameRoutine;
begin
  WriteLn(': IsExactDeleteName');
  WriteLn('  current_text S" Delete" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactInsertNameRoutine;
begin
  WriteLn(': IsExactInsertName');
  WriteLn('  current_text S" Insert" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactIntToHexNameRoutine;
begin
  WriteLn(': IsExactIntToHexName');
  WriteLn('  current_text S" IntToHex" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactNewNameRoutine;
begin
  WriteLn(': IsExactNewName');
  WriteLn('  current_text S" New" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactDisposeNameRoutine;
begin
  WriteLn(': IsExactDisposeName');
  WriteLn('  current_text S" Dispose" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactSetAddrNameRoutine;
begin
  WriteLn(': IsExactSetAddrName');
  WriteLn('  current_text S" SetAddr" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactRoundNameRoutine;
begin
  WriteLn(': IsExactRoundName');
  WriteLn('  current_text S" Round" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactAbsNameRoutine;
begin
  WriteLn(': IsExactAbsName');
  WriteLn('  current_text S" Abs" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactSqrNameRoutine;
begin
  WriteLn(': IsExactSqrName');
  WriteLn('  current_text S" Sqr" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactOddNameRoutine;
begin
  WriteLn(': IsExactOddName');
  WriteLn('  current_text S" Odd" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactUpCaseNameRoutine;
begin
  WriteLn(': IsExactUpCaseName');
  WriteLn('  current_text S" UpCase" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactOrdNameRoutine;
begin
  WriteLn(': IsExactOrdName');
  WriteLn('  current_text S" Ord" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactTruncNameRoutine;
begin
  WriteLn(': IsExactTruncName');
  WriteLn('  current_text S" Trunc" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactPosNameRoutine;
begin
  WriteLn(': IsExactPosName');
  WriteLn('  current_text S" Pos" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeIsExactHexToIntNameRoutine;
begin
  WriteLn(': IsExactHexToIntName');
  WriteLn('  current_text S" HexToInt" StrEqIgnoreCase');
  WriteLn(';')
end;

procedure EmitRuntimeEnumBitRoutine;
begin
  WriteLn(': EnumBit');
  WriteLn('  1 SWAP LSHIFT');
  WriteLn(';')
end;

procedure EmitRuntimeArrayStrideRoutine;
begin
  WriteLn(': ArrayStride');
  WriteLn('  DUP 4 = IF');
  WriteLn('    DROP 1 EXIT');
  WriteLn('  THEN');
  WriteLn('  1');
  WriteLn('  OVER array_dim_count PVAR@ < IF');
  WriteLn('    OVER 1 = IF');
  WriteLn('      array_hi2 PVAR@ array_lo2 PVAR@ - 1 +');
  WriteLn('    ELSE');
  WriteLn('      OVER 2 = IF');
  WriteLn('        array_hi3 PVAR@ array_lo3 PVAR@ - 1 +');
  WriteLn('      ELSE');
  WriteLn('        OVER 3 = IF');
  WriteLn('          array_hi4 PVAR@ array_lo4 PVAR@ - 1 +');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('    OVER 1 + array_dim_count PVAR@ < IF');
  WriteLn('      OVER 1 <= IF');
  WriteLn('        array_hi3 PVAR@ array_lo3 PVAR@ - 1 + *');
  WriteLn('      THEN');
  WriteLn('      OVER 2 <= IF');
  WriteLn('        array_hi4 PVAR@ array_lo4 PVAR@ - 1 + *');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn('  SWAP DROP');
  WriteLn(';')
end;

procedure EmitRuntimeArrayLowerBoundRoutine;
begin
  WriteLn(': ArrayLowerBound');
  WriteLn('  DUP 1 = IF');
  WriteLn('    DROP array_lo1 PVAR@ EXIT');
  WriteLn('  THEN');
  WriteLn('  DUP 2 = IF');
  WriteLn('    DROP array_lo2 PVAR@ EXIT');
  WriteLn('  THEN');
  WriteLn('  DUP 3 = IF');
  WriteLn('    DROP array_lo3 PVAR@ EXIT');
  WriteLn('  THEN');
  WriteLn('  DROP array_lo4 PVAR@');
  WriteLn(';')
end;

procedure EmitRuntimeParseRealLiteralRoutine;
begin
  WriteLn(': ParseRealLiteral');
  WriteLn('  TOK_INT ExpectKind');
  WriteLn('  current_value PVAR@ PWRITE-I32');
  WriteLn('  S"  S>F " PWRITE-STR');
  WriteLn('  NextToken');
  WriteLn('  46 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn('  TOK_INT ExpectKind');
  WriteLn('  current_value PVAR@ 0<> IF');
  WriteLn('    FailParse');
  WriteLn('  THEN');
  WriteLn('  NextToken');
  WriteLn(';')
end;

procedure EmitRuntimeParseRealExprRoutine;
begin
  WriteLn(': ParseRealExpr');
  WriteLn('  ParseRealLiteral');
  WriteLn('  current_kind PVAR@ TOK_SYMBOL = IF');
  WriteLn('    current_text 0 4 * + PVAR@ 47 = IF');
  WriteLn('      NextToken');
  WriteLn('      ParseRealLiteral');
  WriteLn('      S"  FDIV" PWRITE-STR');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeParseSetLiteralRoutine;
begin
  WriteLn(': ParseSetLiteral');
  WriteLn('  0 __SET_MASK PVAR!');
  WriteLn('  91 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn('  0 __DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __DONE PVAR@ 0= WHILE');
  WriteLn('      TOK_IDENT ExpectKind');
  WriteLn('      ResolveCurrentEnumOrdinal');
  WriteLn('      set_mask_value PVAR@ 0< IF');
  WriteLn('        FailParse');
  WriteLn('      THEN');
  WriteLn('      __SET_MASK PVAR@ set_mask_value PVAR@ EnumBit + __SET_MASK PVAR!');
  WriteLn('      NextToken');
  WriteLn('      current_kind PVAR@ TOK_SYMBOL = IF');
  WriteLn('        current_text 0 4 * + PVAR@ 44 = IF');
  WriteLn('          NextToken');
  WriteLn('        ELSE');
  WriteLn('          current_text 0 4 * + PVAR@ 93 = IF');
  WriteLn('            1 __DONE PVAR!');
  WriteLn('          ELSE');
  WriteLn('            FailParse');
  WriteLn('          THEN');
  WriteLn('        THEN');
  WriteLn('      ELSE');
  WriteLn('        FailParse');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn('  __SET_MASK PVAR@ set_mask_value PVAR!');
  WriteLn('  93 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn(';')
end;

procedure EmitRuntimeParseConditionRoutine;
begin
  WriteLn(': ParseCondition');
  WriteLn('  ParseSimpleExpr');
  WriteLn('  current_kind PVAR@ TOK_SYMBOL <> IF');
  WriteLn('    FailParse');
  WriteLn('  THEN');
  WriteLn('  current_text 0 4 * + PVAR@ 60 = IF');
  WriteLn('    current_text 1 4 * + PVAR@ 61 = IF');
  WriteLn('      NextToken ParseSimpleExpr S" <= " PWRITE-STR');
  WriteLn('    ELSE');
  WriteLn('      current_text 1 4 * + PVAR@ 62 = IF');
  WriteLn('        NextToken ParseSimpleExpr S" <> " PWRITE-STR');
  WriteLn('      ELSE');
  WriteLn('        current_text 1 4 * + PVAR@ 0= IF');
  WriteLn('          NextToken ParseSimpleExpr S" < " PWRITE-STR');
  WriteLn('        ELSE');
  WriteLn('          FailParse');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  ELSE');
  WriteLn('    current_text 0 4 * + PVAR@ 62 = IF');
  WriteLn('      current_text 1 4 * + PVAR@ 61 = IF');
  WriteLn('        NextToken ParseSimpleExpr S" >= " PWRITE-STR');
  WriteLn('      ELSE');
  WriteLn('        current_text 1 4 * + PVAR@ 0= IF');
  WriteLn('          NextToken ParseSimpleExpr S" > " PWRITE-STR');
  WriteLn('        ELSE');
  WriteLn('          FailParse');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    ELSE');
  WriteLn('      current_text 0 4 * + PVAR@ 61 = IF');
  WriteLn('        NextToken ParseSimpleExpr S" = " PWRITE-STR');
  WriteLn('      ELSE');
  WriteLn('        FailParse');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeParseArrayIndexesRoutine;
begin
  WriteLn('CREATE __PAI_DIM 0 ,');
  WriteLn(': ParseArrayIndexes');
  WriteLn('  DUP PWRITE-STR 32 PWRITE-CHAR');
  WriteLn('  91 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn('  1 __PAI_DIM PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __PAI_DIM PVAR@ array_dim_count PVAR@ <= WHILE');
  WriteLn('      ParseSimpleExpr');
  WriteLn('      __PAI_DIM PVAR@ ArrayLowerBound PWRITE-I32');
  WriteLn('      S"  - " PWRITE-STR');
  WriteLn('      __PAI_DIM PVAR@ ArrayStride 4 * PWRITE-I32');
  WriteLn('      S"  * + " PWRITE-STR');
  WriteLn('      __PAI_DIM PVAR@ array_dim_count PVAR@ < IF');
  WriteLn('        44 ExpectSymbolChar');
  WriteLn('        NextToken');
  WriteLn('      THEN');
  WriteLn('      __PAI_DIM PVAR@ 1 + __PAI_DIM PVAR!');
  WriteLn('  REPEAT');
  WriteLn('  93 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn('  DROP');
  WriteLn(';')
end;

procedure EmitRuntimeParseTermRoutine;
begin
  WriteLn('CREATE __PT_DONE 0 ,');
  WriteLn(': ParseTerm');
  WriteLn('  ParseFactor');
  WriteLn('  0 __PT_DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __PT_DONE PVAR@ 0= WHILE');
  WriteLn('      current_kind PVAR@ TOK_SYMBOL = IF');
  WriteLn('        current_text 0 4 * + PVAR@ 42 = IF');
  WriteLn('          NextToken ParseFactor S" * " PWRITE-STR');
  WriteLn('        ELSE');
  WriteLn('          current_text 0 4 * + PVAR@ 47 = IF');
  WriteLn('            NextToken ParseFactor S" / " PWRITE-STR');
  WriteLn('          ELSE');
  WriteLn('            1 __PT_DONE PVAR!');
  WriteLn('          THEN');
  WriteLn('        THEN');
  WriteLn('      ELSE');
  WriteLn('        current_kind PVAR@ TOK_IDENT = IF');
  WriteLn('          current_text kw_div StrEqIgnoreCase IF');
  WriteLn('            NextToken ParseFactor S" / " PWRITE-STR');
  WriteLn('          ELSE');
  WriteLn('            current_text kw_mod StrEqIgnoreCase IF');
  WriteLn('              NextToken ParseFactor S" MOD " PWRITE-STR');
  WriteLn('            ELSE');
  WriteLn('              1 __PT_DONE PVAR!');
  WriteLn('            THEN');
  WriteLn('          THEN');
  WriteLn('        ELSE');
  WriteLn('          1 __PT_DONE PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitRuntimeParseSimpleExprRoutine;
begin
  WriteLn('CREATE __PSE_DONE 0 ,');
  WriteLn(': ParseSimpleExpr');
  WriteLn('  ParseTerm');
  WriteLn('  0 __PSE_DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __PSE_DONE PVAR@ 0= WHILE');
  WriteLn('      current_kind PVAR@ TOK_SYMBOL = IF');
  WriteLn('        current_text 0 4 * + PVAR@ 43 = IF');
  WriteLn('          NextToken ParseTerm S" + " PWRITE-STR');
  WriteLn('        ELSE');
  WriteLn('          current_text 0 4 * + PVAR@ 45 = IF');
  WriteLn('            NextToken ParseTerm S" - " PWRITE-STR');
  WriteLn('          ELSE');
  WriteLn('            1 __PSE_DONE PVAR!');
  WriteLn('          THEN');
  WriteLn('        THEN');
  WriteLn('      ELSE');
  WriteLn('        1 __PSE_DONE PVAR!');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitRuntimeParseStringIndexAddressRoutine;
begin
  WriteLn(': ParseStringIndexAddress');
  WriteLn('  DUP PWRITE-STR 32 PWRITE-CHAR');
  WriteLn('  91 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn('  ParseSimpleExpr');
  WriteLn('  S"  4 * + " PWRITE-STR');
  WriteLn('  93 ExpectSymbolChar');
  WriteLn('  NextToken');
  WriteLn('  DROP');
  WriteLn(';')
end;

procedure EmitRuntimeParseFactorLiteralRoutine;
begin
  WriteLn(': ParseFactorLiteral');
  WriteLn('  current_kind PVAR@ TOK_INT = IF');
  WriteLn('    current_value PVAR@ EmitIntWord');
  WriteLn('    NextToken');
  WriteLn('  ELSE');
  WriteLn('    current_kind PVAR@ TOK_STR = IF');
  WriteLn('      current_text 0 4 * + PVAR@ EmitIntWord');
  WriteLn('      NextToken');
  WriteLn('    ELSE');
  WriteLn('      current_kind PVAR@ TOK_SYMBOL = IF');
  WriteLn('        current_text 0 4 * + PVAR@ 35 <> IF');
  WriteLn('          FailParse');
  WriteLn('        THEN');
  WriteLn('        NextToken');
  WriteLn('        TOK_INT ExpectKind');
  WriteLn('        current_value PVAR@ EmitIntWord');
  WriteLn('        NextToken');
  WriteLn('      ELSE');
  WriteLn('        FailParse');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;




procedure EmitRuntimeEmitVariantTagCheckRoutine;
begin
  WriteLn('CREATE __EVTC_TAG 0 ,');
  WriteLn('CREATE __EVTC_BASE 0 ,');
  WriteLn(': EmitVariantTagCheck');
  WriteLn('  __EVTC_BASE PVAR!');
  WriteLn('  __EVTC_TAG PVAR!');
  WriteLn('  __EVTC_TAG PVAR@ 0 >= IF');
  WriteLn('    __EVTC_BASE PVAR@ Write');
  WriteLn('    32 PWRITE-CHAR 80 PWRITE-CHAR 86 PWRITE-CHAR 65 PWRITE-CHAR 82 PWRITE-CHAR 64 PWRITE-CHAR 32 PWRITE-CHAR 95 PWRITE-CHAR 95 PWRITE-CHAR 86 PWRITE-CHAR 65 PWRITE-CHAR 82 PWRITE-CHAR 95 PWRITE-CHAR 84 PWRITE-CHAR 65 PWRITE-CHAR 71 PWRITE-CHAR 32 PWRITE-CHAR 80 PWRITE-CHAR 86 PWRITE-CHAR 65 PWRITE-CHAR 82 PWRITE-CHAR 33 PWRITE-CHAR PWRITELN');
  WriteLn('    95 PWRITE-CHAR 95 PWRITE-CHAR 86 PWRITE-CHAR 65 PWRITE-CHAR 82 PWRITE-CHAR 95 PWRITE-CHAR 84 PWRITE-CHAR 65 PWRITE-CHAR 71 PWRITE-CHAR 32 PWRITE-CHAR 80 PWRITE-CHAR 86 PWRITE-CHAR 65 PWRITE-CHAR 82 PWRITE-CHAR 64 PWRITE-CHAR 32 PWRITE-CHAR');
  WriteLn('    __EVTC_TAG PVAR@ PWRITE-I32');
  WriteLn('    32 PWRITE-CHAR 61 PWRITE-CHAR 32 PWRITE-CHAR 48 PWRITE-CHAR 61 PWRITE-CHAR 32 PWRITE-CHAR 73 PWRITE-CHAR 70 PWRITE-CHAR 32 PWRITE-CHAR 95 PWRITE-CHAR 95 PWRITE-CHAR 86 PWRITE-CHAR 65 PWRITE-CHAR 82 PWRITE-CHAR 73 PWRITE-CHAR 65 PWRITE-CHAR 78 PWRITE-CHAR 84 PWRITE-CHAR 95 PWRITE-CHAR 77 PWRITE-CHAR 73 PWRITE-CHAR 83 PWRITE-CHAR 77 PWRITE-CHAR 65 PWRITE-CHAR 84 PWRITE-CHAR 67 PWRITE-CHAR 72 PWRITE-CHAR 32 PWRITE-CHAR 84 PWRITE-CHAR 72 PWRITE-CHAR 69 PWRITE-CHAR 78 PWRITE-CHAR PWRITELN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitVariantHelpersRoutine;
begin
  WriteLn(': EmitVariantHelpers');
  WriteLn('  variant_active PVAR@ 0<> IF');
  WriteLn('    S" CREATE __VAR_TAG 0 ," PWRITE-STR PWRITELN');
  WriteLn('    S" : __VARIANT_MISMATCH" PWRITE-STR PWRITELN');
  WriteLn('    S"   S"" Variant tag mismatch"" PWRITE-STR" PWRITE-STR PWRITELN');
  WriteLn('    S"   PWRITELN" PWRITE-STR PWRITELN');
  WriteLn('    S"   1 0 / DROP" PWRITE-STR PWRITELN');
  WriteLn('    S" ;" PWRITE-STR PWRITELN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeResolveFieldOffsetRoutine;
begin
  WriteLn(': ResolveFieldOffset');
  WriteLn('  variant_active PVAR@ 0<> IF');
  WriteLn('    DUP variant_tag_name StrEqIgnoreCase IF');
  WriteLn('      DROP 0');
  WriteLn('    ELSE');
  WriteLn('      DUP variant_arm0_name StrEqIgnoreCase IF');
  WriteLn('        DROP 4');
  WriteLn('      ELSE');
  WriteLn('        DUP variant_arm1_name StrEqIgnoreCase IF');
  WriteLn('          DROP 4');
  WriteLn('        ELSE');
  WriteLn('          DUP variant_arm2_name StrEqIgnoreCase IF');
  WriteLn('            DROP 8');
  WriteLn('          ELSE');
  WriteLn('            DROP -1');
  WriteLn('          THEN');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  ELSE');
  WriteLn('    DUP field1_name StrEqIgnoreCase IF');
  WriteLn('      DROP 0');
  WriteLn('    ELSE');
  WriteLn('      DUP field2_name StrEqIgnoreCase IF');
  WriteLn('        DROP 4');
  WriteLn('      ELSE');
  WriteLn('        DROP -1');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeResolveVariantExpectedTagRoutine;
begin
  WriteLn(': ResolveVariantExpectedTag');
  WriteLn('  variant_active PVAR@ 0= IF');
  WriteLn('    DROP -1');
  WriteLn('  ELSE');
  WriteLn('    DUP variant_arm0_name StrEqIgnoreCase IF');
  WriteLn('      DROP 0');
  WriteLn('    ELSE');
  WriteLn('      DUP variant_arm1_name StrEqIgnoreCase IF');
  WriteLn('        DROP 1');
  WriteLn('      ELSE');
  WriteLn('        DUP variant_arm2_name StrEqIgnoreCase IF');
  WriteLn('          DROP 1');
  WriteLn('        ELSE');
  WriteLn('          DROP -1');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('    THEN');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitCurrentWordRoutine;
begin
  WriteLn(': EmitCurrentWord');
  WriteLn('  current_text PWRITE-STR');
  WriteLn('  32 PWRITE-CHAR');
  WriteLn(';')
end;

procedure EmitRuntimeEmitSavedWordRoutine;
begin
  WriteLn(': EmitSavedWord');
  WriteLn('  saved_text PWRITE-STR');
  WriteLn('  32 PWRITE-CHAR');
  WriteLn(';')
end;

procedure EmitRuntimeEmitIntWordRoutine;
begin
  WriteLn(': EmitIntWord');
  WriteLn('  PWRITE-I32');
  WriteLn('  32 PWRITE-CHAR');
  WriteLn(';')
end;

procedure EmitRuntimeEmitCharLineRoutine;
begin
  WriteLn(': EmitCharLine');
  WriteLn('  32 PWRITE-CHAR');
  WriteLn('  Ord PWRITE-I32');
  WriteLn('  S"  PWRITE-CHAR" PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitStringHelpersRoutine;
begin
  WriteLn(': EmitStringHelpers');
  WriteLn('  CREATE __WSTR_STOP 0 ,');
  WriteLn('  CREATE __STR_SRC 0 ,');
  WriteLn('  CREATE __STR_A 0 ,');
  WriteLn('  CREATE __STR_B 0 ,');
  WriteLn('  CREATE __STR_I 0 ,');
  WriteLn('  CREATE __STR_J 0 ,');
  WriteLn('  CREATE __STR_LEN 0 ,');
  WriteLn('  CREATE __STR_POS 0 ,');
  WriteLn('  CREATE __STR_MATCH 0 ,');
  WriteLn('  : __STRLEN');
  WriteLn('    0 __STR_I PVAR!');
  WriteLn('    BEGIN');
  WriteLn('      __STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= IF');
  WriteLn('        1');
  WriteLn('      ELSE');
  WriteLn('        __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('        0');
  WriteLn('      THEN');
  WriteLn('    UNTIL');
  WriteLn('    __STR_I PVAR@');
  WriteLn('  ;');
  WriteLn('  : __STRPOS');
  WriteLn('    __STR_A PVAR@ __STR_SRC PVAR!');
  WriteLn('    __STRLEN __STR_LEN PVAR!');
  WriteLn('    __STR_LEN PVAR@ 0= IF');
  WriteLn('      1');
  WriteLn('    ELSE');
  WriteLn('      0 __STR_POS PVAR!');
  WriteLn('      0 __STR_I PVAR!');
  WriteLn('      BEGIN');
  WriteLn('        __STR_POS PVAR@ 0= __STR_B PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= 0= AND WHILE');
  WriteLn('          0 __STR_J PVAR!');
  WriteLn('          1 __STR_MATCH PVAR!');
  WriteLn('          BEGIN');
  WriteLn('            __STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= 0= AND WHILE');
  WriteLn('              __STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@');
  WriteLn('              __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ = 0= IF');
  WriteLn('                0 __STR_MATCH PVAR!');
  WriteLn('              THEN');
  WriteLn('              __STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@ 0= IF');
  WriteLn('                0 __STR_MATCH PVAR!');
  WriteLn('              THEN');
  WriteLn('              __STR_J PVAR@ 1 + __STR_J PVAR!');
  WriteLn('          REPEAT');
  WriteLn('          __STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= AND IF');
  WriteLn('            __STR_I PVAR@ 1 + __STR_POS PVAR!');
  WriteLn('          THEN');
  WriteLn('          __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('      REPEAT');
  WriteLn('      __STR_POS PVAR@');
  WriteLn('    THEN');
  WriteLn('  ;');
  WriteLn(';')
end;

procedure EmitRuntimeEmitExtendedStringHelpersRoutine;
begin
  WriteLn(': EmitExtendedStringHelpers');
  WriteLn('  EmitStringHelpers');
  WriteLn('  CREATE __HEX_PTR 0 ,');
  WriteLn('  CREATE __HEX_LEN 0 ,');
  WriteLn('  CREATE __HEX_ACC 0 ,');
  WriteLn('  CREATE __HEX_I 0 ,');
  WriteLn('  CREATE __HEX_STOP 0 ,');
  WriteLn('  CREATE __I2H_VAL 0 ,');
  WriteLn('  CREATE __I2H_PTR 0 ,');
  WriteLn('  CREATE __I2H_MAX 0 ,');
  WriteLn('  CREATE __I2H_FILL 0 ,');
  WriteLn('  CREATE __I2H_REQ 0 ,');
  WriteLn('  CREATE __I2H_WIDTH 0 ,');
  WriteLn(';')
end;

procedure EmitRuntimeEmitCurrentStringTextRoutine;
begin
  WriteLn(': EmitCurrentStringText');
  WriteLn('  0 __RID_I PVAR!');
  WriteLn('  0 __DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __DONE PVAR@ 0= WHILE');
  WriteLn('      __RID_I PVAR@ current_text PVAR@ __STR_SRC PVAR!');
  WriteLn('      __STRLEN >= IF');
  WriteLn('        1 __DONE PVAR!');
  WriteLn('      ELSE');
  WriteLn('        __RID_I PVAR@ current_text PVAR@ __STR_AT');
  WriteLn('        DUP 0= IF');
  WriteLn('          DROP 1 __DONE PVAR!');
  WriteLn('        ELSE');
  WriteLn('          EmitCharLine');
  WriteLn('          __RID_I PVAR@ 1 + __RID_I PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitRuntimeEmitStringWriteBodyRoutine;
begin
  WriteLn(': EmitStringWriteBody');
  WriteLn('  0 __WSTR_STOP PVAR!');
  WriteLn('  0 >R');
  WriteLn('  BEGIN');
  WriteLn('    __WSTR_STOP PVAR@ 0= R@ char_array_len PVAR@ < AND WHILE');
  WriteLn('      current_text PVAR@ R@ 4 * + PVAR@ DUP 0= IF');
  WriteLn('        DROP');
  WriteLn('        1 __WSTR_STOP PVAR!');
  WriteLn('      ELSE');
  WriteLn('        PWRITE-CHAR');
  WriteLn('      THEN');
  WriteLn('      R> 1 + >R');
  WriteLn('  REPEAT');
  WriteLn('  R> DROP');
  WriteLn(';')
end;

procedure EmitRuntimeEmitStringWriteRoutine;
begin
  WriteLn(': EmitStringWrite');
  WriteLn('  EmitStringWriteBody');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitFieldReadRoutine;
begin
  WriteLn(': EmitFieldRead');
  WriteLn('  DUP 0= IF');
  WriteLn('    DROP');
  WriteLn('    PVAR@');
  WriteLn('  ELSE');
  WriteLn('    PFIELD@');
  WriteLn('  THEN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitStringStoreRoutine;
begin
  WriteLn(': EmitStringStore');
  WriteLn('  0 __STR_I PVAR!');
  WriteLn('  0 __DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __DONE PVAR@ 0= WHILE');
  WriteLn('      __STR_I PVAR@ char_array_len PVAR@ >= IF');
  WriteLn('        1 __DONE PVAR!');
  WriteLn('      ELSE');
  WriteLn('        __STR_I PVAR@ current_text PVAR@ __STR_AT DUP 0= IF');
  WriteLn('          DROP');
  WriteLn('          0');
  WriteLn('          __STR_I PVAR@ 0= IF');
  WriteLn('            assign_text PVAR@ PVAR!');
  WriteLn('          ELSE');
  WriteLn('            assign_text PVAR@ __STR_I PVAR@ 4 * PFIELD!');
  WriteLn('          THEN');
  WriteLn('          1 __DONE PVAR!');
  WriteLn('        ELSE');
  WriteLn('          __STR_I PVAR@ 0= IF');
  WriteLn('            assign_text PVAR@ PVAR!');
  WriteLn('          ELSE');
  WriteLn('            assign_text PVAR@ __STR_I PVAR@ 4 * PFIELD!');
  WriteLn('          THEN');
  WriteLn('          __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn(';')
end;

procedure EmitRuntimeEmitSavedCaseStringRoutine;
begin
  WriteLn(': EmitSavedCaseString');
  WriteLn('  0 __STR_I PVAR!');
  WriteLn('  0 __DONE PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __DONE PVAR@ 0= WHILE');
  WriteLn('      __STR_I PVAR@ saved_text PVAR@ __STR_SRC PVAR!');
  WriteLn('      __STRLEN >= IF');
  WriteLn('        1 __DONE PVAR!');
  WriteLn('      ELSE');
  WriteLn('        __STR_I PVAR@ saved_text PVAR@ __STR_AT');
  WriteLn('        DUP 0= IF');
  WriteLn('          DROP 1 __DONE PVAR!');
  WriteLn('        ELSE');
  WriteLn('          32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR');
  WriteLn('          PWRITE-CHAR');
  WriteLn('          S"  PWRITE-CHAR" PWRITE-STR');
  WriteLn('          PWRITELN');
  WriteLn('          __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('        THEN');
  WriteLn('      THEN');
  WriteLn('  REPEAT');
  WriteLn('  32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR 32 PWRITE-CHAR');
  WriteLn('  S" PWRITELN" PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitCreateCurrentVarRoutine;
begin
  WriteLn(': EmitCreateCurrentVar');
  WriteLn('  S" CREATE " PWRITE-STR');
  WriteLn('  current_text PWRITE-STR');
  WriteLn('  S"  0 ," PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitCreateCurrentRecordVarRoutine;
begin
  WriteLn(': EmitCreateCurrentRecordVar');
  WriteLn('  S" CREATE " PWRITE-STR');
  WriteLn('  current_text PWRITE-STR');
  WriteLn('  S"  0 , 4 ALLOT" PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure EmitRuntimeEmitConformantArrayProcedureRoutine;
begin
  WriteLn(': EmitConformantArrayProcedure');
  WriteLn('  S" : " PWRITE-STR');
  WriteLn('  proc_name PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn('  0 __STR_I PVAR!');
  WriteLn('  BEGIN');
  WriteLn('    __STR_I PVAR@ array_total_cells PVAR@ < WHILE');
  WriteLn('      __STR_I PVAR@ 0= IF');
  WriteLn('        int_array_var_name PVAR@ PVAR@');
  WriteLn('      ELSE');
  WriteLn('        int_array_var_name PVAR@ __STR_I PVAR@ 4 * PFIELD@ +');
  WriteLn('      THEN');
  WriteLn('      __STR_I PVAR@ 1 + __STR_I PVAR!');
  WriteLn('  REPEAT');
  WriteLn('  PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn('  S" ;" PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure EmitVariantHelpers;
begin
  if variant_active <> 0 then
    begin
      WriteLn('CREATE __VAR_TAG 0 ,');
      WriteLn(': __VARIANT_MISMATCH');
      WriteLn('  S" Variant tag mismatch" PWRITE-STR');
      WriteLn('  PWRITELN');
      WriteLn('  1 0 / DROP');
      WriteLn(';')
    end;
end;

procedure EmitCurrentStringText;
var
  i: integer;
  done: boolean;
  compact: boolean;
begin
  compact := true;
  i := 0;
  done := false;
  while done = false do
    begin
      if i >= Length(current_text) then
        done := true
      else if current_text[i] = #0 then
        done := true
      else if current_text[i] = '"' then
        begin
          compact := false;
          done := true
        end
      else
        i := i + 1
    end;
  if compact then
    begin
      Write('S" ');
      Write(current_text);
      WriteLn('" PWRITE-STR')
    end
  else
    begin
      i := 0;
      done := false;
      while done = false do
        begin
          if i >= Length(current_text) then
            done := true
          else if current_text[i] = #0 then
            done := true
          else
            begin
              EmitCharLine(current_text[i]);
              i := i + 1
            end
        end
    end
end;

procedure EmitSavedCaseString;
var
  i: integer;
  done: boolean;
  compact: boolean;
begin
  compact := true;
  i := 0;
  done := false;
  while done = false do
    begin
      if i >= Length(saved_text) then
        done := true
      else if saved_text[i] = #0 then
        done := true
      else if saved_text[i] = '"' then
        begin
          compact := false;
          done := true
        end
      else
        i := i + 1
    end;
  if compact then
    begin
      Write('      S" ');
      Write(saved_text);
      WriteLn('" PWRITE-STR');
      WriteLn('      PWRITELN')
    end
  else
    begin
      i := 0;
      done := false;
      while done = false do
        begin
          if i >= Length(saved_text) then
            done := true
          else if saved_text[i] = #0 then
            done := true
          else
            begin
              Write('      ');
              Write(Ord(saved_text[i]));
              WriteLn(' PWRITE-CHAR');
              i := i + 1
            end
        end;
      WriteLn('      PWRITELN')
    end
end;

procedure ParseRealLiteral;
begin
  ExpectKind(TOK_INT);
  Write(current_value);
  Write(' S>F ');
  NextToken();
  ExpectSymbolChar('.');
  NextToken();
  ExpectKind(TOK_INT);
  if current_value <> 0 then
    FailParse();
  NextToken()
end;

procedure ParseRealExpr;
begin
  ParseRealLiteral();
  if current_kind = TOK_SYMBOL then
    begin
      if current_text[0] = '/' then
        begin
          NextToken();
          ParseRealLiteral();
          Write(' FDIV')
        end
    end
end;

procedure ParseSetLiteral;
var
  enum_index: integer;
  mask_value: integer;
  done: boolean;
begin
  mask_value := 0;
  ExpectSymbolChar('[');
  NextToken();
  done := false;
  while done = false do
    begin
      ExpectKind(TOK_IDENT);
      ResolveCurrentEnumOrdinal();
      enum_index := set_mask_value;
      if enum_index < 0 then
        FailParse();
      mask_value := mask_value + EnumBit(enum_index);
      NextToken();
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = ',' then
            NextToken()
          else if current_text[0] = ']' then
            done := true
          else
            FailParse()
        end
      else
        FailParse()
    end;
  set_mask_value := mask_value;
  ExpectSymbolChar(']');
  NextToken()
end;

function ArrayStride(dim_index: integer): integer;
var
  span_value: integer;
begin
  if dim_index = 4 then
    ArrayStride := 1
  else
    begin
      span_value := 1;
      if dim_index < array_dim_count then
        begin
          if dim_index = 1 then
            span_value := array_hi2 - array_lo2 + 1
          else if dim_index = 2 then
            span_value := array_hi3 - array_lo3 + 1
          else if dim_index = 3 then
            span_value := array_hi4 - array_lo4 + 1;
          if dim_index + 1 < array_dim_count then
            begin
              if dim_index <= 1 then
                span_value := span_value * (array_hi3 - array_lo3 + 1);
              if dim_index <= 2 then
                span_value := span_value * (array_hi4 - array_lo4 + 1)
            end
        end;
      ArrayStride := span_value
    end
end;

function ArrayLowerBound(dim_index: integer): integer;
begin
  if dim_index = 1 then
    ArrayLowerBound := array_lo1
  else if dim_index = 2 then
    ArrayLowerBound := array_lo2
  else if dim_index = 3 then
    ArrayLowerBound := array_lo3
  else
    ArrayLowerBound := array_lo4
end;

procedure ParseArrayIndexes(var base_name: lexeme_buf);
var
  dim_index: integer;
  lower_bound_value: integer;
  stride_value: integer;
begin
  Write(base_name);
  Write(' ');
  ExpectSymbolChar('[');
  NextToken();
  dim_index := 1;
  while dim_index <= array_dim_count do
    begin
      ParseSimpleExpr();
      if dim_index = 1 then
        lower_bound_value := array_lo1
      else if dim_index = 2 then
        lower_bound_value := array_lo2
      else if dim_index = 3 then
        lower_bound_value := array_lo3
      else
        lower_bound_value := array_lo4;
      Write(lower_bound_value);
      EmitMinusWord();
      if dim_index = 4 then
        stride_value := 1
      else
        begin
          stride_value := 1;
          if dim_index < array_dim_count then
            begin
              if dim_index = 1 then
                stride_value := array_hi2 - array_lo2 + 1
              else if dim_index = 2 then
                stride_value := array_hi3 - array_lo3 + 1
              else if dim_index = 3 then
                stride_value := array_hi4 - array_lo4 + 1;
              if dim_index + 1 < array_dim_count then
                begin
                  if dim_index <= 1 then
                    stride_value := stride_value * (array_hi3 - array_lo3 + 1);
                  if dim_index <= 2 then
                    stride_value := stride_value * (array_hi4 - array_lo4 + 1)
                end
            end
        end;
      Write(stride_value * 4);
      EmitMulAddWord();
      if dim_index < array_dim_count then
        begin
          ExpectSymbolChar(',');
          NextToken()
        end;
      dim_index := dim_index + 1
    end;
  ExpectSymbolChar(']');
  NextToken()
end;

procedure ParseFactorLiteral;
begin
  if current_kind = TOK_INT then
    begin
      EmitIntWord(current_value);
      NextToken()
    end
  else if current_kind = TOK_STR then
    begin
      EmitIntWord(Ord(current_text[0]));
      NextToken()
    end
  else
    begin
      if current_kind <> TOK_SYMBOL then
        FailParse();
      if current_text[0] <> '#' then
        FailParse();
      NextToken();
      ExpectKind(TOK_INT);
      EmitIntWord(current_value);
      NextToken()
    end
end;

procedure ParseFactor;
var
  is_true_name: integer;
  is_false_name: integer;
  is_nil_name: integer;
  is_chr_name: integer;
  is_ord_name: integer;
  is_addr_name: integer;
  is_sourceat_name: integer;
  is_matchpair_name: integer;
  is_isstringvar_name: integer;
  is_isintarrayvar_name: integer;
  is_hasrecordvarname_name: integer;
  is_streqignorecase_name: integer;
  is_issavedrecordvarname_name: integer;
  field_offset: integer;
begin
  if current_kind = 2 then
    begin
      ParseFactorLiteral()
    end
  else if current_kind = 4 then
    begin
      ParseFactorLiteral()
    end
  else if current_kind = 3 then
    begin
      if current_text[0] <> '#' then
        FailParse();
      ParseFactorLiteral()
    end
  else if current_kind = 1 then
    begin
      StrCopy(current_text, saved_text);
      is_true_name := 0;
      if saved_text[0] = 't' then
        begin
          if saved_text[1] = 'r' then
            begin
              if saved_text[2] = 'u' then
                begin
                  if saved_text[3] = 'e' then
                    begin
                      if saved_text[4] = #0 then
                        is_true_name := 1
                    end
                end
            end
        end;
      if is_true_name <> 0 then
        begin
          NextToken();
          current_value := 1;
          EmitCurrentWord()
        end
      else
        begin
          is_false_name := 0;
          if saved_text[0] = 'f' then
            begin
              if saved_text[1] = 'a' then
                begin
                  if saved_text[2] = 'l' then
                    begin
                      if saved_text[3] = 's' then
                        begin
                          if saved_text[4] = 'e' then
                            begin
                              if saved_text[5] = #0 then
                                is_false_name := 1
                            end
                        end
                    end
                end
            end;
          if is_false_name <> 0 then
            begin
              NextToken();
              current_value := 0;
              EmitCurrentWord()
            end
          else
            begin
              is_nil_name := 0;
              if saved_text[0] = 'n' then
                begin
                  if saved_text[1] = 'i' then
                    begin
                      if saved_text[2] = 'l' then
                        begin
                          if saved_text[3] = #0 then
                            is_nil_name := 1
                        end
                    end
                end;
              if is_nil_name <> 0 then
                begin
                  NextToken();
                  current_value := 0;
                  EmitCurrentWord()
                end
              else
                begin
                  is_chr_name := 0;
                  if saved_text[0] = 'C' then
                    begin
                      if saved_text[1] = 'h' then
                        begin
                          if saved_text[2] = 'r' then
                            begin
                              if saved_text[3] = #0 then
                                is_chr_name := 1
                            end
                        end
                    end;
                  if is_chr_name <> 0 then
                    begin
                      NextToken();
                      if current_kind <> TOK_SYMBOL then
                        FailParse();
                      if current_text[0] <> '(' then
                        FailParse();
                      NextToken();
                      ParseSimpleExpr();
                      if current_kind <> TOK_SYMBOL then
                        FailParse();
                      if current_text[0] <> ')' then
                        FailParse();
                      NextToken()
                    end
                  else
                    begin
                      is_ord_name := 0;
                      if saved_text[0] = 'O' then
                        begin
                          if saved_text[1] = 'r' then
                            begin
                              if saved_text[2] = 'd' then
                                begin
                                  if saved_text[3] = #0 then
                                    is_ord_name := 1
                                end
                            end
                        end;
                      if is_ord_name <> 0 then
                        begin
                          NextToken();
                          if current_kind <> TOK_SYMBOL then
                            FailParse();
                          if current_text[0] <> '(' then
                            FailParse();
                          NextToken();
                          ParseSimpleExpr();
                          if current_kind <> TOK_SYMBOL then
                            FailParse();
                          if current_text[0] <> ')' then
                            FailParse();
                          NextToken()
                        end
                      else
                        begin
                          is_addr_name := 0;
                          if saved_text[0] = 'A' then
                            begin
                              if saved_text[1] = 'd' then
                                begin
                                  if saved_text[2] = 'd' then
                                    begin
                                      if saved_text[3] = 'r' then
                                        begin
                                          if saved_text[4] = #0 then
                                            is_addr_name := 1
                                        end
                                    end
                                end
                            end;
                          if is_addr_name <> 0 then
                            begin
                              NextToken();
                              ExpectSymbolChar('(');
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              Write(current_text);
                              Write(' PVAR@ ');
                              NextToken();
                              ExpectSymbolChar('^');
                              NextToken();
                              ExpectSymbolChar(')');
                              NextToken()
                            end
                          else
                            begin
                              builtin_text := 'Length';
                              if StrEqIgnoreCase(saved_text, builtin_text) then
                                begin
                                  NextToken();
                                  ExpectSymbolChar('(');
                                  NextToken();
                              ExpectKind(TOK_IDENT);
                              Write(current_text);
                              WriteLn(' PVAR@ __STR_SRC PVAR!');
                              Write('__STRLEN ');
                              NextToken();
                              ExpectSymbolChar(')');
                                  NextToken()
                                end
                              else
                                begin
                                  is_sourceat_name := 0;
                                  if saved_text[0] = 'S' then
                                    begin
                                      if saved_text[1] = 'o' then
                                        begin
                                          if saved_text[2] = 'u' then
                                            begin
                                              if saved_text[3] = 'r' then
                                                begin
                                                  if saved_text[4] = 'c' then
                                                    begin
                                                      if saved_text[5] = 'e' then
                                                        begin
                                                          if saved_text[6] = 'A' then
                                                            begin
                                                              if saved_text[7] = 't' then
                                                                begin
                                                                  if saved_text[8] = #0 then
                                                                    is_sourceat_name := 1
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end;
                                  if is_sourceat_name <> 0 then
                                    begin
                                      NextToken();
                                      ExpectSymbolChar('(');
                                      NextToken();
                                      ParseSimpleExpr();
                                      ExpectSymbolChar(')');
                                      Write('SourceAt ');
                                      NextToken()
                                    end
                                  else
                                    begin
                                      is_matchpair_name := 0;
                                      if saved_text[0] = 'M' then
                                        begin
                                          if saved_text[1] = 'a' then
                                            begin
                                              if saved_text[2] = 't' then
                                                begin
                                                  if saved_text[3] = 'c' then
                                                    begin
                                                      if saved_text[4] = 'h' then
                                                        begin
                                                          if saved_text[5] = 'P' then
                                                            begin
                                                              if saved_text[6] = 'a' then
                                                                begin
                                                                  if saved_text[7] = 'i' then
                                                                    begin
                                                                      if saved_text[8] = 'r' then
                                                                        begin
                                                                          if saved_text[9] = #0 then
                                                                            is_matchpair_name := 1
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end;
                                      if is_matchpair_name <> 0 then
                                        begin
                                          NextToken();
                                          if current_kind <> TOK_SYMBOL then
                                            FailParse();
                                          if current_text[0] <> '(' then
                                            FailParse();
                                          NextToken();
                                          ParseSimpleExpr();
                                          if current_kind <> TOK_SYMBOL then
                                            FailParse();
                                          if current_text[0] <> ',' then
                                            FailParse();
                                          NextToken();
                                          ParseSimpleExpr();
                                          if current_kind <> TOK_SYMBOL then
                                            FailParse();
                                          if current_text[0] <> ')' then
                                            FailParse();
                                          EmitMatchPairWord();
                                          NextToken()
                                        end
                                      else
                                        begin
                                          is_isstringvar_name := 0;
                                          if saved_text[0] = 'I' then
                                            begin
                                              if saved_text[1] = 's' then
                                                begin
                                                  if saved_text[2] = 'S' then
                                                    begin
                                                      if saved_text[3] = 't' then
                                                        begin
                                                          if saved_text[4] = 'r' then
                                                            begin
                                                              if saved_text[5] = 'i' then
                                                                begin
                                                                  if saved_text[6] = 'n' then
                                                                    begin
                                                                      if saved_text[7] = 'g' then
                                                                        begin
                                                                          if saved_text[8] = 'V' then
                                                                            begin
                                                                              if saved_text[9] = 'a' then
                                                                                begin
                                                                                  if saved_text[10] = 'r' then
                                                                                    begin
                                                                                      if saved_text[11] = #0 then
                                                                                        is_isstringvar_name := 1
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end;
                                          if is_isstringvar_name <> 0 then
                                            begin
                                              NextToken();
                                              if current_kind <> TOK_SYMBOL then
                                                FailParse();
                                              if current_text[0] <> '(' then
                                                FailParse();
                                              NextToken();
                                              ExpectKind(TOK_IDENT);
                                              EmitCurrentWord();
                                              EmitIsStringVarWord();
                                              NextToken();
                                              if current_kind <> TOK_SYMBOL then
                                                FailParse();
                                              if current_text[0] <> ')' then
                                                FailParse();
                                              NextToken()
                                            end
                                          else
                                            begin
                                              is_isintarrayvar_name := 0;
                                              if saved_text[0] = 'I' then
                                                begin
                                                  if saved_text[1] = 's' then
                                                    begin
                                                      if saved_text[2] = 'I' then
                                                        begin
                                                          if saved_text[3] = 'n' then
                                                            begin
                                                              if saved_text[4] = 't' then
                                                                begin
                                                                  if saved_text[5] = 'A' then
                                                                    begin
                                                                      if saved_text[6] = 'r' then
                                                                        begin
                                                                          if saved_text[7] = 'r' then
                                                                            begin
                                                                              if saved_text[8] = 'a' then
                                                                                begin
                                                                                  if saved_text[9] = 'y' then
                                                                                    begin
                                                                                      if saved_text[10] = 'V' then
                                                                                        begin
                                                                                          if saved_text[11] = 'a' then
                                                                                            begin
                                                                                              if saved_text[12] = 'r' then
                                                                                                begin
                                                                                                  if saved_text[13] = #0 then
                                                                                                    is_isintarrayvar_name := 1
                                                                                                end
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end;
                                              if is_isintarrayvar_name <> 0 then
                                                begin
                                                  NextToken();
                                                  if current_kind <> TOK_SYMBOL then
                                                    FailParse();
                                                  if current_text[0] <> '(' then
                                                    FailParse();
                                                  NextToken();
                                                  if current_kind <> 1 then
                                                    FailParse();
                                                  EmitCurrentWord();
                                                  EmitIsIntArrayVarWord();
                                                  NextToken();
                                                  if current_kind <> TOK_SYMBOL then
                                                    FailParse();
                                                  if current_text[0] <> ')' then
                                                    FailParse();
                                                  NextToken()
                                                end
                                              else
                                                begin
                                                  is_hasrecordvarname_name := 0;
                                                  if saved_text[0] = 'H' then
                                                    begin
                                                      if saved_text[1] = 'a' then
                                                        begin
                                                          if saved_text[2] = 's' then
                                                            begin
                                                              if saved_text[3] = 'R' then
                                                                begin
                                                                  if saved_text[4] = 'e' then
                                                                    begin
                                                                      if saved_text[5] = 'c' then
                                                                        begin
                                                                          if saved_text[6] = 'o' then
                                                                            begin
                                                                              if saved_text[7] = 'r' then
                                                                                begin
                                                                                  if saved_text[8] = 'd' then
                                                                                    begin
                                                                                      if saved_text[9] = 'V' then
                                                                                        begin
                                                                                          if saved_text[10] = 'a' then
                                                                                            begin
                                                                                              if saved_text[11] = 'r' then
                                                                                                begin
                                                                                                  if saved_text[12] = 'N' then
                                                                                                    begin
                                                                                                      if saved_text[13] = 'a' then
                                                                                                        begin
                                                                                                          if saved_text[14] = 'm' then
                                                                                                            begin
                                                                                                              if saved_text[15] = 'e' then
                                                                                                                begin
                                                                                                                  if saved_text[16] = #0 then
                                                                                                                    is_hasrecordvarname_name := 1
                                                                                                                end
                                                                                                            end
                                                                                                        end
                                                                                                    end
                                                                                                end
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end;
                                                  if is_hasrecordvarname_name <> 0 then
                                                    begin
                                                      NextToken();
                                                      if current_kind <> TOK_SYMBOL then
                                                        FailParse();
                                                      if current_text[0] <> '(' then
                                                        FailParse();
                                                      NextToken();
                                                  if current_kind <> TOK_SYMBOL then
                                                        FailParse();
                                                      if current_text[0] <> ')' then
                                                        FailParse();
                                                      EmitHasRecordVarNameWord();
                                                      NextToken()
                                                    end
                                                  else
                                                    begin
                                                      is_streqignorecase_name := 0;
                                                      if saved_text[0] = 'S' then
                                                        begin
                                                          if saved_text[1] = 't' then
                                                            begin
                                                              if saved_text[2] = 'r' then
                                                                begin
                                                                  if saved_text[3] = 'E' then
                                                                    begin
                                                                      if saved_text[4] = 'q' then
                                                                        begin
                                                                          if saved_text[5] = 'I' then
                                                                            begin
                                                                              if saved_text[6] = 'g' then
                                                                                begin
                                                                                  if saved_text[7] = 'n' then
                                                                                    begin
                                                                                      if saved_text[8] = 'o' then
                                                                                        begin
                                                                                          if saved_text[9] = 'r' then
                                                                                            begin
                                                                                              if saved_text[10] = 'e' then
                                                                                                begin
                                                                                                  if saved_text[11] = 'C' then
                                                                                                    begin
                                                                                                      if saved_text[12] = 'a' then
                                                                                                        begin
                                                                                                          if saved_text[13] = 's' then
                                                                                                            begin
                                                                                                              if saved_text[14] = 'e' then
                                                                                                                begin
                                                                                                                  if saved_text[15] = #0 then
                                                                                                                    is_streqignorecase_name := 1
                                                                                                                end
                                                                                                            end
                                                                                                        end
                                                                                                    end
                                                                                                end
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end;
                                                  if is_streqignorecase_name <> 0 then
                                                        begin
                                                          NextToken();
                                                          if current_kind <> TOK_SYMBOL then
                                                            FailParse();
                                                          if current_text[0] <> '(' then
                                                            FailParse();
                                                          NextToken();
                                                          if current_kind <> 1 then
                                                            FailParse();
                                                          EmitCurrentWord();
                                                          NextToken();
                                                          if current_kind <> TOK_SYMBOL then
                                                            FailParse();
                                                          if current_text[0] <> ',' then
                                                            FailParse();
                                                          NextToken();
                                                          if current_kind <> 1 then
                                                            FailParse();
                                                          EmitCurrentWord();
                                                          NextToken();
                                                          if current_kind <> TOK_SYMBOL then
                                                            FailParse();
                                                          if current_text[0] <> ')' then
                                                            FailParse();
                                                          EmitStrEqIgnoreCaseWord();
                                                          NextToken()
                                                        end
                                                      else
                                                        begin
                                                          is_issavedrecordvarname_name := 0;
                                                          if saved_text[0] = 'I' then
                                                            begin
                                                              if saved_text[1] = 's' then
                                                                begin
                                                                  if saved_text[2] = 'S' then
                                                                    begin
                                                                      if saved_text[3] = 'a' then
                                                                        begin
                                                                          if saved_text[4] = 'v' then
                                                                            begin
                                                                              if saved_text[5] = 'e' then
                                                                                begin
                                                                                  if saved_text[6] = 'd' then
                                                                                    begin
                                                                                      if saved_text[7] = 'R' then
                                                                                        begin
                                                                                          if saved_text[8] = 'e' then
                                                                                            begin
                                                                                              if saved_text[9] = 'c' then
                                                                                                begin
                                                                                                  if saved_text[10] = 'o' then
                                                                                                    begin
                                                                                                      if saved_text[11] = 'r' then
                                                                                                        begin
                                                                                                          if saved_text[12] = 'd' then
                                                                                                            begin
                                                                                                              if saved_text[13] = 'V' then
                                                                                                                begin
                                                                                                                  if saved_text[14] = 'a' then
                                                                                                                    begin
                                                                                                                      if saved_text[15] = 'r' then
                                                                                                                        begin
                                                                                                                          if saved_text[16] = 'N' then
                                                                                                                            begin
                                                                                                                              if saved_text[17] = 'a' then
                                                                                                                                begin
                                                                                                                                  if saved_text[18] = 'm' then
                                                                                                                                    begin
                                                                                                                                      if saved_text[19] = 'e' then
                                                                                                                                        begin
                                                                                                                                          if saved_text[20] = #0 then
                                                                                                                                            is_issavedrecordvarname_name := 1
                                                                                                                                        end
                                                                                                                                    end
                                                                                                                                end
                                                                                                                            end
                                                                                                                        end
                                                                                                                    end
                                                                                                                end
                                                                                                            end
                                                                                                        end
                                                                                                    end
                                                                                                end
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end;
                                                          if is_issavedrecordvarname_name <> 0 then
                                                            begin
                                                              NextToken();
                                                              if current_kind <> TOK_SYMBOL then
                                                                FailParse();
                                                              if current_text[0] <> '(' then
                                                                FailParse();
                                                              NextToken();
                                                              if current_kind <> TOK_SYMBOL then
                                                                FailParse();
                                                              if current_text[0] <> ')' then
                                                                FailParse();
                                                              EmitIsSavedRecordVarNameWord();
                                                              NextToken()
                                                            end
                                                          else
                                                            begin
                                                              ResolveSavedEnumOrdinal();
                                                              NextToken();
                                                              if set_mask_value >= 0 then
                                                                begin
                                                                  current_value := set_mask_value;
                                                                  EmitCurrentWord()
                                                                end
                          else if IsStringVar(saved_text) then
                            begin
                              if current_kind = TOK_SYMBOL then
                                begin
                                  if current_text[0] = '[' then
                                    begin
                                      ParseStringIndexAddress(saved_text);
                                      EmitPVarReadWord()
                                    end
                                  else
                                    begin
                                      EmitSavedWord();
                                      EmitPVarReadWord()
                                    end
                                end
                              else
                                begin
                                  EmitSavedWord();
                                  EmitPVarReadWord()
                                end
                            end
                          else if IsIntArrayVar(saved_text) then
                            begin
                              if current_kind = TOK_SYMBOL then
                                begin
                                  if current_text[0] = '[' then
                                    begin
                                      ParseArrayIndexes(saved_text);
                                      EmitPVarReadWord()
                                    end
                                  else
                                    begin
                                      EmitSavedWord();
                                      EmitPVarReadWord()
                                    end
                                end
                              else
                                begin
                                  EmitSavedWord();
                                  EmitPVarReadWord()
                                end
                            end
                          else if IsSavedRecordVarName() then
                            begin
                              if current_kind = TOK_SYMBOL then
                                begin
                                  if current_text[0] = '.' then
                                    begin
                                      NextToken();
                                      if current_kind <> 1 then
                                        FailParse();
                                      if StrEqIgnoreCase(current_text, variant_arm0_name) then
                                        begin
                                          StrCopy(record_var_name, saved_text);
                                          EmitSavedWord();
                                          WriteLn(' PVAR@ __VAR_TAG PVAR!');
                                          WriteLn('__VAR_TAG PVAR@ 0 = 0= IF __VARIANT_MISMATCH THEN')
                                        end
                                      else
                                        begin
                                          if StrEqIgnoreCase(current_text, variant_arm1_name) then
                                            begin
                                              StrCopy(record_var_name, saved_text);
                                              EmitSavedWord();
                                              WriteLn(' PVAR@ __VAR_TAG PVAR!');
                                              WriteLn('__VAR_TAG PVAR@ 1 = 0= IF __VARIANT_MISMATCH THEN')
                                            end
                                          else
                                            begin
                                              if StrEqIgnoreCase(current_text, variant_arm2_name) then
                                                begin
                                                  StrCopy(record_var_name, saved_text);
                                                  EmitSavedWord();
                                                  WriteLn(' PVAR@ __VAR_TAG PVAR!');
                                                  WriteLn('__VAR_TAG PVAR@ 1 = 0= IF __VARIANT_MISMATCH THEN')
                                                end
                                            end
                                        end;
                                      if variant_active <> 0 then
                                        begin
                                          if StrEqIgnoreCase(variant_tag_name, current_text) then
                                            field_offset := 0
                                          else if StrEqIgnoreCase(variant_arm0_name, current_text) then
                                            field_offset := 4
                                          else if StrEqIgnoreCase(variant_arm1_name, current_text) then
                                            field_offset := 4
                                          else if StrEqIgnoreCase(variant_arm2_name, current_text) then
                                            field_offset := 8
                                          else
                                            begin
                                              field_offset := 0;
                                              field_offset := field_offset - 1
                                            end
                                        end
                                      else if StrEqIgnoreCase(field1_name, current_text) then
                                        field_offset := 0
                                      else if StrEqIgnoreCase(field2_name, current_text) then
                                        field_offset := 4
                                      else
                                        begin
                                          field_offset := 0;
                                          field_offset := field_offset - 1
                                        end;
                                      EmitFieldRead(record_var_name, field_offset);
                                      NextToken()
                                    end
                                  else
                                    begin
                                      EmitSavedWord();
                                      EmitPVarReadWord()
                                    end
                                end
                              else
                                begin
                                  EmitSavedWord();
                                  EmitPVarReadWord()
                                end
                            end
                          else if IsPointerVar(saved_text) then
                            begin
                              if current_kind = TOK_SYMBOL then
                                begin
                                  if current_text[0] = '^' then
                                    begin
                                      NextToken();
                                      if current_kind = TOK_SYMBOL then
                                        begin
                                          if current_text[0] = '[' then
                                            begin
                                              ExpectSymbolChar('[');
                                              NextToken();
                                              Write(saved_text);
                                              Write(' PVAR@ ');
                                              ParseSimpleExpr();
                                              Write(' 4 * + PVAR@ ');
                                              ExpectSymbolChar(']');
                                              NextToken()
                                            end
                                          else if current_text[0] = '.' then
                                            begin
                                              NextToken();
                                              ExpectKind(TOK_IDENT);
                                              Write(saved_text);
                                              WriteLn(' PVAR@ 0 + PVAR@');
                                              NextToken()
                                            end
                                          else
                                            begin
                                              Write(saved_text);
                                              WriteLn(' PVAR@ PVAR@')
                                            end;
                                        end
                                      else
                                        begin
                                          Write(saved_text);
                                          WriteLn(' PVAR@ PVAR@')
                                        end
                                    end
                                  else
                                    begin
                                      EmitSavedWord();
                                      Write('PVAR@ ')
                                    end
                                end
                              else
                                begin
                                  EmitSavedWord();
                                  Write('PVAR@ ')
                                end
                            end
                          else if with_active <> 0 then
                            begin
                              if ResolveFieldOffset(saved_text) >= 0 then
                                EmitFieldRead(with_base_text, ResolveFieldOffset(saved_text))
                              else if HasName(func_name) then
                                begin
                                  if StrEqIgnoreCase(saved_text, func_name) then
                                    begin
                                      if current_kind = TOK_SYMBOL then
                                        begin
                                          if current_text[0] = '(' then
                                            begin
                                              NextToken();
                                              Write(func_param);
                                              WriteLn(' PVAR@ >R');
                                              WriteLn('__FUNC_RET PVAR@ >R');
                                              ExpectKind(TOK_INT);
                                              Write(current_value);
                                              Write(' ');
                                              NextToken();
                                              ExpectSymbolChar(')');
                                              Write(func_name);
                                              WriteLn(' __CALL_RET PVAR!');
                                              WriteLn('R> __FUNC_RET PVAR!');
                                              Write('R> ');
                                              Write(func_param);
                                              WriteLn(' PVAR!');
                                              Write('__CALL_RET PVAR@ ');
                                              NextToken()
                                            end
                                          else
                                            begin
                                              EmitSavedWord();
                                              Write('PVAR@ ')
                                            end
                                        end
                                      else
                                        begin
                                          EmitSavedWord();
                                          Write('PVAR@ ')
                                        end
                                    end
                                  else
                                    begin
                                      EmitSavedWord();
                                      Write('PVAR@ ')
                                    end
                                end
                            end
                          else if HasName(func_name) then
                            begin
                              if StrEqIgnoreCase(saved_text, func_name) then
                                begin
                                  if current_kind = TOK_SYMBOL then
                                    begin
                                      if current_text[0] = '(' then
                                        begin
                                          NextToken();
                                          Write(func_param);
                                          WriteLn(' PVAR@ >R');
                                          WriteLn('__FUNC_RET PVAR@ >R');
                                          ExpectKind(TOK_INT);
                                          Write(current_value);
                                          Write(' ');
                                          NextToken();
                                          ExpectSymbolChar(')');
                                          Write(func_name);
                                          WriteLn(' __CALL_RET PVAR!');
                                          WriteLn('R> __FUNC_RET PVAR!');
                                          Write('R> ');
                                          Write(func_param);
                                          WriteLn(' PVAR!');
                                          Write('__CALL_RET PVAR@ ');
                                          NextToken()
                                        end
                                      else
                                        begin
                                          EmitSavedWord();
                                          Write('PVAR@ ')
                                        end
                                    end
                                  else
                                    begin
                                      EmitSavedWord();
                                      Write('PVAR@ ')
                                    end
                                end
                              else
                                begin
                                  EmitSavedWord();
                                  Write('PVAR@ ')
                                end
                            end
                          else if HasName(proc_param) and StrEqIgnoreCase(saved_text, proc_param) then
                            begin
                              Write(proc_param);
                              Write(' PVAR@ PVAR@ ')
                            end
                              else
                                begin
                                  EmitSavedWord();
                                  Write('PVAR@ ')
                                end
                            end
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                    end
                end
            end
        end
          end
        end
    end
  else
    begin
      FailParse()
    end
end;

procedure ParseTerm;
var
  done: boolean;
begin
  ParseFactor();
  done := false;
  while done = false do
    begin
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '*' then
            begin
              NextToken();
              ParseFactor();
              Write('* ')
            end
          else if current_text[0] = '/' then
            begin
              NextToken();
              ParseFactor();
              Write('/ ')
            end
          else
            done := true
        end
      else if current_kind = 1 then
        begin
          if StrEqIgnoreCase(current_text, kw_div) then
            begin
              NextToken();
              ParseFactor();
              Write('/ ')
            end
          else if StrEqIgnoreCase(current_text, kw_mod) then
            begin
              NextToken();
              ParseFactor();
              Write('MOD ')
            end
          else
            done := true
        end
      else
        done := true
    end
end;

procedure ParseSimpleExpr;
var
  done: boolean;
begin
  ParseTerm();
  done := false;
  while done = false do
    begin
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '+' then
            begin
              NextToken();
              ParseTerm();
              Write('+ ')
            end
          else if current_text[0] = '-' then
            begin
              NextToken();
              ParseTerm();
              Write('- ')
            end
          else
            done := true
        end
      else
        done := true
    end
end;

procedure ParseStringIndexAddress(var base_name: lexeme_buf);
begin
  Write(base_name);
  Write(' ');
  ExpectSymbolChar('[');
  NextToken();
  ParseSimpleExpr();
  Write(' 4 * + ');
  ExpectSymbolChar(']');
  NextToken()
end;

procedure ParseCondition;
begin
  ParseSimpleExpr();
  if current_kind <> TOK_SYMBOL then
    FailParse();
  if current_text[0] = '<' then
    begin
      if current_text[1] = '=' then
        begin
          NextToken();
          ParseSimpleExpr();
          Write('<= ')
        end
      else if current_text[1] = '>' then
        begin
          NextToken();
          ParseSimpleExpr();
          Write('<> ')
        end
      else if current_text[1] = #0 then
        begin
          NextToken();
          ParseSimpleExpr();
          Write('< ')
        end
      else
        FailParse()
    end
  else if current_text[0] = '>' then
    begin
      if current_text[1] = '=' then
        begin
          NextToken();
          ParseSimpleExpr();
          Write('>= ')
        end
      else if current_text[1] = #0 then
        begin
          NextToken();
          ParseSimpleExpr();
          Write('> ')
        end
      else
        FailParse()
    end
  else if current_text[0] = '=' then
    begin
      NextToken();
      ParseSimpleExpr();
      Write('= ')
    end
  else
    FailParse()
end;

procedure ParseAssignmentStmt;
var
  field_offset: integer;
  assign_expr_ready: integer;
begin
  StrCopy(saved_text, assign_text);
  field_offset := -1;
  assign_expr_ready := 0;
  if IsIntArrayVar(assign_text) then
    begin
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '[' then
            field_offset := -996
        end
    end;
  if IsStringVar(assign_text) then
    begin
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '[' then
            field_offset := -997
        end
    end;
  if IsPointerVar(assign_text) then
    begin
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '^' then
            begin
              field_offset := -995;
              NextToken();
              if current_kind = TOK_SYMBOL then
                begin
                  if current_text[0] = '[' then
                    field_offset := -994
                  else if current_text[0] = '.' then
                    begin
                      NextToken();
                      ExpectKind(TOK_IDENT);
                      NextToken()
                    end
                end
            end
        end
    end;
  if current_kind = TOK_SYMBOL then
    begin
      if current_text[0] = ':' then
        begin
          if current_text[1] = '=' then
            begin
              ExpectAssignSymbol();
              NextToken();
              assign_expr_ready := 1;
              if current_kind = TOK_STR then
                begin
                  EmitStringStore();
                  NextToken();
                  field_offset := -999
                end
              else if current_kind = TOK_SYMBOL then
                begin
                  if current_text[0] = '[' then
                    begin
                      ParseSetLiteral();
                      Write(set_mask_value);
                      Write(' ');
                      Write(assign_text);
                      WriteLn(' PVAR!');
                      field_offset := -998
                    end
                end
            end
        end
    end;
  if field_offset = -999 then
    begin
    end
  else if field_offset = -998 then
    begin
    end
  else if AssignTargetIsSetVar() then
    begin
      if assign_expr_ready = 0 then
        begin
          ExpectAssignSymbol();
          NextToken()
        end;
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = '[' then
            begin
              ParseSetLiteral();
              Write(set_mask_value);
              Write(' ');
              Write(assign_text);
              WriteLn(' PVAR!')
            end
          else
            FailParse()
        end
      else if current_kind = TOK_IDENT then
        begin
          Write(current_text);
          Write(' PVAR@ ');
          NextToken();
          ExpectSymbolChar('+');
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          Write(' PVAR@ OR ');
          Write(assign_text);
          WriteLn(' PVAR!');
          NextToken()
        end
      else
        FailParse()
    end
  else if HasEnumVarName() and StrEqIgnoreCase(enum_var_name, assign_text) then
    begin
      if assign_expr_ready = 0 then
        begin
          ExpectAssignSymbol();
          NextToken()
        end;
      ExpectKind(TOK_IDENT);
      ResolveCurrentEnumOrdinal();
      field_offset := set_mask_value;
      if field_offset < 0 then
        FailParse();
      Write(field_offset);
      Write(' ');
      Write(assign_text);
      WriteLn(' PVAR!');
      NextToken()
    end
  else if HasSubrangeVarName() and StrEqIgnoreCase(subrange_var_name, assign_text) then
    begin
      if assign_expr_ready = 0 then
        begin
          ExpectAssignSymbol();
          NextToken()
        end;
      ExpectKind(TOK_INT);
      Write(current_value);
      Write(' DUP ');
      Write(subrange_lo);
      Write(' >= OVER ');
      Write(subrange_hi);
      WriteLn(' <= AND 0= IF __SUBRANGE_MISMATCH THEN');
      Write(assign_text);
      WriteLn(' PVAR!');
      NextToken()
    end
  else if HasRealVarName() and StrEqIgnoreCase(real_var_name, assign_text) then
    begin
      if assign_expr_ready = 0 then
        begin
          ExpectAssignSymbol();
          NextToken()
        end;
      ParseRealExpr();
      Write(' ');
      Write(assign_text);
      WriteLn(' PVAR!')
    end
  else if IsStringVar(assign_text) then
    begin
      if field_offset = -997 then
        begin
          ParseStringIndexAddress(assign_text);
          WriteLn('>R');
          if assign_expr_ready = 0 then
            begin
              ExpectAssignSymbol();
              NextToken()
            end;
          if current_kind = TOK_STR then
            begin
              Write(Ord(current_text[0]));
              Write(' ');
              NextToken()
            end
          else if current_kind = TOK_SYMBOL then
            begin
              if current_text[0] <> '#' then
                FailParse();
              NextToken();
              ExpectKind(TOK_INT);
              Write(current_value);
              Write(' ');
              NextToken()
            end
          else
            ParseSimpleExpr();
          WriteLn('R> PVAR!')
        end
      else
        begin
          if assign_expr_ready = 0 then
            begin
              ExpectAssignSymbol();
              NextToken()
            end;
          if current_kind <> TOK_STR then
            FailParse();
          EmitStringStore();
          NextToken()
        end
    end
  else if HasName(proc_param) and StrEqIgnoreCase(proc_param, assign_text) then
    begin
      if assign_expr_ready = 0 then
        begin
          ExpectAssignSymbol();
          NextToken()
        end;
      ParseSimpleExpr();
      Write(proc_param);
      WriteLn(' PVAR@ PVAR!')
    end
  else
    begin
      if field_offset = -995 then
        begin
          if assign_expr_ready = 0 then
            begin
              ExpectAssignSymbol();
              NextToken()
            end;
          ParseSimpleExpr();
          Write(assign_text);
          WriteLn(' PVAR@ 0 + PVAR!')
        end
      else if field_offset = -994 then
        begin
          ExpectSymbolChar('[');
          NextToken();
          Write(assign_text);
          Write(' PVAR@ ');
          ParseSimpleExpr();
          WriteLn(' 4 * + >R');
          ExpectSymbolChar(']');
          NextToken();
          if assign_expr_ready = 0 then
            begin
              ExpectAssignSymbol();
              NextToken()
            end;
          ParseSimpleExpr();
          WriteLn('R> PVAR!')
        end
      else if field_offset = -996 then
        begin
          ParseArrayIndexes(assign_text);
          WriteLn('>R');
          if assign_expr_ready = 0 then
            begin
              ExpectAssignSymbol();
              NextToken()
            end;
          ParseSimpleExpr();
          WriteLn('R> PVAR!')
        end
      else
        begin
      if HasRecordVarName() and StrEqIgnoreCase(record_var_name, assign_text) then
        begin
          if current_kind = TOK_SYMBOL then
            begin
              if current_text[0] = '.' then
                begin
                  NextToken();
                  ExpectKind(TOK_IDENT);
                  field_offset := ResolveFieldOffset(current_text);
                  if field_offset < 0 then
                    FailParse();
                  set_mask_value := ResolveVariantExpectedTag(current_text);
                  NextToken()
                end
            end
        end
      else if with_active <> 0 then
        begin
          field_offset := ResolveFieldOffset(assign_text);
          if field_offset >= 0 then
            StrCopy(with_base_text, assign_text)
        end;
      if assign_expr_ready = 0 then
        begin
          ExpectAssignSymbol();
          NextToken()
        end;
      ParseSimpleExpr();
      if field_offset < 0 then
        begin
          Write(assign_text);
          Write(' ');
          WriteLn('PVAR!')
        end
      else if field_offset = 0 then
        begin
          Write(assign_text);
          Write(' ');
          WriteLn('PVAR!')
        end
      else
        begin
          EmitVariantTagCheck(set_mask_value, assign_text);
          Write(assign_text);
          Write(' ');
          Write(field_offset);
          WriteLn(' PFIELD!')
        end
        end
    end
end;

procedure ParseBuiltinStringStmt;
begin
  saved_text := 'Concat';
  if StrEqIgnoreCase(builtin_text, saved_text) then
    begin
      ExpectSymbolChar('(');
      NextToken();
      ExpectKind(TOK_IDENT);
      Write(current_text);
      WriteLn(' __STR_SRC PVAR!');
      NextToken();
      ExpectSymbolChar(',');
      Write(string_var3_name);
      WriteLn(' __STR_DST PVAR!');
      WriteLn('__STRCPY');
      Write(string_var1_name);
      WriteLn(' __STR_SRC PVAR!');
      WriteLn('__STRLEN __STR_LEN PVAR!');
      NextToken();
      ExpectKind(TOK_IDENT);
      Write(current_text);
      WriteLn(' __STR_SRC PVAR!');
      Write(string_var3_name);
      WriteLn(' __STR_LEN PVAR@ 4 * + __STR_DST PVAR!');
      WriteLn('__STRCPY');
      NextToken();
      ExpectSymbolChar(',');
      NextToken();
      ExpectKind(TOK_IDENT);
      NextToken();
      ExpectSymbolChar(')');
      NextToken()
    end
  else
    begin
      saved_text := 'Delete';
      if StrEqIgnoreCase(builtin_text, saved_text) then
        begin
          ExpectSymbolChar('(');
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          WriteLn(' __STR_DST PVAR!');
          NextToken();
          ExpectSymbolChar(',');
          NextToken();
          ExpectKind(TOK_INT);
          Write(current_value);
          WriteLn(' __STR_IDX PVAR!');
          NextToken();
          ExpectSymbolChar(',');
          NextToken();
          ExpectKind(TOK_INT);
          Write(current_value);
          WriteLn(' __STR_CNT PVAR!');
          WriteLn('__STRDELETE');
          NextToken();
          ExpectSymbolChar(')');
          NextToken()
        end
      else
        begin
          saved_text := 'Insert';
          if StrEqIgnoreCase(builtin_text, saved_text) then
            begin
              ExpectSymbolChar('(');
              NextToken();
              ExpectKind(TOK_IDENT);
              Write(current_text);
              WriteLn(' __STR_SRC PVAR!');
              NextToken();
              ExpectSymbolChar(',');
              NextToken();
              ExpectKind(TOK_IDENT);
              Write(current_text);
              WriteLn(' __STR_DST PVAR!');
              NextToken();
              ExpectSymbolChar(',');
              NextToken();
              ExpectKind(TOK_INT);
              Write(current_value);
              WriteLn(' __STR_IDX PVAR!');
              WriteLn('__STRINSERT');
              NextToken();
              ExpectSymbolChar(')');
              NextToken()
            end
          else
            begin
              saved_text := 'IntToHex';
              if StrEqIgnoreCase(builtin_text, saved_text) then
                begin
                  ExpectSymbolChar('(');
                  NextToken();
                  ExpectKind(TOK_INT);
                  Write(current_value);
                  WriteLn(' __I2H_VAL PVAR!');
                  NextToken();
                  ExpectSymbolChar(',');
                  NextToken();
                  ExpectKind(TOK_IDENT);
                  Write(current_text);
                  WriteLn(' __I2H_PTR PVAR!');
                  NextToken();
                  ExpectSymbolChar(',');
                  NextToken();
                  ExpectKind(TOK_INT);
                  Write(current_value);
                  WriteLn(' __I2H_MAX PVAR!');
                  NextToken();
                  ExpectSymbolChar(',');
                  NextToken();
                  ExpectKind(TOK_IDENT);
                  builtin_text := 'true';
                  if StrEqIgnoreCase(current_text, builtin_text) then
                    WriteLn('1 __I2H_FILL PVAR!')
                  else
                    WriteLn('0 __I2H_FILL PVAR!');
                  WriteLn('__I32_TO_HEX_STR');
                  NextToken();
                  ExpectSymbolChar(')');
                  NextToken()
                end
              else
                FailParse()
            end
        end
    end
end;

procedure ParseReadStmt;
begin
  ExpectSymbolChar('(');
  NextToken();
  ExpectKind(TOK_IDENT);
  Write('PREAD-I32 ');
  Write(current_text);
  WriteLn(' PVAR!');
  NextToken();
  ExpectSymbolChar(')');
  NextToken()
end;

procedure ParsePointerBuiltinStmt;
begin
  saved_text := 'new';
  if StrEqIgnoreCase(builtin_text, saved_text) then
    begin
      ExpectSymbolChar('(');
      NextToken();
      ExpectKind(TOK_IDENT);
      WriteLn('HERE __NEWP PVAR!');
      WriteLn('4 ALLOT');
      WriteLn('__NEWP PVAR@ ');
      Write(current_text);
      WriteLn(' PVAR!');
      NextToken();
      ExpectSymbolChar(')');
      NextToken()
    end
  else
    begin
      saved_text := 'dispose';
      if StrEqIgnoreCase(builtin_text, saved_text) then
    begin
      ExpectSymbolChar('(');
      NextToken();
      ExpectKind(TOK_IDENT);
      Write('0 ');
      Write(current_text);
      WriteLn(' PVAR!');
      NextToken();
      ExpectSymbolChar(')');
      NextToken()
        end
      else
        begin
          saved_text := 'setaddr';
          if StrEqIgnoreCase(builtin_text, saved_text) then
    begin
      ExpectSymbolChar('(');
      NextToken();
      ExpectKind(TOK_IDENT);
      StrCopy(current_text, saved_text);
      NextToken();
      ExpectSymbolChar(',');
      NextToken();
      ExpectKind(TOK_IDENT);
      Write(current_text);
      Write(' PVAR@ ');
      Write(saved_text);
      WriteLn(' PVAR!');
      NextToken();
      ExpectSymbolChar(')');
      NextToken()
            end
          else
            FailParse()
        end
    end
end;

procedure ParseProcedureCallStmt;
begin
  if conformant_proc_dims <> 0 then
    begin
      ExpectSymbolChar('(');
      NextToken();
      ExpectKind(TOK_IDENT);
      if StrEqIgnoreCase(current_text, int_array_var_name) = false then
        FailParse();
      NextToken();
      ExpectSymbolChar(')');
      Write(proc_name);
      WriteLn('');
      NextToken()
    end
  else
    begin
      ExpectSymbolChar('(');
      NextToken();
      if current_kind = TOK_SYMBOL then
        begin
          if current_text[0] = ')' then
            begin
              Write(proc_name);
              WriteLn('');
              NextToken()
            end
          else
            FailParse()
        end
      else
        begin
          ExpectKind(TOK_IDENT);
          Write(proc_param);
          WriteLn(' PVAR@ >R');
          Write(current_text);
          Write(' ');
          NextToken();
          ExpectSymbolChar(')');
          Write(proc_name);
          WriteLn(' R> ');
          Write(proc_param);
          WriteLn(' PVAR!');
          NextToken()
        end
    end
end;

procedure EmitConformantArrayProcedure(dummy: integer);
var
  cell_index: integer;
begin
  Write(': ');
  Write(proc_name);
  WriteLn('');
  cell_index := 0;
  while cell_index < array_total_cells do
    begin
      if cell_index = 0 then
        begin
          Write(int_array_var_name);
          WriteLn(' PVAR@')
        end
      else
        begin
          Write(int_array_var_name);
          Write(' ');
          Write(cell_index * 4);
          WriteLn(' PFIELD@ +')
        end;
      cell_index := cell_index + 1
    end;
  WriteLn('PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';')
end;

procedure ParseWithStmt;
begin
  ExpectKind(TOK_IDENT);
  StrCopy(current_text, with_base_text);
  NextToken();
  if StrEqIgnoreCase(current_text, kw_do) = false then
    FailParse();
  NextToken();
  ExpectKind(TOK_KW_BEGIN);
  NextToken();
  with_active := 1;
  ParseStmtList();
  with_active := 0;
  ExpectKind(TOK_KW_END);
  NextToken()
end;

procedure ParseIfStmt;
begin
  NextToken();
  ParseSimpleExpr();
  if current_kind = TOK_SYMBOL then
    begin
      if current_text[0] = '<' then
        begin
          if current_text[1] = '=' then
            begin
              NextToken();
              ParseSimpleExpr();
              Write('<= ')
            end
          else if current_text[1] = '>' then
            begin
              NextToken();
              ParseSimpleExpr();
              Write('<> ')
            end
          else if current_text[1] = #0 then
            begin
              NextToken();
              ParseSimpleExpr();
              Write('< ')
            end
          else
            FailParse()
        end
      else if current_text[0] = '>' then
        begin
          if current_text[1] = '=' then
            begin
              NextToken();
              ParseSimpleExpr();
              Write('>= ')
            end
          else if current_text[1] = #0 then
            begin
              NextToken();
              ParseSimpleExpr();
              Write('> ')
            end
          else
            FailParse()
        end
      else if current_text[0] = '=' then
        begin
          NextToken();
          ParseSimpleExpr();
          Write('= ')
        end
    end;
  WriteLn('IF');
  if StrEqIgnoreCase(current_text, kw_then) = false then
    FailParse();
  NextToken();
  ParseStmt();
  if current_kind = TOK_IDENT then
    begin
      if StrEqIgnoreCase(current_text, kw_else) then
        begin
          WriteLn('ELSE');
          NextToken();
          ParseStmt()
        end
    end;
  WriteLn('THEN')
end;

procedure ParseCaseStmt;
var
  case_var_name: lexeme_buf;
  low_text: lexeme_buf;
  mid_text: lexeme_buf;
  high_text: lexeme_buf;
begin
  ExpectKind(TOK_IDENT);
  StrCopy(current_text, case_var_name);
  NextToken();
  builtin_text := 'of';
  if StrEqIgnoreCase(current_text, builtin_text) = false then
    FailParse();
  ClearStr(low_text);
  ClearStr(mid_text);
  ClearStr(high_text);
  Write(case_var_name);
  WriteLn(' PVAR@ >R');
  WriteLn('  0 __CASE_MATCH PVAR!');
  NextToken();

  ExpectKind(TOK_INT);
  NextToken();
  ExpectSymbolChar(',');
  NextToken();
  ExpectKind(TOK_INT);
  NextToken();
  ExpectSymbolChar(':');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailParse();
  NextToken();
  ExpectSymbolChar('(');
  NextToken();
  ExpectKind(TOK_STR);
  StrCopy(current_text, low_text);
  NextToken();
  ExpectSymbolChar(')');
  NextToken();
  ExpectSymbolChar(';');
  NextToken();

  ExpectKind(TOK_INT);
  NextToken();
  ExpectSymbolChar('.');
  if current_text[1] <> '.' then
    FailParse();
  NextToken();
  ExpectKind(TOK_INT);
  NextToken();
  ExpectSymbolChar(':');
  NextToken();
  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailParse();
  NextToken();
  ExpectSymbolChar('(');
  NextToken();
  ExpectKind(TOK_STR);
  StrCopy(current_text, mid_text);
  NextToken();
  ExpectSymbolChar(')');
  NextToken();

  builtin_text := 'else';
  if StrEqIgnoreCase(current_text, builtin_text) = false then
    FailParse();
  NextToken();
  if StrEqIgnoreCase(current_text, kw_writeln) = false then
    FailParse();
  NextToken();
  ExpectSymbolChar('(');
  NextToken();
  ExpectKind(TOK_STR);
  StrCopy(current_text, high_text);
  NextToken();
  ExpectSymbolChar(')');
  NextToken();

  builtin_text := 'end';
  if StrEqIgnoreCase(current_text, builtin_text) = false then
    FailParse();

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

  NextToken()
end;

procedure ParseWriteLnStmt;
begin
  ExpectSymbolChar('(');
  NextToken();
  if current_kind = TOK_STR then
    begin
      EmitCurrentStringText();
      NextToken()
    end
  else if current_kind = TOK_SYMBOL then
    begin
      if current_text[0] = '(' then
        begin
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          Write(' PVAR@ ');
          NextToken();
          ExpectSymbolChar('*');
          NextToken();
          ParseSetLiteral();
          Write(set_mask_value);
          EmitAndWord();
          ExpectSymbolChar(')');
          NextToken();
          ExpectSymbolChar('=');
          NextToken();
          ParseSetLiteral();
          Write(set_mask_value);
          WriteLn(' = PWRITE-BOOL')
        end
      else
        begin
          ParseSimpleExpr();
          WriteLn('PWRITE-I32')
        end
    end
  else if current_kind = TOK_IDENT then
    begin
      if HasEnumVarName() and StrEqIgnoreCase(enum_var_name, current_text) then
        begin
          StrCopy(current_text, saved_text);
          NextToken();
          builtin_text := 'in';
          if StrEqIgnoreCase(current_text, builtin_text) = false then
            FailParse();
          EmitIntWord(1);
          EmitSavedWord();
          WriteLn(' PVAR@ LSHIFT');
          NextToken();
          if current_kind <> TOK_IDENT then
            FailParse();
          EmitCurrentWord();
          WriteLn(' PVAR@ AND 0= 0= PWRITE-BOOL');
          NextToken()
        end
      else if IsExactRoundName() then
        begin
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> '(' then
            FailParse();
          NextToken();
          if current_kind <> TOK_IDENT then
            FailParse();
          EmitCurrentWord();
          WriteLn(' PVAR@ FROUND-I32 PWRITE-I32');
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> ')' then
            FailParse();
          NextToken()
        end
      else if IsExactAbsName() then
        begin
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> '(' then
            FailParse();
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> '-' then
            FailParse();
          NextToken();
          if current_kind <> TOK_INT then
            FailParse();
          EmitIntWord(current_value);
          WriteLn(' NEGATE DUP 0< IF NEGATE THEN PWRITE-I32');
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> ')' then
            FailParse();
          NextToken()
        end
      else if IsExactSqrName() then
        begin
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> '(' then
            FailParse();
          NextToken();
          if current_kind <> TOK_INT then
            FailParse();
          EmitIntWord(current_value);
          WriteLn(' DUP * PWRITE-I32');
          NextToken();
          if current_kind <> TOK_SYMBOL then
            FailParse();
          if current_text[0] <> ')' then
            FailParse();
          NextToken()
        end
      else if IsExactOddName() then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          ExpectKind(TOK_INT);
          Write(current_value);
          WriteLn(' 1 AND 0= 0= PWRITE-BOOL');
          NextToken();
          ExpectSymbolChar(')');
          NextToken()
        end
      else if IsExactUpCaseName() then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          ExpectKind(TOK_STR);
          Write(Ord(current_text[0]));
          WriteLn(' DUP 97 >= OVER 122 <= AND IF 32 - THEN PWRITE-CHAR');
          NextToken();
          ExpectSymbolChar(')');
          NextToken()
        end
      else if IsExactOrdName() then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          builtin_text := 'Chr';
			                                                                          if StrEqIgnoreCase(current_text, builtin_text) then
			                                                                                begin
              NextToken();
              ExpectSymbolChar('(');
              NextToken();
              ExpectKind(TOK_INT);
              Write(current_value);
              WriteLn(' PWRITE-I32');
              NextToken();
              ExpectSymbolChar(')');
              NextToken();
              ExpectSymbolChar(')');
              NextToken()
            end
          else
            begin
              ExpectKind(TOK_IDENT);
              Write(current_text);
              Write(' PVAR@ ');
              NextToken();
              ExpectSymbolChar(')');
              NextToken();
              ExpectSymbolChar('+');
              NextToken();
              ExpectKind(TOK_IDENT);
              Write(current_text);
              WriteLn(' PVAR@ + PWRITE-I32');
              NextToken()
            end
        end
      else if IsExactTruncName() then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          WriteLn(' PVAR@ F>S PWRITE-I32');
          NextToken();
          ExpectSymbolChar(')');
          NextToken()
        end
      else if IsStringVar(current_text) then
        begin
          EmitStringWriteBody();
          NextToken()
        end
      else if HasRealVarName() and StrEqIgnoreCase(real_var_name, current_text) then
        begin
          Write(current_text);
          WriteLn(' PVAR@ PWRITE-F32');
          NextToken()
        end
      else if IsExactPosName() then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          Write(' __STR_A PVAR! ');
          NextToken();
          ExpectSymbolChar(',');
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          WriteLn(' __STR_B PVAR! __STRPOS PWRITE-I32');
          NextToken();
          ExpectSymbolChar(')');
          NextToken()
        end
      else if IsExactHexToIntName() then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          ExpectKind(TOK_IDENT);
          Write(current_text);
          Write(' __HEX_PTR PVAR! ');
          Write(char_array_len);
          WriteLn(' __HEX_LEN PVAR! __HEX_TO_I32 PWRITE-I32');
          NextToken();
          ExpectSymbolChar(')');
          NextToken()
        end
      else
        begin
          ResolveCurrentEnumOrdinal();
          if set_mask_value >= 0 then
            begin
              Write(EnumBit(set_mask_value));
              Write(' ');
              NextToken();
              builtin_text := 'in';
              if StrEqIgnoreCase(current_text, builtin_text) = false then
                FailParse();
              NextToken();
              ExpectKind(TOK_IDENT);
              Write(current_text);
              WriteLn(' PVAR@ AND 0= 0= PWRITE-BOOL');
              NextToken()
            end
          else if HasName(func_name) and StrEqIgnoreCase(current_text, func_name) then
            begin
              NextToken();
              ExpectSymbolChar('(');
              NextToken();
              Write(func_param);
              WriteLn(' PVAR@ >R');
              WriteLn('__FUNC_RET PVAR@ >R');
              ExpectKind(TOK_INT);
              Write(current_value);
              Write(' ');
              NextToken();
              ExpectSymbolChar(')');
              Write(func_name);
              WriteLn(' __CALL_RET PVAR!');
              WriteLn('R> __FUNC_RET PVAR!');
              Write('R> ');
              Write(func_param);
              WriteLn(' PVAR!');
              WriteLn('__CALL_RET PVAR@ PWRITE-I32');
              NextToken()
            end
          else if IsPointerVar(current_text) then
            begin
              StrCopy(current_text, saved_text);
              NextToken();
              if current_kind = TOK_SYMBOL then
                begin
                  if current_text[0] = '^' then
                    begin
                      NextToken();
                      if current_kind = TOK_SYMBOL then
                        begin
                          if current_text[0] = '.' then
                            begin
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              Write(saved_text);
                              WriteLn(' PVAR@ 0 + PVAR@ PWRITE-I32');
                              NextToken()
                            end
                          else
                            begin
                              Write(saved_text);
                              WriteLn(' PVAR@ PVAR@ PWRITE-I32')
                            end
                        end
                      else
                        begin
                          Write(saved_text);
                          WriteLn(' PVAR@ PVAR@ PWRITE-I32')
                        end
                    end
                  else
                    begin
                      ExpectSymbolChar('=');
                      NextToken();
                      builtin_text := 'nil';
                      if StrEqIgnoreCase(current_text, builtin_text) = false then
                        FailParse();
                      Write(saved_text);
                      WriteLn(' PVAR@ 0 = PWRITE-BOOL');
                      NextToken()
                    end
                end
              else
                begin
                  Write(saved_text);
                  WriteLn(' PVAR@ PWRITE-I32')
                end
            end
          else
            begin
              ParseSimpleExpr();
              WriteLn('PWRITE-I32')
            end
        end
    end
  else
    begin
      ParseSimpleExpr();
      WriteLn('PWRITE-I32')
    end;
  WriteLn('  PWRITELN');
  ExpectSymbolChar(')');
  NextToken()
end;

procedure ParseSimpleStmt;
begin
  if current_kind = TOK_IDENT then
    begin
      builtin_text := 'SetSourceAt';
      if StrEqIgnoreCase(current_text, builtin_text) then
        begin
          NextToken();
          ExpectSymbolChar('(');
          NextToken();
          ParseSimpleExpr();
          ExpectSymbolChar(',');
          NextToken();
          ParseSimpleExpr();
          WriteLn('SetSourceAt');
          ExpectSymbolChar(')');
          NextToken()
        end
      else
        begin
      builtin_text := 'Read';
      if IsExactReadName() then
        begin
          NextToken();
          ParseReadStmt()
        end
      else if IsExactWriteLnName() then
        begin
          NextToken();
          ParseWriteLnStmt()
        end
      else if IsExactWithName() then
        begin
          NextToken();
          ParseWithStmt()
        end
      else if IsExactConcatName() then
        begin
          StrCopy(current_text, builtin_text);
          NextToken();
          ParseBuiltinStringStmt()
        end
      else
        begin
          builtin_text := 'Delete';
          if IsExactDeleteName() then
            begin
              StrCopy(current_text, builtin_text);
              NextToken();
              ParseBuiltinStringStmt()
            end
          else
            begin
              builtin_text := 'Insert';
              if IsExactInsertName() then
                begin
                  StrCopy(current_text, builtin_text);
                  NextToken();
                  ParseBuiltinStringStmt()
                end
              else
                begin
                  builtin_text := 'IntToHex';
                  if IsExactIntToHexName() then
                    begin
                      StrCopy(current_text, builtin_text);
                      NextToken();
                      ParseBuiltinStringStmt()
                    end
                  else
                    begin
                      builtin_text := 'new';
                      if IsExactNewName() then
                        begin
                          StrCopy(current_text, builtin_text);
                          NextToken();
                          ParsePointerBuiltinStmt()
                        end
                      else
                        begin
                          builtin_text := 'dispose';
                          if IsExactDisposeName() then
                            begin
                              StrCopy(current_text, builtin_text);
                              NextToken();
                              ParsePointerBuiltinStmt()
                            end
                          else
                            begin
                              builtin_text := 'SetAddr';
                              if IsExactSetAddrName() then
                                begin
                                  StrCopy(current_text, builtin_text);
                                  NextToken();
                                  ParsePointerBuiltinStmt()
                                end
                              else
                                begin
                                      builtin_text := 'InitKeywords';
                                  if StrEqIgnoreCase(current_text, builtin_text) then
                                    begin
                                      NextToken();
                                      ExpectSymbolChar('(');
                                      NextToken();
                                      ExpectSymbolChar(')');
                                      WriteLn('InitKeywords');
                                      NextToken()
                                    end
                                  else
                                    begin
                                      builtin_text := 'AdvanceChar';
                                      if StrEqIgnoreCase(current_text, builtin_text) then
                                        begin
                                          NextToken();
                                          ExpectSymbolChar('(');
                                          NextToken();
                                          ExpectSymbolChar(')');
                                          WriteLn('AdvanceChar');
                                          NextToken()
                                        end
                                      else
                                        begin
                                          builtin_text := 'SkipSpaces';
                                          if StrEqIgnoreCase(current_text, builtin_text) then
                                            begin
                                              NextToken();
                                              ExpectSymbolChar('(');
                                              NextToken();
                                              ExpectSymbolChar(')');
                                              WriteLn('SkipSpaces');
                                              NextToken()
                                            end
                                          else
                                            begin
                                              builtin_text := 'ReadIdentifier';
                                              if StrEqIgnoreCase(current_text, builtin_text) then
                                                begin
                                                  NextToken();
                                                  ExpectSymbolChar('(');
                                                  NextToken();
                                                  ExpectSymbolChar(')');
                                                  WriteLn('ReadIdentifier');
                                                  NextToken()
                                                end
                                              else
                                                begin
                                                  builtin_text := 'ReadNumber';
                                                  if StrEqIgnoreCase(current_text, builtin_text) then
                                                    begin
                                                      NextToken();
                                                      ExpectSymbolChar('(');
                                                      NextToken();
                                                      ExpectSymbolChar(')');
                                                      WriteLn('ReadNumber');
                                                      NextToken()
                                                    end
                                                  else
                                                    begin
                                                      builtin_text := 'ReadSymbol';
                                                      if StrEqIgnoreCase(current_text, builtin_text) then
                                                        begin
                                                          NextToken();
                                                          ExpectSymbolChar('(');
                                                          NextToken();
                                                          ExpectSymbolChar(')');
                                                          WriteLn('ReadSymbol');
                                                          NextToken()
                                                        end
                                                      else
                                                        begin
                                                          builtin_text := 'ReadString';
                                                          if StrEqIgnoreCase(current_text, builtin_text) then
                                                            begin
                                                              NextToken();
                                                              ExpectSymbolChar('(');
                                                              NextToken();
                                                              ExpectSymbolChar(')');
                                                              WriteLn('ReadString');
                                                              NextToken()
                                                            end
                                                          else
                                                            begin
                                                              builtin_text := 'NextToken';
	                                                              if StrEqIgnoreCase(current_text, builtin_text) then
	                                                                begin
	                                                                  NextToken();
	                                                                  ExpectSymbolChar('(');
	                                                                  NextToken();
	                                                                  ExpectSymbolChar(')');
	                                                                  WriteLn('NextToken');
	                                                                  NextToken()
	                                                                end
	                                                              else
	                                                                begin
		                                                                  builtin_text := 'ClearStr';
		                                                                  if StrEqIgnoreCase(current_text, builtin_text) then
		                                                                    begin
                                                                      NextToken();
                                                                      ExpectSymbolChar('(');
                                                                      NextToken();
                                                                      ExpectKind(TOK_IDENT);
                                                                      Write(current_text);
                                                                      WriteLn(' ClearStr');
                                                                      NextToken();
	                                                                      ExpectSymbolChar(')');
	                                                                      NextToken()
	                                                                    end
		                                                                  else
		                                                                    begin
		                                                                      builtin_text := 'AppendChar';
                                                                      if StrEqIgnoreCase(current_text, builtin_text) then
                                                                        begin
                                                                          NextToken();
                                                                          ExpectSymbolChar('(');
                                                                          NextToken();
                                                                          ExpectKind(TOK_IDENT);
                                                                          Write(current_text);
                                                                          Write(' ');
                                                                          NextToken();
                                                                          ExpectSymbolChar(',');
                                                                          NextToken();
                                                                          ParseSimpleExpr();
                                                                          ExpectSymbolChar(')');
                                                                          WriteLn(' AppendChar');
                                                                          NextToken()
                                                                        end
                                                                      else
                                                                        begin
                                                                          builtin_text := 'StrCopy';
                                                                          if StrEqIgnoreCase(current_text, builtin_text) then
                                                                            begin
                                                                              NextToken();
                                                                              ExpectSymbolChar('(');
                                                                              NextToken();
                                                                              ExpectKind(TOK_IDENT);
                                                                              Write(current_text);
                                                                              Write(' ');
                                                                              NextToken();
                                                                              ExpectSymbolChar(',');
                                                                              NextToken();
                                                                              ExpectKind(TOK_IDENT);
                                                                              Write(current_text);
                                                                              WriteLn(' StrCopy');
                                                                              NextToken();
                                                                              ExpectSymbolChar(')');
                                                                              NextToken()
                                                                            end
                                                                          else
                                                                            begin
		                                                                          builtin_text := 'EmitVariantTagCheck';
		                                                                          if StrEqIgnoreCase(current_text, builtin_text) then
		                                                                                begin
                                                                                  NextToken();
                                                                                  ExpectSymbolChar('(');
                                                                                  NextToken();
                                                                                  ParseSimpleExpr();
                                                                                  Write(' ');
                                                                                  ExpectSymbolChar(',');
                                                                                  NextToken();
                                                                                  ExpectKind(TOK_IDENT);
                                                                                  Write(current_text);
                                                                                  WriteLn(' EmitVariantTagCheck');
		                                                                                  NextToken();
			                                                                                  ExpectSymbolChar(')');
			                                                                                  NextToken()
			                                                                                end
			                                                                              else
			                                                                                begin
				                                                                          builtin_text := 'EmitFieldRead';
				                                                                          if StrEqIgnoreCase(current_text, builtin_text) then
				                                                                                begin
                                                                                  NextToken();
                                                                                  ExpectSymbolChar('(');
                                                                                  NextToken();
                                                                                  ExpectKind(TOK_IDENT);
                                                                                  Write(current_text);
                                                                                  Write(' ');
                                                                                  NextToken();
                                                                                  ExpectSymbolChar(',');
                                                                                  NextToken();
                                                                                  ParseSimpleExpr();
                                                                                  WriteLn(' EmitFieldRead');
				                                                                                  ExpectSymbolChar(')');
				                                                                                  NextToken()
				                                                                                end
				                                                                              else
				                                                                                begin
				                                                                              StrCopy(current_text, saved_text);
				                                                                              NextToken();
                                                                              if current_kind = TOK_SYMBOL then
                                                                                begin
                                                                                  if current_text[0] = '(' then
                                                                                    begin
                                                                                      if HasName(proc_name) then
                                                                                        StrCopy(proc_name, builtin_text)
                                                                                      else
                                                                                        ClearStr(builtin_text);
                                                                                      StrCopy(saved_text, proc_name);
                                                                                      ParseProcedureCallStmt();
                                                                                      StrCopy(builtin_text, proc_name)
                                                                                    end
                                                                                  else
                                                                                    ParseAssignmentStmt()
                                                                                end
                                                                              else
                                                                                ParseAssignmentStmt()
				                                                                                end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end;
                                                    end;
                                                end;
                                            end
                                        end
                                    end
                                end
                            end
                        end;
                    end;
                end;
            end;
        end;
      end
    end
  else
    FailParse()
end;

procedure ParseForStmt;
begin
  NextToken();
  ExpectKind(TOK_IDENT);
  StrCopy(current_text, loop_var_text);
  NextToken();
  if current_kind <> TOK_SYMBOL then
    FailParse();
  if current_text[0] <> ':' then
    FailParse();
  if current_text[1] <> '=' then
    FailParse();
  NextToken();
  ParseSimpleExpr();
  Write(loop_var_text);
  WriteLn(' PVAR!');
  if StrEqIgnoreCase(current_text, kw_to) = false then
    FailParse();
  NextToken();
  WriteLn('BEGIN');
  Write(loop_var_text);
  Write(' PVAR@ ');
  ParseSimpleExpr();
  WriteLn('<= WHILE');
  if StrEqIgnoreCase(current_text, kw_do) = false then
    FailParse();
  NextToken();
  ParseStmt();
  Write(loop_var_text);
  Write(' PVAR@ 1 + ');
  Write(loop_var_text);
  WriteLn(' PVAR!');
  WriteLn('REPEAT')
end;

procedure ParseWhileStmt;
begin
  NextToken();
  WriteLn('BEGIN');
  ParseCondition();
  WriteLn('WHILE');
  if StrEqIgnoreCase(current_text, kw_do) = false then
    FailParse();
  NextToken();
  ParseStmt();
  WriteLn('REPEAT')
end;

procedure ParseRepeatStmt;
var
  done: boolean;
begin
  NextToken();
  WriteLn('BEGIN');
  done := false;
  while done = false do
    begin
      ParseStmt();
      if StrEqIgnoreCase(current_text, kw_until) then
        done := true
      else
        begin
          ExpectSymbolChar(';');
          NextToken()
        end
    end;
  NextToken();
  ParseCondition();
  WriteLn('UNTIL')
end;

procedure ParseLocalVarSection;
var
  parsing: boolean;
begin
  parsing := false;
  if current_kind = TOK_KW_VAR then
    begin
      parsing := true;
      NextToken()
    end;
  while parsing do
    begin
      if current_kind = TOK_KW_BEGIN then
        parsing := false
      else
        begin
          ExpectKind(TOK_IDENT);
          repeat
            Write('CREATE ');
            Write(current_text);
            WriteLn(' 0 ,');
            NextToken();
            if current_kind = TOK_SYMBOL then
              begin
                if current_text[0] = ',' then
                  NextToken()
              end
          until (current_kind <> TOK_SYMBOL) or (current_text[0] <> ',');
          ExpectSymbolChar(':');
          NextToken();
          if current_kind = TOK_KW_INTEGER then
            NextToken()
          else if StrEqIgnoreCase(current_text, kw_char) then
            NextToken()
          else
            begin
              builtin_text := 'boolean';
              if StrEqIgnoreCase(current_text, builtin_text) then
                NextToken()
              else
                FailParse()
            end;
          ExpectSymbolChar(';');
          NextToken()
        end
    end
end;

procedure EmitCreateCurrentVar;
begin
  Write('CREATE ');
  Write(current_text);
  WriteLn(' 0 ,')
end;

procedure EmitCreateCurrentRecordVar;
begin
  Write('CREATE ');
  Write(current_text);
  WriteLn(' 0 , 4 ALLOT')
end;

procedure ParseConstSection;
var
  done: boolean;
begin
  if current_kind = TOK_IDENT then
    begin
      builtin_text := 'const';
      if StrEqIgnoreCase(current_text, builtin_text) then
        begin
          NextToken();
          done := false;
          while done = false do
            begin
              if current_kind <> TOK_IDENT then
                done := true
              else if StrEqIgnoreCase(current_text, kw_type) then
                done := true
              else if StrEqIgnoreCase(current_text, kw_var) then
                begin
                  current_kind := TOK_KW_VAR;
                  done := true
                end
              else if StrEqIgnoreCase(current_text, kw_begin) then
                begin
                  current_kind := TOK_KW_BEGIN;
                  done := true
                end
              else if StrEqIgnoreCase(current_text, kw_procedure) then
                done := true
              else if StrEqIgnoreCase(current_text, kw_function) then
                done := true
              else
                begin
                  NextToken();
                  ExpectSymbolChar('=');
                  NextToken();
                  if current_kind <> TOK_INT then
                    FailParse();
                  NextToken();
                  ExpectSymbolChar(';');
                  NextToken()
                end
            end
        end
    end
end;

procedure ParseTypeSection;
begin
  if current_kind = TOK_IDENT then
    begin
      if StrEqIgnoreCase(current_text, kw_type) then
        begin
          ClearStr(record_type_name);
          ClearStr(variant_type_name);
          ClearStr(pointer_type_name);
          ClearStr(int_array_type_name);
          ClearStr(string_type_name);
          ClearStr(string_type2_name);
          ClearStr(enum_type_name);
          ClearStr(set_type_name);
          ClearStr(subrange_type_name);
          NextToken();
          while current_kind = TOK_IDENT do
            begin
              if StrEqIgnoreCase(current_text, kw_var) then
                current_kind := TOK_KW_VAR
              else
                begin
                  StrCopy(current_text, saved_text);
                  NextToken();
                  ExpectSymbolChar('=');
                  NextToken();
                  if StrEqIgnoreCase(current_text, kw_record) then
                    begin
                      NextToken();
                      if current_kind = TOK_IDENT then
                        begin
                          builtin_text := 'case';
                          if StrEqIgnoreCase(current_text, builtin_text) then
                            begin
                              variant_active := 1;
                              StrCopy(saved_text, variant_type_name);
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              StrCopy(current_text, variant_tag_name);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectKind(TOK_KW_INTEGER);
                              NextToken();
                              builtin_text := 'of';
                              if StrEqIgnoreCase(current_text, builtin_text) = false then
                                FailParse();
                              NextToken();
                              ExpectKind(TOK_INT);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectSymbolChar('(');
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              StrCopy(current_text, variant_arm0_name);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectKind(TOK_KW_INTEGER);
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              ExpectSymbolChar(')');
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              ExpectKind(TOK_INT);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectSymbolChar('(');
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              StrCopy(current_text, variant_arm1_name);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectKind(TOK_KW_INTEGER);
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              StrCopy(current_text, variant_arm2_name);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectKind(TOK_KW_INTEGER);
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              ExpectSymbolChar(')');
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_end) = false then
                                FailParse();
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken()
                            end
                          else
                            begin
                              StrCopy(saved_text, record_type_name);
                              StrCopy(current_text, field1_name);
                              ClearStr(field2_name);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectKind(TOK_KW_INTEGER);
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_end) = false then
                                begin
                                  ExpectKind(TOK_IDENT);
                                  StrCopy(current_text, field2_name);
                                  NextToken();
                                  ExpectSymbolChar(':');
                                  NextToken();
                                  ExpectKind(TOK_KW_INTEGER);
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken()
                                end;
                              if StrEqIgnoreCase(current_text, kw_end) = false then
                                FailParse();
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken()
                            end
                        end
                      else
                        FailParse()
                    end
                  else if StrEqIgnoreCase(current_text, kw_array) then
                    begin
                      NextToken();
                      ExpectSymbolChar('[');
                      NextToken();
                      ExpectKind(TOK_INT);
                      array_lo1 := current_value;
                      NextToken();
                      if current_kind = TOK_SYMBOL then
                        begin
                          if current_text[0] = '.' then
                            begin
                              if current_text[1] <> '.' then
                                FailParse();
                              NextToken();
                              ExpectKind(TOK_INT);
                              array_hi1 := current_value;
                              array_dim_count := 1;
                              NextToken();
                              if current_kind = TOK_SYMBOL then
                                begin
                                  if current_text[0] = ',' then
                                    begin
                                      array_dim_count := 2;
                                      NextToken();
                                      ExpectKind(TOK_INT);
                                      array_lo2 := current_value;
                                      NextToken();
                                      ExpectSymbolChar('.');
                                      if current_text[1] <> '.' then
                                        FailParse();
                                      NextToken();
                                      ExpectKind(TOK_INT);
                                      array_hi2 := current_value;
                                      NextToken();
                                      if current_kind = TOK_SYMBOL then
                                        begin
                                          if current_text[0] = ',' then
                                            begin
                                              array_dim_count := 3;
                                              NextToken();
                                              ExpectKind(TOK_INT);
                                              array_lo3 := current_value;
                                              NextToken();
                                              ExpectSymbolChar('.');
                                              if current_text[1] <> '.' then
                                                FailParse();
                                              NextToken();
                                              ExpectKind(TOK_INT);
                                              array_hi3 := current_value;
                                              NextToken();
                                              if current_kind = TOK_SYMBOL then
                                                begin
                                                  if current_text[0] = ',' then
                                                    begin
                                                      array_dim_count := 4;
                                                      NextToken();
                                                      ExpectKind(TOK_INT);
                                                      array_lo4 := current_value;
                                                      NextToken();
                                                      ExpectSymbolChar('.');
                                                      if current_text[1] <> '.' then
                                                        FailParse();
                                                      NextToken();
                                                      ExpectKind(TOK_INT);
                                                      array_hi4 := current_value;
                                                      NextToken()
                                                    end;
                                                end;
                                            end
                                        end
                                    end
                                end;
                              ExpectSymbolChar(']');
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_of) = false then
                                FailParse();
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_char) then
                                begin
                                  if array_dim_count <> 1 then
                                    FailParse();
                                  if HasStringTypeName() = false then
                                    begin
                                      StrCopy(saved_text, string_type_name);
                                      char_array_len := array_hi1 - array_lo1 + 1
                                    end
                                  else
                                    begin
                                      StrCopy(saved_text, string_type2_name);
                                      char_array_len2 := array_hi1 - array_lo1 + 1
                                    end;
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken()
                                end
                              else
                                begin
                                  if current_kind <> TOK_KW_INTEGER then
                                    FailParse();
                                  array_total_cells := array_hi1 - array_lo1 + 1;
                                  if array_dim_count >= 2 then
                                    array_total_cells := array_total_cells * (array_hi2 - array_lo2 + 1);
                                  if array_dim_count >= 3 then
                                    array_total_cells := array_total_cells * (array_hi3 - array_lo3 + 1);
                                  if array_dim_count >= 4 then
                                    array_total_cells := array_total_cells * (array_hi4 - array_lo4 + 1);
                                  StrCopy(saved_text, int_array_type_name);
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken()
                                end
                            end
                          else
                            begin
                              if HasStringTypeName() = false then
                                begin
                                  StrCopy(saved_text, string_type_name);
                                  char_array_len := array_lo1
                                end
                              else
                                begin
                                  StrCopy(saved_text, string_type2_name);
                                  char_array_len2 := array_lo1
                                end;
                              ExpectSymbolChar(']');
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_of) = false then
                                FailParse();
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_char) = false then
                                FailParse();
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken()
                            end
                        end
                      else
                        FailParse()
                    end
                  else if current_kind = TOK_SYMBOL then
                    begin
                      if current_text[0] = '(' then
                        begin
                          StrCopy(saved_text, enum_type_name);
                          ClearStr(enum_name0);
                          ClearStr(enum_name1);
                          ClearStr(enum_name2);
                          ClearStr(enum_name3);
                          ClearStr(enum_name4);
                          ClearStr(enum_name5);
                          ClearStr(enum_name6);
                          ClearStr(enum_name7);
                          set_mask_value := 0;
                          NextToken();
                          while current_kind = TOK_IDENT do
                            begin
                              if set_mask_value = 0 then
                                StrCopy(current_text, enum_name0)
                              else if set_mask_value = 1 then
                                StrCopy(current_text, enum_name1)
                              else if set_mask_value = 2 then
                                StrCopy(current_text, enum_name2)
                              else if set_mask_value = 3 then
                                StrCopy(current_text, enum_name3)
                              else if set_mask_value = 4 then
                                StrCopy(current_text, enum_name4)
                              else if set_mask_value = 5 then
                                StrCopy(current_text, enum_name5)
                              else if set_mask_value = 6 then
                                StrCopy(current_text, enum_name6)
                              else if set_mask_value = 7 then
                                StrCopy(current_text, enum_name7);
                              set_mask_value := set_mask_value + 1;
                              NextToken();
                              if current_kind = TOK_SYMBOL then
                                begin
                                  if current_text[0] = ',' then
                                    NextToken()
                                end
                            end;
                          ExpectSymbolChar(')');
                          NextToken();
                          ExpectSymbolChar(';');
                          NextToken()
                        end
                      else if current_text[0] = '^' then
                        begin
                          StrCopy(saved_text, pointer_type_name);
                          NextToken();
                          if current_kind <> TOK_IDENT then
                            begin
                              if current_kind <> TOK_KW_INTEGER then
                                FailParse()
                            end;
                          NextToken();
                          ExpectSymbolChar(';');
                          NextToken()
                        end
                      else
                        FailParse()
                    end
                  else if current_kind = TOK_INT then
                    begin
                      StrCopy(saved_text, subrange_type_name);
                      subrange_lo := current_value;
                      NextToken();
                      ExpectSymbolChar('.');
                      if current_text[1] <> '.' then
                        FailParse();
                      NextToken();
                      ExpectKind(TOK_INT);
                      subrange_hi := current_value;
                      NextToken();
                      ExpectSymbolChar(';');
                      NextToken()
                    end
                  else
                    begin
                      builtin_text := 'set';
                      if StrEqIgnoreCase(current_text, builtin_text) then
                        begin
                          StrCopy(saved_text, set_type_name);
                          NextToken();
                          builtin_text := 'of';
                          if StrEqIgnoreCase(current_text, builtin_text) = false then
                            FailParse();
                          NextToken();
                          ExpectKind(TOK_IDENT);
                          NextToken();
                          ExpectSymbolChar(';');
                          NextToken()
                        end
                      else
                        FailParse()
                    end
                end
            end
        end
    end
end;

(* Keep nested if/else in selfhost parser aligned with src/kpascal.pest:
   if <expr> then <stmt> (else <stmt>)?
   Use begin/end for multi-statement branches, and never emit end; else. *)
procedure ParseProcedureDeclGenericTail;
begin
  NextToken();
  if current_kind <> TOK_SYMBOL then
    begin
      FailParse()
    end
  else
    begin
      if current_text[0] = ';' then
        begin
          NextToken();
          ParseLocalVarSection();
          ExpectKind(TOK_KW_BEGIN);
          Write(': ');
          Write(proc_name);
          WriteLn('');
          NextToken();
          ParseStmtList();
          ExpectKind(TOK_KW_END);
          NextToken();
          WriteLn(';');
          ExpectSymbolChar(';');
          NextToken();
        end
      else
        begin
          ExpectSymbolChar('(');
          NextToken();
          if current_kind = TOK_SYMBOL then
            begin
              ExpectSymbolChar(')');
              NextToken();
              ExpectSymbolChar(';');
              NextToken();
              ParseLocalVarSection();
              ExpectKind(TOK_KW_BEGIN);
              Write(': ');
              Write(proc_name);
              WriteLn('');
              NextToken();
              ParseStmtList();
              ExpectKind(TOK_KW_END);
              NextToken();
              WriteLn(';');
              ExpectSymbolChar(';');
              NextToken();
            end
          else
            begin
              if current_kind = TOK_KW_VAR then
                begin
                  NextToken();
                  ExpectKind(TOK_IDENT);
                  StrCopy(current_text, proc_param);
                  Write('CREATE ');
                  Write(proc_param);
                  WriteLn(' 0 ,');
                  NextToken();
                  ExpectSymbolChar(':');
                  NextToken();
                  ExpectKind(TOK_KW_INTEGER);
                  NextToken();
                  ExpectSymbolChar(')');
                  NextToken();
                  ExpectSymbolChar(';');
                  NextToken();
                  ParseLocalVarSection();
                  ExpectKind(TOK_KW_BEGIN);
                  Write(': ');
                  Write(proc_name);
                  WriteLn('');
                  Write(proc_param);
                  WriteLn(' PVAR!');
                  NextToken();
                  ParseStmtList();
                  ExpectKind(TOK_KW_END);
                  NextToken();
                  WriteLn(';');
                  ExpectSymbolChar(';');
                  NextToken();
                end
              else
                begin
                  ExpectKind(TOK_IDENT);
                  NextToken();
                  ExpectSymbolChar(':');
                  NextToken();
                  if StrEqIgnoreCase(current_text, kw_array) = false then
                    FailParse();
                  conformant_proc_dims := 1;
                  NextToken();
                  ExpectSymbolChar('[');
                  NextToken();
                  ExpectKind(TOK_IDENT);
                  NextToken();
                  if current_text[0] <> '.' then
                    FailParse();
                  if current_text[1] <> '.' then
                    FailParse();
                  NextToken();
                  ExpectKind(TOK_IDENT);
                  NextToken();
                  ExpectSymbolChar(':');
                  NextToken();
                  ExpectKind(TOK_KW_INTEGER);
                  NextToken();
                  if current_text[0] = ';' then
                    begin
                      conformant_proc_dims := 2;
                      NextToken();
                      ExpectKind(TOK_IDENT);
                      NextToken();
                      if current_text[0] <> '.' then
                        FailParse();
                      if current_text[1] <> '.' then
                        FailParse();
                      NextToken();
                      ExpectKind(TOK_IDENT);
                      NextToken();
                      ExpectSymbolChar(':');
                      NextToken();
                      ExpectKind(TOK_KW_INTEGER);
                      NextToken();
                    end;
                  ExpectSymbolChar(']');
                  NextToken();
                  if StrEqIgnoreCase(current_text, kw_of) = false then
                    FailParse();
                  NextToken();
                  ExpectKind(TOK_KW_INTEGER);
                  NextToken();
                  ExpectSymbolChar(')');
                  NextToken();
                  ExpectSymbolChar(';');
                  NextToken();
                  EmitConformantArrayProcedure(0);
                  SkipRoutineBody()
                end
            end
        end
    end
end;

procedure ParseProcedureDecl;
var
  header_done: integer;
  cell_index: integer;
begin
  NextToken();
  ExpectKind(TOK_IDENT);
  StrCopy(current_text, proc_name);

  builtin_text := 'ClearStr';
					                                                      if StrEqIgnoreCase(proc_name, builtin_text) then
					                                                        begin
					                                                          NextToken();
      ExpectSymbolChar('(');
      header_done := 0;
      repeat
        NextToken();
        if current_kind = TOK_SYMBOL then
          begin
            if current_text[0] = ')' then
              header_done := 1
          end
      until header_done <> 0;
      ExpectSymbolChar(')');
      NextToken();
      ExpectSymbolChar(';');
      NextToken();
      EmitMiniClearStrRoutine();
      SkipRoutineBody();
      ClearStr(proc_name);
      ClearStr(proc_param);
      conformant_proc_dims := 0
    end
  else
    begin
      builtin_text := 'AppendChar';
      if StrEqIgnoreCase(proc_name, builtin_text) then
        begin
          NextToken();
          ExpectSymbolChar('(');
          header_done := 0;
          repeat
            NextToken();
            if current_kind = TOK_SYMBOL then
              begin
                if current_text[0] = ')' then
                  header_done := 1
              end
          until header_done <> 0;
          ExpectSymbolChar(')');
          NextToken();
          ExpectSymbolChar(';');
          NextToken();
          EmitMiniAppendCharRoutine();
          SkipRoutineBody();
          ClearStr(proc_name);
          ClearStr(proc_param);
          conformant_proc_dims := 0
        end
      else
        begin
          builtin_text := 'StrCopy';
          if StrEqIgnoreCase(proc_name, builtin_text) then
            begin
              NextToken();
              ExpectSymbolChar('(');
              header_done := 0;
              repeat
                NextToken();
                if current_kind = TOK_SYMBOL then
                  begin
                    if current_text[0] = ')' then
                      header_done := 1
                  end
              until header_done <> 0;
              ExpectSymbolChar(')');
              NextToken();
              ExpectSymbolChar(';');
              NextToken();
              EmitMiniStrCopyRoutine();
              SkipRoutineBody();
              ClearStr(proc_name);
              ClearStr(proc_param);
              conformant_proc_dims := 0
            end
          else
            begin
              builtin_text := 'SetSourceAt';
              if StrEqIgnoreCase(proc_name, builtin_text) then
                begin
                  NextToken();
                  ExpectSymbolChar('(');
                  header_done := 0;
                  repeat
                    NextToken();
                    if current_kind = TOK_SYMBOL then
                      begin
                        if current_text[0] = ')' then
                          header_done := 1
                      end
                  until header_done <> 0;
                  ExpectSymbolChar(')');
                  NextToken();
                  ExpectSymbolChar(';');
                  NextToken();
                  EmitRuntimeSetSourceAtRoutine();
                  SkipRoutineBody();
                  ClearStr(proc_name);
                  ClearStr(proc_param);
                  conformant_proc_dims := 0
                end
              else
                begin
	                  builtin_text := 'AdvanceChar';
	                  if StrEqIgnoreCase(proc_name, builtin_text) then
	                    begin
	                      NextToken();
	                      ExpectSymbolChar(';');
	                      NextToken();
	                      EmitRuntimeAdvanceCharRoutine();
	                      SkipRoutineBody();
	                      ClearStr(proc_name);
	                      ClearStr(proc_param);
	                      conformant_proc_dims := 0
	                    end
	                  else
	                    begin
	                      builtin_text := 'EmitCurrentWord';
	                      if StrEqIgnoreCase(proc_name, builtin_text) then
	                        begin
	                          NextToken();
	                          ExpectSymbolChar(';');
	                          NextToken();
	                          EmitRuntimeEmitCurrentWordRoutine();
	                          SkipRoutineBody();
	                          ClearStr(proc_name);
	                          ClearStr(proc_param);
	                          conformant_proc_dims := 0
	                        end
	                      else
	                        begin
		                          builtin_text := 'EmitSavedWord';
		                          if StrEqIgnoreCase(proc_name, builtin_text) then
		                            begin
		                              NextToken();
	                              ExpectSymbolChar(';');
	                              NextToken();
	                              EmitRuntimeEmitSavedWordRoutine();
	                              SkipRoutineBody();
	                              ClearStr(proc_name);
		                              ClearStr(proc_param);
		                              conformant_proc_dims := 0
		                            end
		                          else
		                            begin
		                              builtin_text := 'EmitCharLine';
		                              if StrEqIgnoreCase(proc_name, builtin_text) then
		                                begin
		                                  NextToken();
		                                  ExpectSymbolChar('(');
		                                  NextToken();
		                                  ExpectKind(TOK_IDENT);
		                                  NextToken();
		                                  ExpectSymbolChar(':');
		                                  NextToken();
		                                  if StrEqIgnoreCase(current_text, kw_char) = false then
		                                    FailParse();
		                                  NextToken();
		                                  ExpectSymbolChar(')');
		                                  NextToken();
		                                  ExpectSymbolChar(';');
		                                  NextToken();
		                                  EmitRuntimeEmitCharLineRoutine();
		                                  SkipRoutineBody();
		                                  ClearStr(proc_name);
		                                  ClearStr(proc_param);
		                                  conformant_proc_dims := 0
		                                end
		                              else
		                                begin
		                              builtin_text := 'EmitIntWord';
		                              if StrEqIgnoreCase(proc_name, builtin_text) then
		                                begin
		                                  NextToken();
	                                  ExpectSymbolChar('(');
	                                  NextToken();
	                                  ExpectKind(TOK_IDENT);
	                                  NextToken();
	                                  ExpectSymbolChar(':');
	                                  NextToken();
	                                  ExpectKind(TOK_KW_INTEGER);
	                                  NextToken();
	                                  ExpectSymbolChar(')');
	                                  NextToken();
	                                  ExpectSymbolChar(';');
	                                  NextToken();
	                                  EmitRuntimeEmitIntWordRoutine();
	                                  SkipRoutineBody();
	                                  ClearStr(proc_name);
		                                  ClearStr(proc_param);
		                                  conformant_proc_dims := 0
		                                end
		                              else
		                                begin
		                                  builtin_text := 'EmitStringHelpers';
		                                  if StrEqIgnoreCase(proc_name, builtin_text) then
		                                    begin
		                                      NextToken();
		                                      ExpectSymbolChar(';');
		                                      NextToken();
		                                      EmitRuntimeEmitStringHelpersRoutine();
		                                      SkipRoutineBody();
		                                      ClearStr(proc_name);
		                                      ClearStr(proc_param);
		                                      conformant_proc_dims := 0
		                                    end
		                                  else
		                                    begin
		                                      builtin_text := 'EmitExtendedStringHelpers';
		                                      if StrEqIgnoreCase(proc_name, builtin_text) then
		                                        begin
		                                          NextToken();
		                                          ExpectSymbolChar(';');
		                                          NextToken();
		                                          EmitRuntimeEmitExtendedStringHelpersRoutine();
		                                          SkipRoutineBody();
		                                          ClearStr(proc_name);
		                                  ClearStr(proc_param);
		                                  conformant_proc_dims := 0
		                                end
		                              else
		                                begin
		                                  builtin_text := 'EmitCurrentStringText';
		                                  if StrEqIgnoreCase(proc_name, builtin_text) then
		                                    begin
		                                      NextToken();
		                                      ExpectSymbolChar(';');
		                                      NextToken();
		                                      EmitRuntimeEmitCurrentStringTextRoutine();
		                                      SkipRoutineBody();
		                                      ClearStr(proc_name);
		                                      ClearStr(proc_param);
		                                      conformant_proc_dims := 0
		                                    end
		                                  else
		                                    begin
		                                      builtin_text := 'EmitStringWriteBody';
		                                      if StrEqIgnoreCase(proc_name, builtin_text) then
		                                        begin
		                                          NextToken();
		                                          ExpectSymbolChar(';');
		                                          NextToken();
		                                          EmitRuntimeEmitStringWriteBodyRoutine();
		                                          SkipRoutineBody();
		                                          ClearStr(proc_name);
		                                          ClearStr(proc_param);
		                                          conformant_proc_dims := 0
		                                        end
		                                      else
		                                        begin
		                                          builtin_text := 'EmitStringWrite';
		                                          if StrEqIgnoreCase(proc_name, builtin_text) then
		                                            begin
		                                              NextToken();
		                                              ExpectSymbolChar(';');
		                                              NextToken();
		                                              EmitRuntimeEmitStringWriteRoutine();
		                                              SkipRoutineBody();
		                                              ClearStr(proc_name);
		                                              ClearStr(proc_param);
		                                              conformant_proc_dims := 0
		                                            end
			                                          else
			                                            begin
			                                              builtin_text := 'EmitFieldRead';
			                                              if StrEqIgnoreCase(proc_name, builtin_text) then
			                                                begin
			                                                  NextToken();
			                                                  ExpectSymbolChar('(');
			                                                  header_done := 0;
			                                                  repeat
			                                                    NextToken();
			                                                    if current_kind = TOK_SYMBOL then
			                                                      begin
			                                                        if current_text[0] = ')' then
			                                                          header_done := 1
			                                                      end
			                                                  until header_done <> 0;
			                                                  ExpectSymbolChar(')');
			                                                  NextToken();
			                                                  ExpectSymbolChar(';');
			                                                  NextToken();
				                                                  EmitRuntimeEmitFieldReadRoutine();
				                                                  SkipRoutineBody();
				                                                  ClearStr(proc_name);
				                                                  ClearStr(proc_param);
				                                                  conformant_proc_dims := 0
				                                                end
				                                              else
				                                                begin
				                                                  builtin_text := 'EmitStringStore';
				                                                  if StrEqIgnoreCase(proc_name, builtin_text) then
				                                                    begin
				                                                      NextToken();
				                                                      ExpectSymbolChar(';');
				                                                      NextToken();
				                                                      EmitRuntimeEmitStringStoreRoutine();
				                                                      SkipRoutineBody();
				                                                      ClearStr(proc_name);
				                                                      ClearStr(proc_param);
				                                                      conformant_proc_dims := 0
				                                                    end
				                                                  else
				                                                    begin
				                                                      builtin_text := 'EmitSavedCaseString';
				                                                      if StrEqIgnoreCase(proc_name, builtin_text) then
				                                                        begin
				                                                          NextToken();
				                                                          ExpectSymbolChar(';');
				                                                          NextToken();
				                                                          EmitRuntimeEmitSavedCaseStringRoutine();
				                                                          SkipRoutineBody();
				                                                          ClearStr(proc_name);
				                                                          ClearStr(proc_param);
					                                                          conformant_proc_dims := 0
					                                                        end
					                                                      else
					                                                        begin
					                                                          builtin_text := 'EmitCreateCurrentVar';
					                                                          if StrEqIgnoreCase(proc_name, builtin_text) then
					                                                            begin
					                                                              NextToken();
					                                                              ExpectSymbolChar(';');
					                                                              NextToken();
					                                                              EmitRuntimeEmitCreateCurrentVarRoutine();
					                                                              SkipRoutineBody();
					                                                              ClearStr(proc_name);
					                                                              ClearStr(proc_param);
					                                                              conformant_proc_dims := 0
					                                                            end
					                                                          else
					                                                            begin
					                                                          builtin_text := 'EmitCreateCurrentRecordVar';
					                                                              if StrEqIgnoreCase(proc_name, builtin_text) then
					                                                                begin
					                                                                  NextToken();
					                                                                  ExpectSymbolChar(';');
					                                                                  NextToken();
					                                                                  EmitRuntimeEmitCreateCurrentRecordVarRoutine();
					                                                                  SkipRoutineBody();
					                                                                  ClearStr(proc_name);
					                                                                  ClearStr(proc_param);
					                                                                  conformant_proc_dims := 0
					                                                                end
					                                                              else
					                                                                begin
					                                                                  builtin_text := 'EmitConformantArrayProcedure';
                                                                  if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                    begin
                                                                      NextToken();
                                                                      ExpectSymbolChar('(');
                                                                      NextToken();
                                                                      ExpectKind(TOK_KW_INTEGER);
                                                                      NextToken();
                                                                      ExpectSymbolChar(')');
                                                                      NextToken();
                                                                      ExpectSymbolChar(';');
                                                                      NextToken();
                                                                      EmitRuntimeEmitConformantArrayProcedureRoutine();
                                                                      SkipRoutineBody();
                                                                      ClearStr(proc_name);
					                                                                      ClearStr(proc_param);
					                                                                      conformant_proc_dims := 0
					                                                                    end
					                                                                  else
					                                                                    begin
					                      builtin_text := 'EmitVariantHelpers';
					                      if StrEqIgnoreCase(proc_name, builtin_text) then
					                        begin
		                          NextToken();
	                          ExpectSymbolChar(';');
	                          NextToken();
	                          EmitRuntimeEmitVariantHelpersRoutine();
	                          SkipRoutineBody();
	                          ClearStr(proc_name);
	                          ClearStr(proc_param);
		                          conformant_proc_dims := 0
		                        end
		                      else
		                        begin
		                      builtin_text := 'SkipSpaces';
	                      if StrEqIgnoreCase(proc_name, builtin_text) then
	                        begin
                          NextToken();
                          ExpectSymbolChar(';');
                          NextToken();
                          EmitRuntimeSkipSpacesRoutine();
                          SkipRoutineBody();
                          ClearStr(proc_name);
                          ClearStr(proc_param);
                          conformant_proc_dims := 0
                        end
                      else
                        begin
                          builtin_text := 'ReadIdentifier';
                          if StrEqIgnoreCase(proc_name, builtin_text) then
                            begin
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              EmitRuntimeReadIdentifierRoutine();
                              SkipRoutineBody();
                              ClearStr(proc_name);
                              ClearStr(proc_param);
                              conformant_proc_dims := 0
                            end
                          else
                            begin
                              builtin_text := 'ResolveCurrentEnumOrdinal';
                              if StrEqIgnoreCase(proc_name, builtin_text) then
                                begin
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken();
                                  EmitRuntimeResolveCurrentEnumOrdinalRoutine();
                                  SkipRoutineBody();
                                  ClearStr(proc_name);
                                  ClearStr(proc_param);
                                  conformant_proc_dims := 0
                                end
                              else
                                begin
                                  builtin_text := 'ResolveSavedEnumOrdinal';
                                  if StrEqIgnoreCase(proc_name, builtin_text) then
                                    begin
                                      NextToken();
                                      ExpectSymbolChar(';');
                                      NextToken();
                                      EmitRuntimeResolveSavedEnumOrdinalRoutine();
                                      SkipRoutineBody();
                                      ClearStr(proc_name);
                                      ClearStr(proc_param);
                                      conformant_proc_dims := 0
                                    end
                                  else
                                    begin
                              builtin_text := 'EmitVariantTagCheck';
                              if StrEqIgnoreCase(proc_name, builtin_text) then
                                begin
                                  NextToken();
                                  ExpectSymbolChar('(');
                                  header_done := 0;
                                  repeat
                                    NextToken();
                                    if current_kind = TOK_SYMBOL then
                                      begin
                                        if current_text[0] = ')' then
                                          header_done := 1
                                      end
                                  until header_done <> 0;
                                  ExpectSymbolChar(')');
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken();
                                  EmitRuntimeEmitVariantTagCheckRoutine();
                                  SkipRoutineBody();
                                  ClearStr(proc_name);
                                  ClearStr(proc_param);
                                  conformant_proc_dims := 0
                                end
                              else
                                begin
                                  builtin_text := 'ReadString';
                                  if StrEqIgnoreCase(proc_name, builtin_text) then
                                    begin
                                      NextToken();
                                      ExpectSymbolChar(';');
                                      NextToken();
                                      EmitRuntimeReadStringRoutine();
                                      SkipRoutineBody();
                                      ClearStr(proc_name);
                                      ClearStr(proc_param);
                                      conformant_proc_dims := 0
                                    end
                                  else
                                    begin
                                      builtin_text := 'ReadNumber';
                                      if StrEqIgnoreCase(proc_name, builtin_text) then
                                        begin
                                          NextToken();
                                          ExpectSymbolChar(';');
                                          NextToken();
                                          EmitRuntimeReadNumberRoutine();
                                          SkipRoutineBody();
                                          ClearStr(proc_name);
                                          ClearStr(proc_param);
                                          conformant_proc_dims := 0
                                        end
                                      else
                                        begin
                                          builtin_text := 'ReadSymbol';
                                          if StrEqIgnoreCase(proc_name, builtin_text) then
                                            begin
                                              NextToken();
                                              ExpectSymbolChar(';');
                                              NextToken();
                                              EmitRuntimeReadSymbolRoutine();
                                              SkipRoutineBody();
                                              ClearStr(proc_name);
                                              ClearStr(proc_param);
                                              conformant_proc_dims := 0
                                            end
                                          else
                                            begin
                                              builtin_text := 'NextToken';
                                              if StrEqIgnoreCase(proc_name, builtin_text) then
                                                begin
                                                  NextToken();
                                                  ExpectSymbolChar(';');
                                                  NextToken();
                                                  EmitRuntimeNextTokenRoutine();
                                                  SkipRoutineBody();
                                                  ClearStr(proc_name);
                                                  ClearStr(proc_param);
                                                  conformant_proc_dims := 0
                                                end
                                              else
                                                begin
                                                  builtin_text := 'WriteToken';
                                                  if StrEqIgnoreCase(proc_name, builtin_text) then
                                                    begin
                                                      NextToken();
                                                      ExpectSymbolChar(';');
                                                      NextToken();
                                                      EmitRuntimeWriteTokenRoutine();
                                                      SkipRoutineBody();
                                                      ClearStr(proc_name);
                                                      ClearStr(proc_param);
                                                      conformant_proc_dims := 0
                                                    end
                                                  else
                                                    begin
                                                      builtin_text := 'ExpectKind';
                                                      if StrEqIgnoreCase(proc_name, builtin_text) then
                                                        begin
                                                          NextToken();
                                                          ExpectSymbolChar('(');
                                                          NextToken();
                                                          ExpectKind(TOK_IDENT);
                                                          NextToken();
                                                          ExpectSymbolChar(':');
                                                          NextToken();
                                                          ExpectKind(TOK_KW_INTEGER);
                                                          NextToken();
                                                          ExpectSymbolChar(')');
                                                          NextToken();
                                                          ExpectSymbolChar(';');
                                                          NextToken();
                                                          EmitRuntimeExpectKindRoutine();
                                                          SkipRoutineBody();
                                                          ClearStr(proc_name);
                                                          ClearStr(proc_param);
                                                          conformant_proc_dims := 0
                                                        end
                                                      else
                                                        begin
                                                          builtin_text := 'ExpectAssignSymbol';
                                                          if StrEqIgnoreCase(proc_name, builtin_text) then
                                                            begin
                                                              NextToken();
                                                              ExpectSymbolChar(';');
                                                              NextToken();
                                                              EmitRuntimeExpectAssignSymbolRoutine();
                                                              SkipRoutineBody();
                                                              ClearStr(proc_name);
                                                              ClearStr(proc_param);
                                                              conformant_proc_dims := 0
                                                            end
                                                          else
                                                            begin
                                                              builtin_text := 'ParseRealLiteral';
                                                              if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                begin
                                                                  NextToken();
                                                                  ExpectSymbolChar(';');
                                                                  NextToken();
                                                                  EmitRuntimeParseRealLiteralRoutine();
                                                                  SkipRoutineBody();
                                                                  ClearStr(proc_name);
                                                                  ClearStr(proc_param);
                                                                  conformant_proc_dims := 0
                                                                end
                                                              else
                                                                begin
                                                                  builtin_text := 'ParseRealExpr';
                                                                  if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                    begin
                                                                      NextToken();
                                                                      ExpectSymbolChar(';');
                                                                      NextToken();
                                                                      EmitRuntimeParseRealExprRoutine();
                                                                      SkipRoutineBody();
                                                                      ClearStr(proc_name);
                                                                      ClearStr(proc_param);
                                                                      conformant_proc_dims := 0
                                                                    end
                                                                  else
                                                                    begin
                                                                      builtin_text := 'ParseSetLiteral';
                                                                      if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                        begin
                                                                          NextToken();
                                                                          ExpectSymbolChar(';');
                                                                          NextToken();
                                                                          EmitRuntimeParseSetLiteralRoutine();
                                                                          SkipRoutineBody();
                                                                          ClearStr(proc_name);
                                                                          ClearStr(proc_param);
                                                                          conformant_proc_dims := 0
                                                                        end
                                                                      else
                                                                        begin
                                                                          builtin_text := 'ParseCondition';
                                                                          if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                            begin
                                                                              NextToken();
                                                                              ExpectSymbolChar(';');
                                                                              NextToken();
                                                                              EmitRuntimeParseConditionRoutine();
                                                                              SkipRoutineBody();
                                                                              ClearStr(proc_name);
                                                                              ClearStr(proc_param);
                                                                              conformant_proc_dims := 0
                                                                            end
                                                                          else
                                                                            begin
                                                                              builtin_text := 'ParseArrayIndexes';
                                                                              if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                                begin
                                                                                  NextToken();
                                                                                  ExpectSymbolChar('(');
                                                                                  NextToken();
                                                                                  ExpectKind(TOK_KW_VAR);
                                                                                  NextToken();
                                                                                  ExpectKind(TOK_IDENT);
                                                                                  NextToken();
                                                                                  ExpectSymbolChar(':');
                                                                                  NextToken();
                                                                                  ExpectKind(TOK_IDENT);
                                                                                  NextToken();
                                                                                  ExpectSymbolChar(')');
                                                                                  NextToken();
                                                                                  ExpectSymbolChar(';');
                                                                                  NextToken();
                                                                                  EmitRuntimeParseArrayIndexesRoutine();
                                                                                  SkipRoutineBody();
                                                                                  ClearStr(proc_name);
                                                                                  ClearStr(proc_param);
                                                                                  conformant_proc_dims := 0
                                                                                end
                                                                              else
                                                                                begin
                                                                                  builtin_text := 'ParseTerm';
                                                                                  if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                                    begin
                                                                                      NextToken();
                                                                                      ExpectSymbolChar(';');
                                                                                      NextToken();
                                                                                      EmitRuntimeParseTermRoutine();
                                                                                      SkipRoutineBody();
                                                                                      ClearStr(proc_name);
                                                                                      ClearStr(proc_param);
                                                                                      conformant_proc_dims := 0
                                                                                    end
                                                                                  else
                                                                                    begin
                                                                                      builtin_text := 'ParseSimpleExpr';
                                                                                      if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                                        begin
                                                                                          NextToken();
                                                                                          ExpectSymbolChar(';');
                                                                                          NextToken();
                                                                                          EmitRuntimeParseSimpleExprRoutine();
                                                                                          SkipRoutineBody();
                                                                                          ClearStr(proc_name);
                                                                                          ClearStr(proc_param);
                                                                                          conformant_proc_dims := 0
                                                                                        end
                                                                                      else
                                                                                        begin
                                                                                          builtin_text := 'ParseFactorLiteral';
                                                                                          if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                                            begin
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(';');
                                                                                              NextToken();
                                                                                              EmitRuntimeParseFactorLiteralRoutine();
                                                                                              SkipRoutineBody();
                                                                                              ClearStr(proc_name);
                                                                                              ClearStr(proc_param);
                                                                                              conformant_proc_dims := 0
                                                                                            end
                                                                                          else
                                                                                            begin
                                                                                          builtin_text := 'ParseStringIndexAddress';
                                                                                          if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                                            begin
                                                                                              NextToken();
                                                                                              ExpectSymbolChar('(');
                                                                                              NextToken();
                                                                                              ExpectKind(TOK_KW_VAR);
                                                                                              NextToken();
                                                                                              ExpectKind(TOK_IDENT);
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(':');
                                                                                              NextToken();
                                                                                              ExpectKind(TOK_IDENT);
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(')');
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(';');
                                                                                              NextToken();
                                                                                              EmitRuntimeParseStringIndexAddressRoutine();
                                                                                              SkipRoutineBody();
                                                                                              ClearStr(proc_name);
                                                                                              ClearStr(proc_param);
                                                                                              conformant_proc_dims := 0
                                                                                            end
                                                                                          else
                                                                                            begin
                                                                                          builtin_text := 'ExpectSymbolChar';
                                                                                          if StrEqIgnoreCase(proc_name, builtin_text) then
                                                                                            begin
                                                                                              NextToken();
                                                                                              ExpectSymbolChar('(');
                                                                                              NextToken();
                                                                                              ExpectKind(TOK_IDENT);
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(':');
                                                                                              NextToken();
                                                                                              if StrEqIgnoreCase(current_text, kw_char) = false then
                                                                                                FailParse();
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(')');
                                                                                              NextToken();
                                                                                              ExpectSymbolChar(';');
                                                                                              NextToken();
                                                                                              EmitRuntimeExpectSymbolCharRoutine();
                                                                                              SkipRoutineBody();
                                                                                              ClearStr(proc_name);
                                                                                              ClearStr(proc_param);
                                                                                              conformant_proc_dims := 0
                                                                                            end
                                                                                          else
                                                                                            begin
                                                                                              ParseProcedureDeclGenericTail();
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                            end
                                                                        end
                                                                        end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                        end
                    end
                end
                                            end
                                        end
                                    end
                                end
                                end
                                                    end
                                                end
                                            end
                                        end
                                        end
                                    end
                                end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
        end
    end
        end
    end
        end
    end
end;

procedure SkipFunctionHeaderToRightParen(var header_done: integer);
begin
  header_done := 0;
  repeat
    NextToken();
    if current_kind = TOK_SYMBOL then
      begin
        if current_text[0] = ')' then
          header_done := 1
      end
  until header_done <> 0
end;

procedure FinishBooleanFunctionDeclHeader;
begin
  ExpectSymbolChar(':');
  NextToken();
  NextToken();
  ExpectSymbolChar(';');
  NextToken()
end;

procedure FinishIntegerFunctionDeclHeader;
begin
  ExpectSymbolChar(':');
  NextToken();
  ExpectKind(TOK_KW_INTEGER);
  NextToken();
  ExpectSymbolChar(';');
  NextToken()
end;

procedure FinishZeroArgBooleanFunctionDeclHeader;
begin
  ExpectSymbolChar(':');
  NextToken();
  NextToken();
  ExpectSymbolChar(';');
  NextToken()
end;

procedure FinishParenBooleanFunctionDeclHeader(var header_done: integer);
begin
  NextToken();
  ExpectSymbolChar('(');
  SkipFunctionHeaderToRightParen(header_done);
  ExpectSymbolChar(')');
  NextToken();
  FinishBooleanFunctionDeclHeader()
end;

procedure FinishParenIntegerFunctionDeclHeader(var header_done: integer);
begin
  NextToken();
  ExpectSymbolChar('(');
  SkipFunctionHeaderToRightParen(header_done);
  ExpectSymbolChar(')');
  NextToken();
  FinishIntegerFunctionDeclHeader()
end;

procedure CompleteFunctionSpecialCase;
begin
  SkipRoutineBody();
  ClearStr(func_name);
  ClearStr(func_param)
end;

procedure ParseFunctionDecl;
var
  header_done: integer;
  generic_param_is_lexeme: integer;
begin
  generic_param_is_lexeme := 0;
  NextToken();
  ExpectKind(TOK_IDENT);
  StrCopy(current_text, func_name);

  builtin_text := 'StrEqIgnoreCase';
  if StrEqIgnoreCase(func_name, builtin_text) then
    begin
      NextToken();
      ExpectSymbolChar('(');
      SkipFunctionHeaderToRightParen(header_done);
      ExpectSymbolChar(')');
      NextToken();
      FinishBooleanFunctionDeclHeader();
      EmitMiniStrEqIgnoreCaseRoutine();
      CompleteFunctionSpecialCase()
    end
  else
    begin
      builtin_text := 'IsLetter';
      if StrEqIgnoreCase(func_name, builtin_text) then
        begin
          NextToken();
          ExpectSymbolChar('(');
          SkipFunctionHeaderToRightParen(header_done);
          ExpectSymbolChar(')');
          NextToken();
          FinishBooleanFunctionDeclHeader();
          EmitRuntimeIsLetterRoutine();
          CompleteFunctionSpecialCase()
        end
      else
        begin
          builtin_text := 'IsDigit';
          if StrEqIgnoreCase(func_name, builtin_text) then
            begin
              NextToken();
              ExpectSymbolChar('(');
              SkipFunctionHeaderToRightParen(header_done);
              ExpectSymbolChar(')');
              NextToken();
              FinishBooleanFunctionDeclHeader();
              EmitRuntimeIsDigitRoutine();
              CompleteFunctionSpecialCase()
            end
          else
            begin
              builtin_text := 'IsIdentChar';
              if StrEqIgnoreCase(func_name, builtin_text) then
                begin
                  NextToken();
                  ExpectSymbolChar('(');
                  SkipFunctionHeaderToRightParen(header_done);
                  ExpectSymbolChar(')');
                  NextToken();
                  FinishBooleanFunctionDeclHeader();
                  EmitRuntimeIsIdentCharRoutine();
                  CompleteFunctionSpecialCase()
                end
              else
                begin
                  builtin_text := 'IsSpace';
                  if StrEqIgnoreCase(func_name, builtin_text) then
                    begin
                      NextToken();
                      ExpectSymbolChar('(');
                      SkipFunctionHeaderToRightParen(header_done);
                      ExpectSymbolChar(')');
                      NextToken();
                      FinishBooleanFunctionDeclHeader();
                      EmitRuntimeIsSpaceRoutine();
                      CompleteFunctionSpecialCase()
                    end
                  else
                    begin
                      builtin_text := 'MatchPair';
                      if StrEqIgnoreCase(func_name, builtin_text) then
                        begin
                          NextToken();
                          ExpectSymbolChar('(');
                          SkipFunctionHeaderToRightParen(header_done);
                          ExpectSymbolChar(')');
                          NextToken();
                          FinishBooleanFunctionDeclHeader();
                          EmitRuntimeMatchPairRoutine();
                          CompleteFunctionSpecialCase()
                        end
                      else
                        begin
                          builtin_text := 'SourceAt';
                          if StrEqIgnoreCase(func_name, builtin_text) then
                            begin
                              NextToken();
                              ExpectSymbolChar('(');
                              NextToken();
                              ExpectKind(TOK_IDENT);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              ExpectKind(TOK_KW_INTEGER);
                              NextToken();
                              ExpectSymbolChar(')');
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              if StrEqIgnoreCase(current_text, kw_char) = false then
                                FailParse();
                              NextToken();
                              ExpectSymbolChar(';');
                              NextToken();
                              EmitRuntimeSourceAtRoutine();
                              CompleteFunctionSpecialCase()
                            end
                          else
                            begin
                              builtin_text := 'HasName';
                              if StrEqIgnoreCase(func_name, builtin_text) then
                                begin
                                  NextToken();
                                  ExpectSymbolChar('(');
                                  SkipFunctionHeaderToRightParen(header_done);
                                  ExpectSymbolChar(')');
                                  NextToken();
                                  FinishBooleanFunctionDeclHeader();
                                  EmitRuntimeHasNameRoutine();
                                  CompleteFunctionSpecialCase()
                                end
                              else
                                begin
                                  builtin_text := 'HasRecordVarName';
                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                    begin
                                      NextToken();
                                      ExpectSymbolChar(':');
                                      NextToken();
                                      NextToken();
                                      ExpectSymbolChar(';');
                                      NextToken();
                                      EmitRuntimeHasRecordVarNameRoutine();
                                      CompleteFunctionSpecialCase()
                                    end
                                  else
                                    begin
                                      builtin_text := 'IsSavedRecordVarName';
                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                        begin
                                          NextToken();
                                          ExpectSymbolChar(':');
                                          NextToken();
                                          NextToken();
                                          ExpectSymbolChar(';');
                                          NextToken();
                                          EmitRuntimeIsSavedRecordVarNameRoutine();
                                          CompleteFunctionSpecialCase()
                                        end
                                      else
                                        begin
                                          builtin_text := 'HasEnumVarName';
                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                            begin
                                              NextToken();
                                              ExpectSymbolChar(':');
                                              NextToken();
                                              NextToken();
                                              ExpectSymbolChar(';');
                                              NextToken();
                                              EmitRuntimeHasEnumVarNameRoutine();
                                              CompleteFunctionSpecialCase()
                                            end
                                          else
                                            begin
                                              builtin_text := 'HasSubrangeVarName';
                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                begin
                                                  NextToken();
                                                  ExpectSymbolChar(':');
                                                  NextToken();
                                                  NextToken();
                                                  ExpectSymbolChar(';');
                                                  NextToken();
                                                  EmitRuntimeHasSubrangeVarNameRoutine();
                                                  CompleteFunctionSpecialCase()
                                                end
                                              else
                                                begin
                                              builtin_text := 'HasRealVarName';
                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                begin
                                                  NextToken();
                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                  EmitRuntimeHasRealVarNameRoutine();
                                                  CompleteFunctionSpecialCase()
                                                end
                                              else
                                                begin
                                                  builtin_text := 'HasEnumTypeName';
                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                    begin
                                                      NextToken();
                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                      EmitRuntimeHasEnumTypeNameRoutine();
                                                      CompleteFunctionSpecialCase()
                                                    end
                                                  else
                                                    begin
                                                      builtin_text := 'HasSetTypeName';
                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                        begin
                                                          NextToken();
                                                          FinishZeroArgBooleanFunctionDeclHeader();
                                                          EmitRuntimeHasSetTypeNameRoutine();
                                                          CompleteFunctionSpecialCase()
                                                        end
                                                      else
                                                        begin
                                                          builtin_text := 'HasSubrangeTypeName';
                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                            begin
                                                              NextToken();
                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                              EmitRuntimeHasSubrangeTypeNameRoutine();
                                                              CompleteFunctionSpecialCase()
                                                            end
                                                          else
                                                            begin
                                                              builtin_text := 'HasRecordTypeName';
                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                begin
                                                                  NextToken();
                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                  EmitRuntimeHasRecordTypeNameRoutine();
                                                                  CompleteFunctionSpecialCase()
                                                                end
                                                              else
                                                                begin
                                                                  builtin_text := 'HasStringTypeName';
                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                    begin
                                                                      NextToken();
                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                      EmitRuntimeHasStringTypeNameRoutine();
                                                                      CompleteFunctionSpecialCase()
                                                                    end
                                                                  else
                                                                    begin
                                                                      builtin_text := 'HasStringType2Name';
                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                        begin
                                                                          NextToken();
                                                                          FinishZeroArgBooleanFunctionDeclHeader();
                                                                          EmitRuntimeHasStringType2NameRoutine();
                                                                          CompleteFunctionSpecialCase()
                                                                        end
                                                                      else
                                                                        begin
                                                                          builtin_text := 'HasIntArrayTypeName';
                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                            begin
                                                                              NextToken();
                                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                                              EmitRuntimeHasIntArrayTypeNameRoutine();
                                                                              CompleteFunctionSpecialCase()
                                                                            end
                                                                          else
                                                                            begin
                                                                              builtin_text := 'HasIntArrayVarName';
                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                begin
                                                                                  NextToken();
                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                  EmitRuntimeHasIntArrayVarNameRoutine();
                                                                                  CompleteFunctionSpecialCase()
                                                                                end
                                                                              else
                                                                                begin
                                                                                  builtin_text := 'ResolveKeywordToken';
                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                    begin
                                                                                      FinishParenIntegerFunctionDeclHeader(header_done);
                                                                                      EmitRuntimeResolveKeywordTokenRoutine();
                                                                                      CompleteFunctionSpecialCase()
                                                                                    end
                                                                                  else
                                                                                    begin
                                                                                  builtin_text := 'IsIntArrayVar';
                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                    begin
                                                                                      FinishParenBooleanFunctionDeclHeader(header_done);
                                                                                      EmitRuntimeIsIntArrayVarRoutine();
                                                                                      CompleteFunctionSpecialCase()
                                                                                    end
                                                                                  else
                                                                                    begin
                                                                                      builtin_text := 'IsPointerVar';
                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                        begin
                                                                                          FinishParenBooleanFunctionDeclHeader(header_done);
                                                                                          EmitRuntimeIsPointerVarRoutine();
                                                                                          CompleteFunctionSpecialCase()
                                                                                        end
                                                                                      else
                                                                                        begin
                                                                                          builtin_text := 'IsStringVar';
                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                            begin
                                                                                              FinishParenBooleanFunctionDeclHeader(header_done);
                                                                                              EmitRuntimeIsStringVarRoutine();
                                                                                              CompleteFunctionSpecialCase()
                                                                                            end
                                                                                          else
                                                                                            begin
                                                                                              builtin_text := 'IsSetVar';
                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                begin
                                                                                                  FinishParenBooleanFunctionDeclHeader(header_done);
                                                                                                  EmitRuntimeIsSetVarRoutine();
                                                                                                  CompleteFunctionSpecialCase()
                                                                                                end
                                                                                              else
                                                                                                begin
                                                                                                  builtin_text := 'AssignTargetIsSetVar';
                                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                    begin
                                                                                                      NextToken();
                                                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                      EmitRuntimeAssignTargetIsSetVarRoutine();
                                                                                                      CompleteFunctionSpecialCase()
                                                                                                    end
                                                                                                  else
                                                                                                    begin
                                                                                                      builtin_text := 'ResolveEnumOrdinal';
                                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                        begin
                                                                                                          FinishParenIntegerFunctionDeclHeader(header_done);
                                                                                                          EmitRuntimeResolveEnumOrdinalRoutine();
                                                                                                          CompleteFunctionSpecialCase()
                                                                                                        end
                                                                                                      else
                                                                                                        begin
                                                                                                          builtin_text := 'IsExactReadName';
                                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                            begin
                                                                                                              NextToken();
                                                                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                              EmitRuntimeIsExactReadNameRoutine();
                                                                                                              CompleteFunctionSpecialCase()
                                                                                                            end
                                                                                                          else
                                                                                                            begin
                                                                                                              builtin_text := 'IsExactWriteLnName';
                                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                begin
                                                                                                                  NextToken();
                                                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                  EmitRuntimeIsExactWriteLnNameRoutine();
                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                end
                                                                                                              else
                                                                                                                begin
                                                                                                                  builtin_text := 'IsExactWithName';
                                                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                    begin
                                                                                                                      NextToken();
                                                                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                      EmitRuntimeIsExactWithNameRoutine();
                                                                                                                      CompleteFunctionSpecialCase()
                                                                                                                    end
                                                                                                                  else
                                                                                                                    begin
                                                                                                                      builtin_text := 'IsExactConcatName';
                                                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                        begin
                                                                                                                                  NextToken();
                                                                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                  EmitRuntimeIsExactConcatNameRoutine();
                                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                        end
                                                                                                                      else
                                                                                                                        begin
                                                                                                                          builtin_text := 'IsExactDeleteName';
                                                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                            begin
                                                                                                                              NextToken();
                                                                                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                              EmitRuntimeIsExactDeleteNameRoutine();
                                                                                                                              CompleteFunctionSpecialCase()
                                                                                                                            end
                                                                                                                          else
                                                                                                                            begin
                                                                                                                              builtin_text := 'IsExactInsertName';
                                                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                begin
                                                                                                                                  NextToken();
                                                                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                  EmitRuntimeIsExactInsertNameRoutine();
                                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                                end
                                                                                                                              else
                                                                                                                                begin
                                                                                                                                  builtin_text := 'IsExactIntToHexName';
                                                                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                    begin
                                                                                                                                      NextToken();
                                                                                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                      EmitRuntimeIsExactIntToHexNameRoutine();
                                                                                                                                      CompleteFunctionSpecialCase()
                                                                                                                                    end
                                                                                                                                  else
                                                                                                                                    begin
                                                                                                                                      builtin_text := 'IsExactNewName';
                                                                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                        begin
                                                                                                                                          NextToken();
                                                                                                                                          FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                          EmitRuntimeIsExactNewNameRoutine();
                                                                                                                                          CompleteFunctionSpecialCase()
                                                                                                                                        end
                                                                                                                                      else
                                                                                                                                        begin
                                                                                                                                          builtin_text := 'IsExactDisposeName';
                                                                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                            begin
                                                                                                                                              NextToken();
                                                                                                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                              EmitRuntimeIsExactDisposeNameRoutine();
                                                                                                                                              CompleteFunctionSpecialCase()
                                                                                                                                            end
                                                                                                                                          else
                                                                                                                                            begin
                                                                                                                                              builtin_text := 'IsExactSetAddrName';
                                                                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                begin
                                                                                                                                                  NextToken();
                                                                                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                  EmitRuntimeIsExactSetAddrNameRoutine();
                                                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                                                end
                                                                                                                                              else
                                                                                                                                                begin
                                                                                                                                                  builtin_text := 'IsExactRoundName';
                                                                                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                    begin
                                                                                                                                                      NextToken();
                                                                                                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                      EmitRuntimeIsExactRoundNameRoutine();
                                                                                                                                                      CompleteFunctionSpecialCase()
                                                                                                                                                    end
                                                                                                                                                  else
                                                                                                                                                    begin
                                                                                                                                                      builtin_text := 'IsExactAbsName';
                                                                                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                        begin
                                                                                                                                                          NextToken();
                                                                                                                                                          FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                          EmitRuntimeIsExactAbsNameRoutine();
                                                                                                                                                          CompleteFunctionSpecialCase()
                                                                                                                                                        end
                                                                                                                                                      else
                                                                                                                                                        begin
                                                                                                                                                          builtin_text := 'IsExactSqrName';
                                                                                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                            begin
                                                                                                                                                              NextToken();
                                                                                                                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                              EmitRuntimeIsExactSqrNameRoutine();
                                                                                                                                                              CompleteFunctionSpecialCase()
                                                                                                                                                            end
                                                                                                                                                          else
                                                                                                                                                            begin
                                                                                                                                                              builtin_text := 'IsExactOddName';
                                                                                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                begin
                                                                                                                                                                  NextToken();
                                                                                                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                                  EmitRuntimeIsExactOddNameRoutine();
                                                                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                                                                end
                                                                                                                                                              else
                                                                                                                                                                begin
                                                                                                                                                                  builtin_text := 'IsExactUpCaseName';
                                                                                                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                    begin
                                                                                                                                                                      NextToken();
                                                                                                                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                                      EmitRuntimeIsExactUpCaseNameRoutine();
                                                                                                                                                                      CompleteFunctionSpecialCase()
                                                                                                                                                                    end
                                                                                                                                                                  else
                                                                                                                                                                    begin
                                                                                                                                                                      builtin_text := 'IsExactOrdName';
                                                                                                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                        begin
                                                                                                                                                                          NextToken();
                                                                                                                                                                          FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                                          EmitRuntimeIsExactOrdNameRoutine();
                                                                                                                                                                          CompleteFunctionSpecialCase()
                                                                                                                                                                        end
                                                                                                                                                                      else
                                                                                                                                                                        begin
                                                                                                                                                                          builtin_text := 'IsExactTruncName';
                                                                                                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                            begin
                                                                                                                                                                              NextToken();
                                                                                                                                                                              FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                                              EmitRuntimeIsExactTruncNameRoutine();
                                                                                                                                                                              CompleteFunctionSpecialCase()
                                                                                                                                                                            end
                                                                                                                                                                          else
                                                                                                                                                                            begin
                                                                                                                                                                              builtin_text := 'IsExactPosName';
                                                                                                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                                begin
                                                                                                                                                                                  NextToken();
                                                                                                                                                                                  FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                                                  EmitRuntimeIsExactPosNameRoutine();
                                                                                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                                                                                end
                                                                                                                                                                              else
                                                                                                                                                                                begin
                                                                                                                                                                                  builtin_text := 'IsExactHexToIntName';
                                                                                                                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                                    begin
                                                                                                                                                                                      NextToken();
                                                                                                                                                                                      FinishZeroArgBooleanFunctionDeclHeader();
                                                                                                                                                                                      EmitRuntimeIsExactHexToIntNameRoutine();
                                                                                                                                                                                      CompleteFunctionSpecialCase()
                                                                                                                                                                                    end
                                                                                                                                                                                  else
                                                                                                                                                                                    begin
                                                                                                                                                                                      builtin_text := 'EnumBit';
                                                                                                                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                                        begin
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectSymbolChar('(');
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectKind(TOK_IDENT);
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectSymbolChar(':');
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectKind(TOK_KW_INTEGER);
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectSymbolChar(')');
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectSymbolChar(':');
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectKind(TOK_KW_INTEGER);
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          ExpectSymbolChar(';');
                                                                                                                                                                                          NextToken();
                                                                                                                                                                                          EmitRuntimeEnumBitRoutine();
                                                                                                                                                                                          CompleteFunctionSpecialCase()
                                                                                                                                                                                        end
                                                                                                                                                                                      else
                                                                                                                                                                                        begin
                                                                                                                                                                                          builtin_text := 'ArrayStride';
                                                                                                                                                                                          if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                                            begin
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectSymbolChar('(');
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectKind(TOK_IDENT);
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectSymbolChar(':');
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectKind(TOK_KW_INTEGER);
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectSymbolChar(')');
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectSymbolChar(':');
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectKind(TOK_KW_INTEGER);
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              ExpectSymbolChar(';');
                                                                                                                                                                                              NextToken();
                                                                                                                                                                                              EmitRuntimeArrayStrideRoutine();
                                                                                                                                                                                              CompleteFunctionSpecialCase()
                                                                                                                                                                                            end
                                                                                                                                                                                          else
                                                                                                                                                                                            begin
                                                                                                                                                                                              builtin_text := 'ArrayLowerBound';
                                                                                                                                                                                              if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                                                                                                                                begin
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectSymbolChar('(');
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectKind(TOK_IDENT);
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectSymbolChar(':');
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectKind(TOK_KW_INTEGER);
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectSymbolChar(')');
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectSymbolChar(':');
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectKind(TOK_KW_INTEGER);
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  ExpectSymbolChar(';');
                                                                                                                                                                                                  NextToken();
                                                                                                                                                                                                  EmitRuntimeArrayLowerBoundRoutine();
                                                                                                                                                                                                  CompleteFunctionSpecialCase()
                                                                                                                                                                                                end
                                                                                                                                                                                              else
                                                                                                                                                                                                begin
                                                                                  builtin_text := 'ResolveFieldOffset';
                                                                                  if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                    begin
                                                                                      FinishParenIntegerFunctionDeclHeader(header_done);
                                                                                      EmitRuntimeResolveFieldOffsetRoutine();
                                                                                      CompleteFunctionSpecialCase()
                                                                                    end
                                                                                  else
                                                                                    begin
                                                                                      builtin_text := 'ResolveVariantExpectedTag';
                                                                                      if StrEqIgnoreCase(func_name, builtin_text) then
                                                                                        begin
                                                                                          FinishParenIntegerFunctionDeclHeader(header_done);
                                                                                          EmitRuntimeResolveVariantExpectedTagRoutine();
                                                                                          CompleteFunctionSpecialCase()
                                                                                        end
                                                                                      else
                                                                                        begin
                              NextToken();
                              ExpectSymbolChar('(');
                              NextToken();
                              if current_kind = TOK_KW_VAR then
                                NextToken();
                              ExpectKind(TOK_IDENT);
                              StrCopy(current_text, func_param);
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              if current_kind = TOK_KW_INTEGER then
                                generic_param_is_lexeme := 0
                              else
                                begin
                                  builtin_text := 'lexeme_buf';
                                  if StrEqIgnoreCase(current_text, builtin_text) then
                                    generic_param_is_lexeme := 1
                                  else
                                    FailParse()
                                end;
                              Write('CREATE ');
                              Write(func_param);
                              if generic_param_is_lexeme <> 0 then
                                WriteLn(' 0 , 124 ALLOT')
                              else
                                WriteLn(' 0 ,');
                              WriteLn('CREATE __FUNC_RET 0 ,');
                              WriteLn('CREATE __CALL_RET 0 ,');
                              NextToken();
                              ExpectSymbolChar(')');
                              NextToken();
                              ExpectSymbolChar(':');
                              NextToken();
                              if current_kind = TOK_KW_INTEGER then
                                begin
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken();
                                  ExpectKind(TOK_KW_BEGIN);
                                  NextToken();
                                  ExpectKind(TOK_IDENT);
                                  if StrEqIgnoreCase(current_text, func_name) = false then
                                    FailParse();
                                  NextToken();
                                  ExpectAssignSymbol();
                                  NextToken();
                                  if current_kind = TOK_INT then
                                    begin
                                      Write(': ');
                                      Write(func_name);
                                      WriteLn('');
                                      Write(func_param);
                                      Write(' PVAR! ');
                                      Write(current_value);
                                      WriteLn(' __FUNC_RET PVAR!');
                                      WriteLn('  __FUNC_RET PVAR@');
                                      WriteLn(';');
                                      NextToken();
                                      ExpectKind(TOK_KW_END);
                                      NextToken();
                                      ExpectSymbolChar(';');
                                      NextToken()
                                    end
                                  else
                                    begin
                                      if generic_param_is_lexeme <> 0 then
                                        FailParse();
                                      ExpectKind(TOK_IDENT);
                                      if StrEqIgnoreCase(current_text, func_param) = false then
                                        FailParse();
                                      NextToken();
                                      ExpectSymbolChar('+');
                                      NextToken();
                                      ExpectKind(TOK_IDENT);
                                      Write(': ');
                                      Write(func_name);
                                      WriteLn('');
                                      Write(func_param);
                                      Write(' PVAR! ');
                                      Write(func_param);
                                      Write(' PVAR@ ');
                                      Write(current_text);
                                      WriteLn(' PVAR@ + __FUNC_RET PVAR!');
                                      WriteLn('  __FUNC_RET PVAR@');
                                      WriteLn(';');
                                      NextToken();
                                      ExpectKind(TOK_KW_END);
                                      NextToken();
                                      ExpectSymbolChar(';');
                                      NextToken()
                                    end
                                end
                              else
                                begin
                                  builtin_text := 'boolean';
                                  if StrEqIgnoreCase(current_text, builtin_text) = false then
                                    FailParse();
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken();
                                  ExpectKind(TOK_KW_BEGIN);
                                  NextToken();
                                  ExpectKind(TOK_IDENT);
                                  if StrEqIgnoreCase(current_text, func_name) = false then
                                    FailParse();
                                  NextToken();
                                  ExpectAssignSymbol();
                                  NextToken();
                                  if current_kind = TOK_INT then
                                    begin
                                      Write(': ');
                                      Write(func_name);
                                      WriteLn('');
                                      Write(func_param);
                                      Write(' PVAR! ');
                                      Write(current_value);
                                      WriteLn(' __FUNC_RET PVAR!');
                                    end
                                  else
                                    begin
                                      ExpectKind(TOK_IDENT);
                                      builtin_text := 'false';
                                      if StrEqIgnoreCase(current_text, builtin_text) then
                                        begin
                                          Write(': ');
                                          Write(func_name);
                                          WriteLn('');
                                          Write(func_param);
                                          WriteLn(' PVAR!');
                                          WriteLn('0 __FUNC_RET PVAR!');
                                        end
                                      else
                                        begin
                                          builtin_text := 'true';
                                          if StrEqIgnoreCase(current_text, builtin_text) = false then
                                            FailParse();
                                          Write(': ');
                                          Write(func_name);
                                          WriteLn('');
                                          Write(func_param);
                                          WriteLn(' PVAR!');
                                          WriteLn('1 __FUNC_RET PVAR!');
                                        end
                                    end;
                                  WriteLn('  __FUNC_RET PVAR@');
                                  WriteLn(';');
                                  NextToken();
                                  ExpectKind(TOK_KW_END);
                                  NextToken();
                                  ExpectSymbolChar(';');
                                  NextToken()
                                end
                                                                                    end
                                                                                end
                                                                              end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                                                                                                                                            end
                                                                                                                                                                        end
                                                                                                                                                                    end
                                                                                                                                                                end
                                                                                                                                                            end
                                                                                                                                                        end
                                                                                                                                                    end
                                                                                                                                                end
                                                                                                                                            end
                                                                                                                                        end
                                                                                                                                    end
                                                                                                                                end
                                                                                                                            end
                                                                                                                        end
                                                                                                                    end
                                                                                                                end
                                                                                                            end
                                                                                                        end
                                                                                                    end
                                                                                                end
                                                                                            end
                                                                                        end
                                                                                    end
                                                                                end
                                                                                end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                                end
                                            end
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
end;

procedure ParseRoutineDecls;
var
  done: boolean;
begin
  done := false;
  while done = false do
    begin
      if current_kind = TOK_IDENT then
        begin
          if StrEqIgnoreCase(current_text, kw_procedure) then
            ParseProcedureDecl()
          else if StrEqIgnoreCase(current_text, kw_function) then
            ParseFunctionDecl()
          else
            done := true
        end
      else
        done := true
    end
end;

procedure ParseVarSection;
var
  done: boolean;
begin
  if current_kind = TOK_KW_VAR then
    begin
      NextToken();
      done := false;
      while done = false do
        begin
          if current_kind <> TOK_IDENT then
            done := true
          else if StrEqIgnoreCase(current_text, kw_procedure) then
            done := true
          else if StrEqIgnoreCase(current_text, kw_function) then
            done := true
          else if StrEqIgnoreCase(current_text, kw_begin) then
            done := true
          else
            begin
              StrCopy(current_text, saved_text);
              NextToken();
              ExpectSymbolChar(':');
              NextToken();
              builtin_text := 'boolean';
              if current_kind = TOK_KW_INTEGER then
                begin
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if StrEqIgnoreCase(current_text, kw_char) then
                begin
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if StrEqIgnoreCase(current_text, builtin_text) then
                begin
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if StrEqIgnoreCase(current_text, kw_real) then
                begin
                  StrCopy(saved_text, real_var_name);
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if HasEnumTypeName() and StrEqIgnoreCase(enum_type_name, current_text) then
                begin
                  StrCopy(saved_text, enum_var_name);
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if HasSetTypeName() and StrEqIgnoreCase(set_type_name, current_text) then
                begin
                  if set_var1_name[0] = #0 then
                    set_var1_name := saved_text
                  else
                    set_var2_name := saved_text;
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if HasSubrangeTypeName() and StrEqIgnoreCase(subrange_type_name, current_text) then
                begin
                  StrCopy(saved_text, subrange_var_name);
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  WriteLn(': __SUBRANGE_MISMATCH');
                  WriteLn('  S" Subrange check failed" PWRITE-STR');
                  WriteLn('  PWRITELN');
                  WriteLn('  1 0 / DROP');
                  WriteLn(';');
                  NextToken()
                end
              else if HasRecordTypeName() and StrEqIgnoreCase(record_type_name, current_text) then
                begin
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 , 4 ALLOT');
                  StrCopy(saved_text, record_var_name);
                  NextToken()
                end
              else if HasName(variant_type_name) and StrEqIgnoreCase(variant_type_name, current_text) then
                begin
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 , 8 ALLOT');
                  StrCopy(saved_text, record_var_name);
                  StrCopy(saved_text, variant_var_name);
                  EmitVariantHelpers();
                  NextToken()
                end
              else if HasStringTypeName() and StrEqIgnoreCase(string_type_name, current_text) then
                begin
                  if HasName(string_var1_name) = false then
                    begin
                      StrCopy(saved_text, string_var1_name);
                      EmitExtendedStringHelpers()
                    end
                  else
                    begin
                      if HasName(string_var2_name) = false then
                        StrCopy(saved_text, string_var2_name)
                      else
                        begin
                          if HasName(string_var3_name) = false then
                            StrCopy(saved_text, string_var3_name)
                          else
                            StrCopy(saved_text, string_var4_name)
                        end
                    end;
                  Write('CREATE ');
                  Write(saved_text);
                  Write(' 0 , ');
                  Write((char_array_len - 1) * 4);
                  WriteLn(' ALLOT');
                  NextToken()
                end
              else if HasStringType2Name() and StrEqIgnoreCase(string_type2_name, current_text) then
                begin
                  if HasName(string_var1_name) = false then
                    begin
                      StrCopy(saved_text, string_var1_name);
                      EmitExtendedStringHelpers()
                    end
                  else
                    begin
                      if HasName(string_var2_name) = false then
                        StrCopy(saved_text, string_var2_name)
                      else
                        begin
                          if HasName(string_var3_name) = false then
                            StrCopy(saved_text, string_var3_name)
                          else
                            StrCopy(saved_text, string_var4_name)
                        end
                    end;
                  Write('CREATE ');
                  Write(saved_text);
                  Write(' 0 , ');
                  Write((char_array_len2 - 1) * 4);
                  WriteLn(' ALLOT');
                  NextToken()
                end
              else if HasIntArrayTypeName() and StrEqIgnoreCase(int_array_type_name, current_text) then
                begin
                  StrCopy(saved_text, int_array_var_name);
                  Write('CREATE ');
                  Write(saved_text);
                  Write(' 0 , ');
                  Write((array_total_cells - 1) * 4);
                  WriteLn(' ALLOT');
                  NextToken()
                end
              else if HasName(pointer_type_name) and StrEqIgnoreCase(pointer_type_name, current_text) then
                begin
                  if HasName(pointer_var1_name) = false then
                    begin
                      StrCopy(saved_text, pointer_var1_name);
                      WriteLn('CREATE __NEWP 0 ,')
                    end
                  else
                    begin
                      if HasName(pointer_var2_name) = false then
                        StrCopy(saved_text, pointer_var2_name)
                      else
                        begin
                          if HasName(pointer_var3_name) = false then
                            StrCopy(saved_text, pointer_var3_name)
                          else
                            StrCopy(saved_text, pointer_var4_name)
                        end
                    end;
                  Write('CREATE ');
                  Write(saved_text);
                  WriteLn(' 0 ,');
                  NextToken()
                end
              else if current_kind = TOK_SYMBOL then
                begin
                  if current_text[0] = '^' then
                    begin
                      if HasName(pointer_var1_name) = false then
                        begin
                          StrCopy(saved_text, pointer_var1_name);
                          WriteLn('CREATE __NEWP 0 ,')
                        end
                      else
                        begin
                          if HasName(pointer_var2_name) = false then
                            StrCopy(saved_text, pointer_var2_name)
                          else
                            begin
                              if HasName(pointer_var3_name) = false then
                                StrCopy(saved_text, pointer_var3_name)
                              else
                                StrCopy(saved_text, pointer_var4_name)
                            end
                        end;
                      NextToken();
                      if current_kind <> TOK_IDENT then
                        begin
                          if current_kind <> TOK_KW_INTEGER then
                            begin
                              FailParse()
                            end
                        end;
                      Write('CREATE ');
                      Write(saved_text);
                      WriteLn(' 0 ,');
                      NextToken()
                    end
                  else
                    begin
                      FailParse()
                    end
                end
              else
                FailParse();
              ExpectSymbolChar(';');
              NextToken()
            end
        end
    end
end;

procedure ParseStmt;
begin
  if current_kind = TOK_KW_BEGIN then
    begin
      NextToken();
      ParseStmtList();
      ExpectKind(TOK_KW_END);
      NextToken()
    end
  else
    begin
      if current_kind = TOK_IDENT then
        begin
          if StrEqIgnoreCase(current_text, kw_if) then
            begin
              ParseIfStmt()
            end
          else if StrEqIgnoreCase(current_text, kw_while) then
            begin
              ParseWhileStmt()
            end
          else if StrEqIgnoreCase(current_text, kw_for) then
            begin
              ParseForStmt()
            end
          else if StrEqIgnoreCase(current_text, kw_repeat) then
            begin
              ParseRepeatStmt()
            end
          else
            begin
              builtin_text := 'case';
              if StrEqIgnoreCase(current_text, builtin_text) then
                begin
                  NextToken();
                  ParseCaseStmt()
                end
              else
                begin
                  ParseSimpleStmt()
                end
            end
        end
      else
        begin
          FailParse()
        end
    end
end;

procedure ParseStmtList;
var
  done: boolean;
begin
  done := false;
  while done = false do
    begin
      if current_kind = TOK_KW_END then
        done := true
      else
        begin
          ParseStmt();
          if current_kind = TOK_SYMBOL then
            begin
              if current_text[0] = ';' then
                begin
                  NextToken();
                  if current_kind = TOK_KW_END then
                    done := true
                end
              else
                done := true
            end
          else if current_kind = TOK_KW_END then
            done := true
          else
            done := true
        end
    end
end;

procedure ParseProgram;
begin
  NextToken();
  ExpectKind(TOK_KW_PROGRAM);
  NextToken();
  ExpectKind(TOK_IDENT);
  NextToken();
  ExpectSymbolChar(';');
  NextToken();
  with_active := 0;
  ClearStr(record_type_name);
  ClearStr(variant_type_name);
  ClearStr(pointer_type_name);
  ClearStr(int_array_type_name);
  ClearStr(string_type_name);
  ClearStr(string_type2_name);
  ClearStr(enum_type_name);
  ClearStr(set_type_name);
  ClearStr(subrange_type_name);
  ClearStr(record_var_name);
  ClearStr(variant_var_name);
  ClearStr(pointer_var1_name);
  ClearStr(pointer_var2_name);
  ClearStr(pointer_var3_name);
  ClearStr(pointer_var4_name);
  ClearStr(int_array_var_name);
  ClearStr(string_var1_name);
  ClearStr(string_var2_name);
  ClearStr(string_var3_name);
  ClearStr(string_var4_name);
  ClearStr(real_var_name);
  ClearStr(enum_var_name);
  ClearStr(set_var1_name);
  ClearStr(set_var2_name);
  ClearStr(subrange_var_name);
  ClearStr(enum_name0);
  ClearStr(enum_name1);
  ClearStr(enum_name2);
  ClearStr(enum_name3);
  ClearStr(enum_name4);
  ClearStr(enum_name5);
  ClearStr(enum_name6);
  ClearStr(enum_name7);
  ClearStr(field1_name);
  ClearStr(field2_name);
  ClearStr(variant_tag_name);
  ClearStr(variant_arm0_name);
  ClearStr(variant_arm1_name);
  ClearStr(variant_arm2_name);
  ClearStr(pointer_field_name);
  variant_active := 0;
  conformant_proc_dims := 0;
  array_dim_count := 0;
  array_total_cells := 0;
  ParseConstSection();
  ParseTypeSection();
  ParseVarSection();
  ParseRoutineDecls();
  ExpectKind(TOK_KW_BEGIN);
  NextToken();

  WriteLn('CREATE __CASE_MATCH 0 ,');
  WriteLn(': MAIN');
  ParseStmtList();
  WriteLn(';');
  WriteLn('MAIN');

  ExpectKind(TOK_KW_END);
  NextToken();
  ExpectSymbolChar('.')
end;
