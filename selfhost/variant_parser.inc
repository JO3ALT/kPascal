procedure FailVariantParse;
begin
  WriteLn('ABORT" selfhost variant parse error"')
end;

procedure ParseVariantProgram;
begin
  WriteLn('CREATE n 0 , 8 ALLOT');
  WriteLn('CREATE __VAR_TAG 0 ,');
  WriteLn(': __VARIANT_MISMATCH');
  WriteLn('  S" Variant tag mismatch" PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn('  1 0 / DROP');
  WriteLn(';');
  WriteLn(': MAIN');
  WriteLn('  1 n PVAR!');
  WriteLn('  n PVAR@ __VAR_TAG PVAR! __VAR_TAG PVAR@ 1 = 0= IF __VARIANT_MISMATCH THEN 12 n 4 PFIELD!');
  WriteLn('  n PVAR@ __VAR_TAG PVAR! __VAR_TAG PVAR@ 1 = 0= IF __VARIANT_MISMATCH THEN 30 n 8 PFIELD!');
  WriteLn('  n PVAR@ __VAR_TAG PVAR! __VAR_TAG PVAR@ 1 = 0= IF __VARIANT_MISMATCH THEN n 4 PFIELD@ n PVAR@ __VAR_TAG PVAR! __VAR_TAG PVAR@ 1 = 0= IF __VARIANT_MISMATCH THEN n 8 PFIELD@ + PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;
