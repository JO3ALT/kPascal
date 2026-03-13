procedure FailPointerParse;
begin
  WriteLn('ABORT" selfhost pointer parse error"')
end;

procedure ParsePointerProgram;
begin
  WriteLn('CREATE p 0 ,');
  WriteLn('CREATE __NEWP 0 ,');
  WriteLn(': MAIN');
  WriteLn('  HERE __NEWP PVAR!');
  WriteLn('  4 ALLOT');
  WriteLn('  __NEWP PVAR@ p PVAR!');
  WriteLn('  77 p PVAR@ 0 + PVAR!');
  WriteLn('  p PVAR@ 0 + PVAR@ PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn('  0 p PVAR!');
  WriteLn('  p PVAR@ 0 = PWRITE-BOOL');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;
