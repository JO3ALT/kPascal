procedure ParseSetOpsProgram;
begin
  WriteLn('CREATE a 0 ,');
  WriteLn('CREATE b 0 ,');
  WriteLn(': MAIN');
  WriteLn('  1 1 0 - LSHIFT 1 2 0 - LSHIFT OR 1 3 0 - LSHIFT OR a PVAR!');
  WriteLn('  1 3 0 - LSHIFT 1 4 0 - LSHIFT OR b PVAR!');
  WriteLn('  1 2 0 - LSHIFT a PVAR@ AND 0= 0= PWRITE-BOOL');
  WriteLn('  PWRITELN');
  WriteLn('  a PVAR@ b PVAR@ OR a PVAR!');
  WriteLn('  1 4 0 - LSHIFT a PVAR@ AND 0= 0= PWRITE-BOOL');
  WriteLn('  PWRITELN');
  WriteLn('  a PVAR@ 1 3 0 - LSHIFT AND 1 3 0 - LSHIFT = PWRITE-BOOL');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;
