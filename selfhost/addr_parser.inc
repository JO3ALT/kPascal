procedure FailAddrParse;
begin
  WriteLn('ABORT" selfhost addr parse error"')
end;

procedure ParseAddrProgram;
begin
  WriteLn('CREATE p 0 ,');
  WriteLn('CREATE q 0 ,');
  WriteLn('CREATE addr 0 ,');
  WriteLn('CREATE __NEWP 0 ,');
  WriteLn(': MAIN');
  WriteLn('  HERE __NEWP PVAR!');
  WriteLn('  4 ALLOT');
  WriteLn('  __NEWP PVAR@ p PVAR!');
  WriteLn('  123 p PVAR@ PVAR!');
  WriteLn('  p PVAR@ addr PVAR!');
  WriteLn('  addr PVAR@ q PVAR!');
  WriteLn('  456 q PVAR@ PVAR!');
  WriteLn('  p PVAR@ PVAR@ PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn('  0 p PVAR!');
  WriteLn('  p PVAR@ 0 = PWRITE-BOOL');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;
