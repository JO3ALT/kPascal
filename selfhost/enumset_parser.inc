procedure ParseEnumSetProgram;
begin
  WriteLn('CREATE c 0 ,');
  WriteLn('CREATE s 0 ,');
  WriteLn('CREATE i 0 ,');
  WriteLn(': __SUBRANGE_MISMATCH');
  WriteLn('  S" Subrange check failed" PWRITE-STR');
  WriteLn('  PWRITELN');
  WriteLn('  1 0 / DROP');
  WriteLn(';');
  WriteLn(': MAIN');
  WriteLn('  1 c PVAR!');
  WriteLn('  1 0 0 - LSHIFT 1 1 0 - LSHIFT OR s PVAR!');
  WriteLn('  3 DUP 1 >= OVER 5 <= AND 0= IF __SUBRANGE_MISMATCH THEN i PVAR!');
  WriteLn('  1 c PVAR@ 0 - LSHIFT s PVAR@ AND 0= 0= PWRITE-BOOL');
  WriteLn('  PWRITELN');
  WriteLn('  c PVAR@ i PVAR@ + PWRITE-I32');
  WriteLn('  PWRITELN');
  WriteLn(';');
  WriteLn('MAIN')
end;
