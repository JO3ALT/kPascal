procedure EmitHeader;
begin
  WriteLn('CREATE __CASE_MATCH 0 ,');
  WriteLn(': MAIN')
end;

procedure EmitFooter;
begin
  WriteLn(';');
  WriteLn('MAIN')
end;

procedure EmitIntLine(value: integer);
begin
  Write('  ');
  Write(value);
  WriteLn(' PWRITE-I32');
  WriteLn('  PWRITELN')
end;

procedure EmitBoolLine(value: integer);
begin
  if value <> 0 then
    begin
      WriteLn('  84 PWRITE-CHAR');
      WriteLn('  82 PWRITE-CHAR');
      WriteLn('  85 PWRITE-CHAR');
      WriteLn('  69 PWRITE-CHAR')
    end
  else
    begin
      WriteLn('  70 PWRITE-CHAR');
      WriteLn('  65 PWRITE-CHAR');
      WriteLn('  76 PWRITE-CHAR');
      WriteLn('  83 PWRITE-CHAR');
      WriteLn('  69 PWRITE-CHAR')
    end;
  WriteLn('  PWRITELN')
end;

procedure EmitStringLine(var text: token_buf);
var i: integer;
begin
  i := 0;
  while text[i] <> #0 do
    begin
      Write('  ');
      Write(Ord(text[i]));
      WriteLn(' PWRITE-CHAR');
      i := i + 1
    end;
  WriteLn('  PWRITELN')
end;
