program seedhello;
var
  sourcelen: integer;
  kind: integer;
begin
  Read(sourcelen);
  Read(kind);
  WriteLn('CREATE __CASE_MATCH 0 ,');
  WriteLn(': MAIN');
  if kind = 0 then
    WriteLn('  72 PWRITE-CHAR')
  else
    WriteLn('');
  if kind = 1 then
    WriteLn('  14 PWRITE-I32')
  else
    WriteLn('');
  if kind = 2 then
    WriteLn('  33 PWRITE-I32')
  else
    WriteLn('');
  if kind = 0 then
    WriteLn('  69 PWRITE-CHAR')
  else
    WriteLn('');
  if kind = 1 then
    WriteLn('  PWRITELN')
  else
    WriteLn('');
  if kind = 2 then
    WriteLn('  PWRITELN')
  else
    WriteLn('');
  if kind = 0 then
    WriteLn('  76 PWRITE-CHAR')
  else
    WriteLn('');
  if kind = 1 then
    WriteLn('  3 PWRITE-I32')
  else
    WriteLn('');
  if kind = 0 then
    WriteLn('  76 PWRITE-CHAR')
  else
    WriteLn('');
  if kind = 1 then
    WriteLn('  PWRITELN')
  else
    WriteLn('');
  if kind = 0 then
    WriteLn('  79 PWRITE-CHAR')
  else
    WriteLn('');
  if kind = 1 then
    WriteLn('  2 PWRITE-I32')
  else
    WriteLn('');
  if kind = 0 then
    WriteLn('  PWRITELN')
  else
    WriteLn('');
  if kind = 1 then
    WriteLn('  PWRITELN')
  else
    WriteLn('');
  WriteLn(';');
  WriteLn('MAIN')
end.
