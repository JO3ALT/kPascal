program rwstr;
type
  s8 = array[8] of char;
var
  s: s8;
begin
  ReadStr(s, 5);
  WriteStr(s);
  WriteLn;
  s := 'XYZ';
  WriteStr(s);
  WriteLn
end.
