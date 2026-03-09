program sample13;
type
  str16 = array[16] of char;
var
  s: str16;
  needle: str16;
begin
  s := 'ABC';
  needle := 'BC';
  WriteLn(s);
  WriteLn(Pos(needle, s))
end.
