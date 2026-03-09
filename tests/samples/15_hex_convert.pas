program sample15;
type
  hexbuf = array[9] of char;
var
  s: hexbuf;
begin
  IntToHex(255, s, 8, true);
  WriteLn(s);
  WriteLn(HexToInt(s))
end.
