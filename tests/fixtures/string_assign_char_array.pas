program strarr;
type
  s6 = array[6] of char;
var
  s: s6;
begin
  s := 'ABC';
  WriteLn(s[0], s[1], s[2]);
  WriteLn(s[3] = #0);
  s := 'XYZLONG';
  WriteLn(s[0], s[1], s[2], s[3], s[4]);
  WriteLn(s[5] = #0)
end.
