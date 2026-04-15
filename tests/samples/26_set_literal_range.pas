program sample26;
type
  digit = (d0, d1, d2, d3, d4, d5, d6, d7);
  digits = set of digit;
var
  a: digits;
begin
  a := [d1..d3, d5];
  WriteLn(d0 in a);
  WriteLn(d2 in a);
  WriteLn(d5 in a);
  WriteLn((a * [d2..d4]) = [d2, d3])
end.
