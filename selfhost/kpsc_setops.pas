program kpsc_setops;
type
  digit = (d0, d1, d2, d3, d4, d5, d6, d7);
  digits = set of digit;
var
  a: digits;
  b: digits;
begin
  a := [d1, d2, d3];
  b := [d3, d4];
  WriteLn(d2 in a);
  a := a + b;
  WriteLn(d4 in a);
  WriteLn((a * [d3]) = [d3])
end.
