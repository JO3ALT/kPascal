program sample24;
type
  small = 1..5;
var
  i: small;
  r: real;
begin
  i := 5;
  r := 7.25;
  WriteLn(i);
  WriteLn(r);
  WriteLn(Trunc(r));
  r := 7.0 / 2.0;
  WriteLn(r)
end.
