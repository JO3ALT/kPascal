program floatbasic;
const
  cf: real = 1.25;
var
  x: real;
  y: real;
begin
  x := 1.5;
  y := 2.25;
  WriteLn(cf);
  WriteLn(x + y);
  WriteLn(y - x);
  WriteLn(x * y);
  WriteLn(y / x);
  WriteLn(x < y);
  WriteLn(x = 1.5)
end.
