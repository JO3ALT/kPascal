program floatbasic;
const
  cf: float = 1.25;
var
  x: float;
  y: float;
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
