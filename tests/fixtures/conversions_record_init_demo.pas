program convrecinit;
type
  point = record
    x: integer;
    y: real;
  end;
var
  a: integer;
  b: integer;
  c: real;
imut
  p: point;
begin
  a := Trunc(3.9);
  b := Round(-2.6);
  c := 7 / 2.0;
  p := point(x := a; y := c);
  WriteLn(a);
  WriteLn(b);
  WriteLn(c);
  WriteLn(p.x);
  WriteLn(p.y)
end.
