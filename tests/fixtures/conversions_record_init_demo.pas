program convrecinit;
type
  point = record
    x: integer;
    y: float;
  end;
var
  a: integer;
  b: integer;
  c: float;
imut
  p: point;
begin
  a := Trunc(3.9);
  b := Round(-2.6);
  c := Float(7) / 2.0;
  p := point(x := a; y := c);
  WriteLn(a);
  WriteLn(b);
  WriteLn(c);
  WriteLn(p.x);
  WriteLn(p.y)
end.
