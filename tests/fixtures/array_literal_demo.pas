program arraylitdemo;
type
  pair = record
    a: integer;
    b: integer;
  end;
var
  xs: array[4] of integer;
  ps: array[2] of pair;
imut
  ys: array[3] of float;
begin
  xs := [10, 20, 30, 40];
  ps := [pair(a := 1; b := 2), pair(a := 3; b := 4)];
  ys := [1.5, 2.5, 3.5];
  WriteLn(xs[0]);
  WriteLn(xs[3]);
  WriteLn(ps[0].a + ps[1].b);
  WriteLn(ys[1])
end.
