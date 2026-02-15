program agg3d;
type
  rec = record
    x: integer;
    y: integer;
  end;
  cube = array[2,3,4] of integer;
var
  a: rec;
  b: rec;
  c: cube;
begin
  a.x := 10;
  a.y := 20;
  b := a;
  c[1,2,3] := 77;
  WriteLn(b.x);
  WriteLn(b.y);
  WriteLn(c[1,2,3])
end.
