program kpsc_conf2d;
type
  mat = array[0..1, 4..5] of integer;
var
  m: mat;

procedure ShowTotal(a: array[i1..j1: integer; i2..j2: integer] of integer);
var
  x: integer;
  y: integer;
  sum: integer;
begin
  sum := 0;
  for x := Low(a) to High(a) do
    for y := i2 to j2 do
      sum := sum + a[x, y];
  WriteLn(sum)
end;

begin
  m[0, 4] := 1;
  m[0, 5] := 2;
  m[1, 4] := 3;
  m[1, 5] := 4;
  ShowTotal(m)
end.
