program kpsc_array4d;
type
  cube4 = array[1..2, 1..2, 1..2, 1..2] of integer;
var
  a: cube4;
begin
  a[1, 1, 2, 1] := 9;
  a[2, 2, 1, 2] := 4;
  WriteLn(a[1, 1, 2, 1] + a[2, 2, 1, 2])
end.
