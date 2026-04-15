program kpsc_array2d;
type
  matrix = array[1..2, 1..2] of integer;
var
  m: matrix;
begin
  m[1, 1] := 1;
  m[1, 2] := 2;
  m[2, 1] := 3;
  m[2, 2] := 4;
  WriteLn(m[1, 2] + m[2, 1] + m[2, 2])
end.
