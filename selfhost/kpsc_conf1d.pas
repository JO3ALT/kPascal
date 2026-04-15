program kpsc_conf1d;
type
  vec = array[3..5] of integer;
var
  v: vec;

procedure ShowSum(a: array[lo..hi: integer] of integer);
var
  i: integer;
  sum: integer;
begin
  sum := 0;
  for i := Low(a) to High(a) do
    sum := sum + a[i];
  WriteLn(sum)
end;

begin
  v[3] := 5;
  v[4] := 6;
  v[5] := 7;
  ShowSum(v)
end.
