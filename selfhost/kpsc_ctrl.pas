program kpsc_ctrl;
var
  i: integer;
  sum: integer;
begin
  sum := 0;
  for i := 1 to 5 do
    sum := sum + i;
  i := 3;
  repeat
    sum := sum - 1;
    i := i - 1
  until i = 0;
  WriteLn(sum)
end.
