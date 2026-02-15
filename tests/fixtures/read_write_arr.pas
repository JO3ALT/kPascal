program rwarr;
type
  arr = array[4] of integer;
var
  a: arr;
begin
  ReadArr(a, 3);
  WriteArr(a, 3)
end.
