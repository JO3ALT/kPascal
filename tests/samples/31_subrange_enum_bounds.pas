program sample31;
type
  digit = (zero, one, two, three, four, five);
  mid = one..four;
  midset = set of mid;
var
  s: midset;
  m: mid;
begin
  m := three;
  s := [one..three];
  WriteLn(m in s);
  WriteLn(four in s)
end.
