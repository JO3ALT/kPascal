program sample29;
type
  small = 5..7;
  smallset = set of small;
var
  s: smallset;
  t: smallset;
begin
  s := [5..7];
  t := [6, 7];
  WriteLn(6 in s);
  WriteLn((s * t) = t)
end.
