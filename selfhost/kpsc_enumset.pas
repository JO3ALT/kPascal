program kpsc_enumset;
type
  color = (red, green, blue);
  palette = set of color;
  small = 1..5;
var
  c: color;
  s: palette;
  i: small;
begin
  c := green;
  s := [red, green];
  i := 3;
  WriteLn(c in s);
  WriteLn(Ord(c) + i)
end.
