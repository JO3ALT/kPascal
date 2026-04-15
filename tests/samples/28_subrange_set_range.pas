program sample28;
type
  small = 5..7;
  smallset = set of small;
var
  lo: small;
  hi: small;
  mid: small;
  s: smallset;
begin
  lo := 5;
  hi := 7;
  mid := 6;
  s := [lo..hi];
  WriteLn(mid in s);
  WriteLn((s * [mid..hi]) = [mid, hi])
end.
