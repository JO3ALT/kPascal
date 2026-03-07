program sample08;
type
  cellp = ^integer;
var
  p: cellp;
  q: cellp;
  addr: integer;
begin
  new(p);
  p^ := 123;
  addr := Addr(p^);
  SetAddr(q, addr);
  q^ := 456;
  WriteLn(p^);
  dispose(p);
  WriteLn(p = nil)
end.
