program sample07;
type
  node = record
    value: integer;
  end;
var
  p: ^node;
begin
  new(p);
  p^.value := 77;
  WriteLn(p^.value);
  dispose(p);
  WriteLn(p = nil)
end.
