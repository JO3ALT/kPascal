program sample17;
var
  x: integer;

procedure Bump(var v: integer);
begin
  v := v + 2
end;

function AddBase(a: integer): integer;
begin
  AddBase := a + x
end;

begin
  x := 4;
  Bump(x);
  WriteLn(AddBase(3))
end.
