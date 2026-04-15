program sample23;

procedure AddInto(var a: integer; b: integer);
begin
  a := a + b
end;

var
  x: integer;

begin
  x := 10;
  AddInto(x, 7);
  WriteLn(x)
end.
