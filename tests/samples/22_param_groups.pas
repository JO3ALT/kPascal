program sample22;

procedure ShowTotal(a: integer; b, c: integer);
begin
  WriteLn(a + b + c)
end;

function Add4(a: integer; b, c: integer; d: integer): integer;
begin
  Add4 := a + b + c + d
end;

begin
  ShowTotal(2, 3, 4);
  WriteLn(Add4(1, 2, 3, 4))
end.
