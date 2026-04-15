program sample21;

procedure ShowSum(a, b: integer);
begin
  WriteLn(a + b)
end;

function Add3(a, b, c: integer): integer;
begin
  Add3 := a + b + c
end;

begin
  ShowSum(3, 4);
  WriteLn(Add3(1, 2, 3))
end.
