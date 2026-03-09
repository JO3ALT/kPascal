program sample05;
type
  point = record
    x: integer;
    y: integer;
  end;
var
  p: point;
begin
  p.x := 10;
  p.y := 20;
  with p do
  begin
    x := x + 1;
    y := y + 2
  end;
  WriteLn(p.x + p.y)
end.
