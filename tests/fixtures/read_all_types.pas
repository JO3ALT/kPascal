program readall;
type
  rec = record
    i: integer;
    b: boolean;
    c: char;
  end;
var
  i: integer;
  b: boolean;
  c: char;
  r: rec;
begin
  Read(i, b, c, r.i, r.b, r.c);
  WriteLn(i);
  WriteLn(b);
  WriteLn(c);
  WriteLn(r.i);
  WriteLn(r.b);
  WriteLn(r.c)
end.
