program sample14;
type
  str16 = array[16] of char;
var
  a: str16;
  b: str16;
  c: str16;
  z: str16;
begin
  a := 'AB';
  b := 'CD';
  z[0] := 'Z';
  z[1] := #0;
  Concat(a, b, c);
  WriteLn(c);
  Delete(c, 2, 2);
  WriteLn(c);
  Insert(z, c, 2);
  WriteLn(c)
end.
