program builtins;
type
  a5 = array[5] of char;
  a9 = array[9] of char;
var
  s: a5;
  hs: a9;
  i: integer;
  a: integer;
  b: integer;
begin
  s := 'AB';
  i := Ord('A') + $10;
  WriteLn(i);
  WriteLn(Chr(66));
  WriteLn(Length(s));
  WriteLn(Low(s));
  WriteLn(High(s));
  Read(a);
  ReadLn;
  Read(b);
  IntToHex(a, hs, 8, true);
  WriteLn(hs);
  WriteLn(b)
end.
