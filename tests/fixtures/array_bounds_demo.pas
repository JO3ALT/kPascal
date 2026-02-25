program arrayboundsdemo;
var
  a: array[-1..1] of integer;
  m: array[2..3, 5..6] of integer;
begin
  a[-1] := 10;
  a[0] := 20;
  a[1] := 30;
  m[2, 5] := 7;
  m[3, 6] := 9;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(Length(a));
  WriteLn(a[-1] + a[1]);
  WriteLn(Low(m));
  WriteLn(High(m));
  WriteLn(m[2, 5] + m[3, 6])
end.
