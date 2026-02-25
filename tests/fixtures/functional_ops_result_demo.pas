program functionalopsresultdemo;
type
  color = (red, green, blue);
  pair = record
    x: integer;
    y: integer;
  end;
  i4 = array[4] of integer;
  rint = result of integer, integer;
var
  c: color;
  p: pair;
  p2: pair;
  i: integer;
  xs: i4;
  ys: i4;
  zs: i4;
  n: integer;
  s: integer;
  r: rint;

begin
  c := green;
  case c of
    red: WriteLn(1);
    green: WriteLn(2);
    blue: WriteLn(3)
  end;

  p := pair(x := 10; y := 20);
  p2 := p with (y := 99);
  WriteLn(p.x);
  WriteLn(p2.y);

  xs := [1, 2, 3, 4];
  ys := xs with [1 := 20, 3 := 40];
  WriteLn(xs[1]);
  WriteLn(ys[1]);
  WriteLn(ys[3]);

  for i := 0 to 3 do
    zs[i] := xs[i] + 1;
  WriteArr(zs, 4);

  n := 0;
  for i := 0 to 3 do
    if zs[i] = 2 then
    begin
      ys[n] := zs[i];
      n := n + 1
    end
    else if zs[i] = 4 then
    begin
      ys[n] := zs[i];
      n := n + 1
    end;
  WriteLn(n);
  WriteArr(ys, n);

  s := 0;
  for i := 0 to 3 do
    s := s + xs[i];
  WriteLn(s);

  r := ok(value := 42);
  case r of
    ok(v): WriteLn(v);
    err(e): WriteLn(e)
  end;

  r := err(error := 7);
  case r of
    ok(v): WriteLn(v);
    err(e): WriteLn(e)
  end
end.
