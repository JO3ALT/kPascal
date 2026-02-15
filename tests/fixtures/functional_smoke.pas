program fs;
type
  pr = record
    x: integer;
    y: integer;
  end;
var
  a: integer;
  b: integer;
  r: pr;

procedure P(v: integer; var t: integer);
begin
  t := t + v
end;

function F(n: integer): integer;
begin
  case n of
    -2: F := 20;
    -1: F := 10;
    0: F := 0
  else
    F := 99
  end
end;

begin
  a := 1;
  P(2, a);

  r.x := a;
  r.y := 5;
  b := r.x + r.y;

  for a := 1 to 3 do
    Write('*');
  WriteLn;

  case r.x of
    3: WriteLn('THREE')
  else
    WriteLn('OTHER')
  end;

  WriteLn(b);
  WriteLn(F(-2));
  WriteLn(F(7))
end.
