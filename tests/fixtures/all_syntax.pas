program allsyntax;
const
  c1 = 10;
  c2 = -3 + 2 * 4;
  c3 = #65;
  c4 = 'Z';
  c5 = c1 >= c2;
type
  myint = integer;
  mychar = char;
  pair = record
    x: integer;
    y: myint;
  end;
  wrapper = record
    p: pair;
    flag: boolean;
  end;
var
  i: integer;
  ch: mychar;
  ok: boolean;
  p: pair;
  w: wrapper;

procedure Bump(var a: integer);
begin
  a := a + 1
end;

function Sign(v: integer): integer;
begin
  if v < 0 then
    Sign := -1
  else
    if v > 0 then
      Sign := 1
    else
      Sign := 0
end;
begin
  ;
  i := c1 + c2 * 2;
  i := -i;
  ch := c3;
  ok := not (i = 0);

  ok := i = 10;
  ok := i <> 11;
  ok := i < 12;
  ok := i <= 13;
  ok := i > 14;
  ok := i >= 15;

  p.x := i;
  p.y := p.x + 1;
  w.p.x := p.y;
  w.p.y := w.p.x - 1;
  w.flag := i <> 0;

  if i > 0 then
    Write(i);

  if i <= 0 then
    WriteLn('N')
  else
    begin
      Write(ch);
      WriteLn
    end;

  while i < 20 do
    begin
      i := i + 1;
      WriteLn(i)
    end;

  for i := 1 to 3 do
    Write('*');

  for i := 3 downto 1 do
    Write('*');

  i := 20;
  repeat
    i := i - 1;
    Write(#42)
  until i = 10;

  Bump(i);
  case Sign(i) of
    -1: Write('N');
    0: Write('Z');
    1: Write('P')
  else
    Write('?')
  end;

  Write(' ');
  Write('ABC', ' ', i);
  WriteLn;
  WriteLn(1 < 2);
  WriteLn(c4);
  WriteLn(c5)
end.
