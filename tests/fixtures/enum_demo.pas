program enumdemo;
type
  color = (red, green, blue);
var
  c: color;
begin
  c := green;
  WriteLn(blue);
  WriteLn(c);
  case c of
    red: WriteLn('RED');
    green: WriteLn('GREEN');
    blue: WriteLn('BLUE')
  end
end.
