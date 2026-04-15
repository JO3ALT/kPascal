program kpsc_case;
var
  i: integer;
begin
  i := 3;
  case i of
    1, 2: WriteLn('LOW');
    3..5: WriteLn('MID')
  else
    WriteLn('HIGH')
  end
end.
