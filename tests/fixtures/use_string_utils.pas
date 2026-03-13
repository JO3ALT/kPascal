program usestringutils;
(* $I string_utils.pas *)
type
  str8 = array[8] of char;
  str16 = array[16] of char;
var
  a: str8;
  b: str8;
  d: str8;
  e: str8;
  f: str8;
  c: str16;
  n: integer;
begin
  ClearStr(a);
  AppendChar(a, 'P');
  AppendChar(a, 'A');
  AppendChar(a, 'S');
  WriteLn(a);

  b := 'PAS';
  WriteLn(StrEq(a, b));
  WriteLn(StrCmp(a, b));

  AppendChar(b, 'C');
  WriteLn(b);
  WriteLn(StrCmp(a, b));

  StrCopy(b, c);
  WriteLn(c);
  WriteLn(StartsWith(c, a));

  a := '  ABC';
  TrimLeft(a);
  WriteLn(a);

  b := 'XYZ   ';
  TrimRight(b);
  WriteLn(b);

  d := 'cal';
  AppendStr(d, a);
  WriteLn(a);

  c := ' -123';
  WriteLn(ParseInt(c, n));
  WriteLn(n);

  c := '12X';
  WriteLn(ParseInt(c, n));

  a := 'Pascal';
  b := 'pascal';
  e := 'Pascal';
  f := 'Pascal';
  c := 'PascaL';
  WriteLn(StrEqIgnoreCase(a, b));
  WriteLn(StrEqLit(a, e));
  WriteLn(StrEqIgnoreCaseLit(b, f));
  WriteLn(StrEqLit(b, f));
  WriteLn(StrEqIgnoreCaseLit(c, f));
  ClearStr(d);
  WriteLn(HasNameEqIgnoreCase(d, e));
  WriteLn(HasNameEqIgnoreCase(a, f));
  WriteLn(HasNameEqIgnoreCase(b, e))
end.
