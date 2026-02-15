program allfeat;

type
  pair = record
    a: integer;
    b: integer;
  end;
  arr3 = array[2,3,4] of integer;
  iarr = array[4] of integer;
  s8 = array[8] of char;

var
  gi: integer;
  gj: integer;
  gn: integer;
  gb: boolean;
  gch: char;
  gp1: pair;
  gp2: pair;
  ga1: iarr;
  ga2: iarr;
  gcube: arr3;
  gstr: s8;

(* $I math.pas *)

procedure IncRef(var x: integer);
begin
  x := x + 1
end;

function SumPair(pp: pair): integer;
begin
  SumPair := pp.a + pp.b
end;

procedure Outer(var x: integer);
  procedure Inner(var y: integer);
  begin
    y := y + 3
  end;
begin
  Inner(x)
end;

begin
  WriteLn('BEGIN');
  WriteLn($2A);
  WriteLn(Ord('A'));
  WriteLn(Chr(66));

  gi := 5;
  gj := 2;
  gb := gi > gj;
  gch := 'Z';
  WriteLn(gi);
  WriteLn(gb);
  WriteLn(gch);

  gp1.a := 10;
  gp1.b := 20;
  gp2 := gp1;
  WriteLn(SumPair(gp2));

  ga1[0] := 1;
  ga1[1] := 2;
  ga1[2] := 3;
  ga1[3] := 4;
  ga2 := ga1;
  WriteLn(ga2[0]);
  WriteLn(ga2[1]);
  WriteLn(ga2[2]);
  WriteLn(ga2[3]);

  gcube[1,2,3] := 77;
  WriteLn(gcube[1,2,3]);
  WriteLn(Length(ga1));
  WriteLn(Low(ga1));
  WriteLn(High(ga1));

  gstr := 'ABC';
  WriteStr(gstr);
  WriteLn;
  WriteLn(gstr[3] = #0);

  for gi := 1 to 3 do
    Write('*');
  WriteLn;

  gi := 3;
  while gi > 0 do
    begin
      Write('#');
      gi := gi - 1
    end;
  WriteLn;

  repeat
    gj := gj + 1
  until gj = 4;
  WriteLn(gj);

  case gj of
    3: WriteLn('THREE');
    4: WriteLn('FOUR')
  else
    WriteLn('OTHER')
  end;

  gi := 10;
  IncRef(gi);
  Outer(gi);
  WriteLn(gi);

  WriteLn(sqrt(81));
  WriteLn(sin(30));
  WriteLn(cos(60));
  WriteLn(tan(45));
  WriteLn(asin(5000));
  WriteLn(acos(5000));
  WriteLn(atan(10000));
  WriteLn(ln(2));
  WriteLn(log(10));

  Read(gn);
  ReadLn;
  Read(gb, gch);
  ReadArr(ga1, 3);
  ReadStr(gstr, 5);

  WriteHex(gn);
  WriteLn;
  WriteLn(gb);
  WriteLn(gch);
  WriteArr(ga1, 3);
  WriteStr(gstr);
  WriteLn;
  WriteLn('END')
end.
