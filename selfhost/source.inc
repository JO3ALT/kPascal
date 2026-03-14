procedure InitKeywords;
begin
  kw_program := 'program';
  kw_type := 'type';
  kw_var := 'var';
  kw_begin := 'begin';
  kw_end := 'end';
  kw_array := 'array';
  kw_of := 'of';
  kw_record := 'record';
  kw_char := 'char';
  kw_integer := 'integer';
  kw_real := 'real';
  kw_writeln := 'writeln';
  kw_pos := 'pos';
  kw_div := 'div';
  kw_mod := 'mod';
  kw_and := 'and';
  kw_for := 'for';
  kw_while := 'while';
  kw_to := 'to';
  kw_do := 'do';
  kw_repeat := 'repeat';
  kw_until := 'until';
  kw_with := 'with';
  kw_if := 'if';
  kw_then := 'then';
  kw_else := 'else';
  kw_procedure := 'procedure';
  kw_function := 'function'
end;

procedure FinalizeLoadedSource;
begin
  source_len := Length(source);
  source_pos := 0
end;

function SourceAt(index: integer): char;
begin
  if index < 32768 then
    SourceAt := source[index]
  else if index < 65536 then
    SourceAt := source1^[index - 32768]
  else if index < 98304 then
    SourceAt := source2^[index - 65536]
  else if index < 131072 then
    SourceAt := source3^[index - 98304]
  else
    SourceAt := source4^[index - 131072]
end;

procedure SetSourceAt(index: integer; ch: char);
begin
  if index < 32768 then
    source[index] := ch
  else if index < 65536 then
    begin
      if source1 = nil then
        New(source1);
      source1^[index - 32768] := ch
    end
  else if index < 98304 then
    begin
      if source2 = nil then
        New(source2);
      source2^[index - 65536] := ch
    end
  else if index < 131072 then
    begin
      if source3 = nil then
        New(source3);
      source3^[index - 98304] := ch
    end
  else
    begin
      if source4 = nil then
        New(source4);
      source4^[index - 131072] := ch
    end
end;

procedure ReadSourceFromStdin;
var
  n: integer;
  i: integer;
  c: integer;
begin
  InitKeywords();
  Read(n);
  i := 0;
  while i < n do
    begin
      Read(c);
      if i < 32768 then
        source[i] := Chr(c)
      else if i < 65536 then
        begin
          if source1 = nil then
            New(source1);
          source1^[i - 32768] := Chr(c)
        end
      else if i < 98304 then
        begin
          if source2 = nil then
            New(source2);
          source2^[i - 65536] := Chr(c)
        end
      else if i < 131072 then
        begin
          if source3 = nil then
            New(source3);
          source3^[i - 98304] := Chr(c)
        end
      else
        begin
          if source4 = nil then
            New(source4);
          source4^[i - 131072] := Chr(c)
        end;
      i := i + 1
    end;
  if i < 32768 then
    source[i] := #0
  else if i < 65536 then
    begin
      if source1 = nil then
        New(source1);
      source1^[i - 32768] := #0
    end
  else if i < 98304 then
    begin
      if source2 = nil then
        New(source2);
      source2^[i - 65536] := #0
    end
  else if i < 131072 then
    begin
      if source3 = nil then
        New(source3);
      source3^[i - 98304] := #0
    end
  else
    begin
      if source4 = nil then
        New(source4);
      source4^[i - 131072] := #0
    end;
  source_len := i;
  source_pos := 0
end;

procedure LoadDefaultSource;
begin
  source := 'program sample01; begin WriteLn(''HELLO'') end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadArithmeticSource;
begin
  source := 'program sample02; var i: integer; begin i := 2 + 3 * 4; WriteLn(i); WriteLn(17 div 5); WriteLn(17 mod 5) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadControlSource;
begin
  source := 'program sample03; var i: integer; sum: integer; begin sum := 0; for i := 1 to 5 do sum := sum + i; i := 3; repeat sum := sum - 1; i := i - 1 until i = 0; WriteLn(sum) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadRecordSource;
begin
  source := 'program sample05; type point = record x: integer; y: integer; end; var p: point; begin p.x := 10; p.y := 20; with p do begin x := x + 1; y := y + 2 end; WriteLn(p.x + p.y) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadStringSource;
begin
  source := 'program sample13; type str16 = array[16] of char; var s: str16; needle: str16; begin s := ''ABC''; needle := ''BC''; WriteLn(s); WriteLn(Pos(needle, s)) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadStringEditSource;
begin
  source := 'program sample14; type str16 = array[16] of char; var a: str16; b: str16; c: str16; z: str16; begin a := ''AB''; b := ''CD''; z := ''Z''; Concat(a, b, c); WriteLn(c); Delete(c, 2, 2); WriteLn(c); Insert(z, c, 2); WriteLn(c) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadHexSource;
begin
  source := 'program sample15; type hexbuf = array[9] of char; var s: hexbuf; begin IntToHex(255, s, 8, true); WriteLn(s); WriteLn(HexToInt(s)) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadRealSource;
begin
  source := 'program sample16; var r: real; begin r := 7.0 / 2.0; WriteLn(r); WriteLn(Round(r)); WriteLn(Trunc(r)) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadCaseSource;
begin
  source := 'program sample18; var i: integer; begin i := 3; case i of 1, 2: WriteLn(''LOW''); 3..5: WriteLn(''MID'') else WriteLn(''HIGH'') end end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadScalarBuiltinsSource;
begin
  source := 'program sample20; begin WriteLn(Abs(-7)); WriteLn(Sqr(5)); WriteLn(Odd(5)); WriteLn(UpCase(''q'')); WriteLn(Ord(Chr(66))) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadArray2dSource;
begin
  source := 'program sample09; type matrix = array[1..2, 1..2] of integer; var m: matrix; begin m[1, 1] := 1; m[1, 2] := 2; m[2, 1] := 3; m[2, 2] := 4; WriteLn(m[1, 2] + m[2, 1] + m[2, 2]) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadArray4dSource;
begin
  source := 'program sample10; type cube4 = array[1..2, 1..2, 1..2, 1..2] of integer; var a: cube4; begin a[1, 1, 2, 1] := 9; a[2, 2, 1, 2] := 4; WriteLn(a[1, 1, 2, 1] + a[2, 2, 1, 2]) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadVariantSource;
begin
  source := 'program sample06; type node = record case tag: integer of 0: (i: integer;); 1: (j: integer; k: integer;); end; var n: node; begin n.tag := 1; n.j := 12; n.k := 30; WriteLn(n.j + n.k) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadPointerSource;
begin
  source := 'program sample07; type node = record value: integer; end; var p: ^node; begin new(p); p^.value := 77; WriteLn(p^.value); dispose(p); WriteLn(p = nil) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadAddrSource;
begin
  source := 'program sample08; type cellp = ^integer; var p: cellp; q: cellp; addr: integer; begin new(p); p^ := 123; addr := Addr(p^); SetAddr(q, addr); q^ := 456; WriteLn(p^); dispose(p); WriteLn(p = nil) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadEnumSetSource;
begin
  source := 'program sample04; type color = (red, green, blue); palette = set of color; small = 1..5; var c: color; s: palette; i: small; begin c := green; s := [red, green]; i := 3; WriteLn(c in s); WriteLn(Ord(c) + i) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadConformant1dSource;
begin
  source := 'program sample11; type vec = array[3..5] of integer; var v: vec; procedure ShowSum(a: array[lo..hi: integer] of integer); var i: integer; sum: integer; begin sum := 0; for i := Low(a) to High(a) do sum := sum + a[i]; WriteLn(sum) end; begin v[3] := 5; v[4] := 6; v[5] := 7; ShowSum(v) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadConformant2dSource;
begin
  source := 'program sample12; type mat = array[0..1, 4..5] of integer; var m: mat; procedure ShowTotal(a: array[i1..j1: integer; i2..j2: integer] of integer); var x: integer; y: integer; sum: integer; begin sum := 0; for x := Low(a) to High(a) do for y := i2 to j2 do sum := sum + a[x, y]; WriteLn(sum) end; begin m[0, 4] := 1; m[0, 5] := 2; m[1, 4] := 3; m[1, 5] := 4; ShowTotal(m) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadSetOpsSource;
begin
  source := 'program sample19; type digit = (d0, d1, d2, d3, d4, d5, d6, d7); digits = set of digit; var a: digits; b: digits; begin a := [d1, d2, d3]; b := [d3, d4]; WriteLn(d2 in a); a := a + b; WriteLn(d4 in a); WriteLn((a * [d3]) = [d3]) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure LoadRoutineSource;
begin
  source := 'program sample17; var x: integer; procedure Bump(var v: integer); begin v := v + 2 end; function AddBase(a: integer): integer; begin AddBase := a + x end; begin x := 4; Bump(x); WriteLn(AddBase(3)) end.';
  InitKeywords();
  FinalizeLoadedSource()
end;

procedure AdvanceChar;
begin
  if source_pos < source_len then
    source_pos := source_pos + 1
end;

function IsLetter(ch: char): boolean;
begin
  if ch < 'A' then
    IsLetter := false
  else if ch <= 'Z' then
    IsLetter := true
  else if ch < 'a' then
    IsLetter := false
  else if ch <= 'z' then
    IsLetter := true
  else if ch = '_' then
    IsLetter := true
  else
    IsLetter := false
end;

function IsDigit(ch: char): boolean;
begin
  if ch < '0' then
    IsDigit := false
  else if ch <= '9' then
    IsDigit := true
  else
    IsDigit := false
end;

function IsIdentChar(ch: char): boolean;
begin
  if IsLetter(ch) then
    IsIdentChar := true
  else if IsDigit(ch) then
    IsIdentChar := true
  else
    IsIdentChar := false
end;

function IsSpace(ch: char): boolean;
begin
  if ch = ' ' then
    IsSpace := true
  else if ch = #10 then
    IsSpace := true
  else if ch = #13 then
    IsSpace := true
  else if ch = #9 then
    IsSpace := true
  else
    IsSpace := false
end;

function MatchPair(first_ch: char; second_ch: char): boolean;
begin
  if source_pos >= source_len then
    MatchPair := false
  else if SourceAt(source_pos) <> first_ch then
    MatchPair := false
  else if source_pos + 1 >= source_len then
    MatchPair := false
  else if SourceAt(source_pos + 1) <> second_ch then
    MatchPair := false
  else
    MatchPair := true
end;
