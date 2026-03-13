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
      SetSourceAt(i, Chr(c));
      i := i + 1
    end;
  SetSourceAt(i, #0);
  source_len := i;
  source_pos := 0
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
