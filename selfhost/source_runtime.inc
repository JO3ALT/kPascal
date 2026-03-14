procedure InitKeywords;
begin
  ClearStr(kw_program);
  AppendChar(kw_program, 'p'); AppendChar(kw_program, 'r'); AppendChar(kw_program, 'o'); AppendChar(kw_program, 'g'); AppendChar(kw_program, 'r'); AppendChar(kw_program, 'a'); AppendChar(kw_program, 'm');
  ClearStr(kw_type);
  AppendChar(kw_type, 't'); AppendChar(kw_type, 'y'); AppendChar(kw_type, 'p'); AppendChar(kw_type, 'e');
  ClearStr(kw_var);
  AppendChar(kw_var, 'v'); AppendChar(kw_var, 'a'); AppendChar(kw_var, 'r');
  ClearStr(kw_begin);
  AppendChar(kw_begin, 'b'); AppendChar(kw_begin, 'e'); AppendChar(kw_begin, 'g'); AppendChar(kw_begin, 'i'); AppendChar(kw_begin, 'n');
  ClearStr(kw_end);
  AppendChar(kw_end, 'e'); AppendChar(kw_end, 'n'); AppendChar(kw_end, 'd');
  ClearStr(kw_array);
  AppendChar(kw_array, 'a'); AppendChar(kw_array, 'r'); AppendChar(kw_array, 'r'); AppendChar(kw_array, 'a'); AppendChar(kw_array, 'y');
  ClearStr(kw_of);
  AppendChar(kw_of, 'o'); AppendChar(kw_of, 'f');
  ClearStr(kw_record);
  AppendChar(kw_record, 'r'); AppendChar(kw_record, 'e'); AppendChar(kw_record, 'c'); AppendChar(kw_record, 'o'); AppendChar(kw_record, 'r'); AppendChar(kw_record, 'd');
  ClearStr(kw_char);
  AppendChar(kw_char, 'c'); AppendChar(kw_char, 'h'); AppendChar(kw_char, 'a'); AppendChar(kw_char, 'r');
  ClearStr(kw_integer);
  AppendChar(kw_integer, 'i'); AppendChar(kw_integer, 'n'); AppendChar(kw_integer, 't'); AppendChar(kw_integer, 'e'); AppendChar(kw_integer, 'g'); AppendChar(kw_integer, 'e'); AppendChar(kw_integer, 'r');
  ClearStr(kw_real);
  AppendChar(kw_real, 'r'); AppendChar(kw_real, 'e'); AppendChar(kw_real, 'a'); AppendChar(kw_real, 'l');
  ClearStr(kw_writeln);
  AppendChar(kw_writeln, 'w'); AppendChar(kw_writeln, 'r'); AppendChar(kw_writeln, 'i'); AppendChar(kw_writeln, 't'); AppendChar(kw_writeln, 'e'); AppendChar(kw_writeln, 'l'); AppendChar(kw_writeln, 'n');
  ClearStr(kw_pos);
  AppendChar(kw_pos, 'p'); AppendChar(kw_pos, 'o'); AppendChar(kw_pos, 's');
  ClearStr(kw_div);
  AppendChar(kw_div, 'd'); AppendChar(kw_div, 'i'); AppendChar(kw_div, 'v');
  ClearStr(kw_mod);
  AppendChar(kw_mod, 'm'); AppendChar(kw_mod, 'o'); AppendChar(kw_mod, 'd');
  ClearStr(kw_and);
  AppendChar(kw_and, 'a'); AppendChar(kw_and, 'n'); AppendChar(kw_and, 'd');
  ClearStr(kw_for);
  AppendChar(kw_for, 'f'); AppendChar(kw_for, 'o'); AppendChar(kw_for, 'r');
  ClearStr(kw_while);
  AppendChar(kw_while, 'w'); AppendChar(kw_while, 'h'); AppendChar(kw_while, 'i'); AppendChar(kw_while, 'l'); AppendChar(kw_while, 'e');
  ClearStr(kw_to);
  AppendChar(kw_to, 't'); AppendChar(kw_to, 'o');
  ClearStr(kw_do);
  AppendChar(kw_do, 'd'); AppendChar(kw_do, 'o');
  ClearStr(kw_repeat);
  AppendChar(kw_repeat, 'r'); AppendChar(kw_repeat, 'e'); AppendChar(kw_repeat, 'p'); AppendChar(kw_repeat, 'e'); AppendChar(kw_repeat, 'a'); AppendChar(kw_repeat, 't');
  ClearStr(kw_until);
  AppendChar(kw_until, 'u'); AppendChar(kw_until, 'n'); AppendChar(kw_until, 't'); AppendChar(kw_until, 'i'); AppendChar(kw_until, 'l');
  ClearStr(kw_with);
  AppendChar(kw_with, 'w'); AppendChar(kw_with, 'i'); AppendChar(kw_with, 't'); AppendChar(kw_with, 'h');
  ClearStr(kw_if);
  AppendChar(kw_if, 'i'); AppendChar(kw_if, 'f');
  ClearStr(kw_then);
  AppendChar(kw_then, 't'); AppendChar(kw_then, 'h'); AppendChar(kw_then, 'e'); AppendChar(kw_then, 'n');
  ClearStr(kw_else);
  AppendChar(kw_else, 'e'); AppendChar(kw_else, 'l'); AppendChar(kw_else, 's'); AppendChar(kw_else, 'e');
  ClearStr(kw_procedure);
  AppendChar(kw_procedure, 'p'); AppendChar(kw_procedure, 'r'); AppendChar(kw_procedure, 'o'); AppendChar(kw_procedure, 'c'); AppendChar(kw_procedure, 'e'); AppendChar(kw_procedure, 'd'); AppendChar(kw_procedure, 'u'); AppendChar(kw_procedure, 'r'); AppendChar(kw_procedure, 'e');
  ClearStr(kw_function);
  AppendChar(kw_function, 'f'); AppendChar(kw_function, 'u'); AppendChar(kw_function, 'n'); AppendChar(kw_function, 'c'); AppendChar(kw_function, 't'); AppendChar(kw_function, 'i'); AppendChar(kw_function, 'o'); AppendChar(kw_function, 'n')
end;

function SourceAt(index: integer): char;
begin
  if index = source_pos then
    begin
      if source_pos < source_len then
        SourceAt := current_ch
      else
        SourceAt := #0
    end
  else if index = source_pos + 1 then
    begin
      if source_pos + 1 < source_len then
        SourceAt := next_ch
      else
        SourceAt := #0
    end
  else
    SourceAt := #0
end;

procedure SetSourceAt(index: integer; ch: char);
begin
  if index = source_pos then
    current_ch := ch
  else if index = source_pos + 1 then
    next_ch := ch
end;

procedure ReadSourceFromStdin;
begin
  InitKeywords();
  Read(source_len);
  source_pos := 0;
  current_ch := #0;
  next_ch := #0;
  if source_len > 0 then
    begin
      Read(stream_code);
      current_ch := Chr(stream_code);
      if source_len > 1 then
        begin
          Read(stream_code);
          next_ch := Chr(stream_code)
        end
    end
end;

procedure AdvanceChar;
begin
  if source_pos < source_len then
    begin
      source_pos := source_pos + 1;
      current_ch := next_ch;
      if source_pos + 1 < source_len then
        begin
          Read(stream_code);
          next_ch := Chr(stream_code)
        end
      else
        next_ch := #0
    end
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
  else if current_ch <> first_ch then
    MatchPair := false
  else if source_pos + 1 >= source_len then
    MatchPair := false
  else if next_ch <> second_ch then
    MatchPair := false
  else
    MatchPair := true
end;
