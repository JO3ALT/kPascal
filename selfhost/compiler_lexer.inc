procedure SkipWhitespace;
begin
  while (source_pos < source_len) and (source_text[source_pos] <= ' ') do
    source_pos := source_pos + 1
end;

procedure ClearTokenText;
var i: integer;
begin
  for i := 0 to MAX_TOKEN_LEN do
    current_text[i] := #0
end;

procedure ReadIdentOrKeyword;
var i: integer;
begin
  ClearTokenText();
  i := 0;
  while (source_pos < source_len) and ((source_text[source_pos] >= 'a') and (source_text[source_pos] <= 'z') or (source_text[source_pos] >= 'A') and (source_text[source_pos] <= 'Z')) do
    begin
      if i <= MAX_TOKEN_LEN then
        current_text[i] := source_text[source_pos];
      i := i + 1;
      source_pos := source_pos + 1
    end;
  current_kind := TOK_IDENT
end;

procedure ReadNumber;
begin
  current_value := 0;
  while (source_pos < source_len) and (source_text[source_pos] >= '0') and (source_text[source_pos] <= '9') do
    begin
      current_value := current_value * 10 + Ord(source_text[source_pos]) - Ord('0');
      source_pos := source_pos + 1
    end;
  current_kind := TOK_INT
end;

procedure ReadSymbol;
begin
  ClearTokenText();
  current_text[0] := source_text[source_pos];
  current_text[1] := #0;
  current_kind := TOK_SYMBOL;
  source_pos := source_pos + 1
end;

procedure NextToken;
begin
  SkipWhitespace();
  ClearTokenText();
  if source_pos >= source_len then
    begin
      current_kind := TOK_EOF;
      exit
    end;
  if (source_text[source_pos] >= '0') and (source_text[source_pos] <= '9') then
    ReadNumber()
  else if ((source_text[source_pos] >= 'a') and (source_text[source_pos] <= 'z')) or ((source_text[source_pos] >= 'A') and (source_text[source_pos] <= 'Z')) then
    ReadIdentOrKeyword()
  else
    ReadSymbol()
end;
