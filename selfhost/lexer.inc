procedure SkipSpaces;
var
  done: boolean;
  keep: boolean;
  ch: char;
begin
  done := false;
  while done = false do
    begin
      keep := false;
      if source_pos >= source_len then
        done := true
      ;
      if done = false then
        begin
          ch := SourceAt(source_pos);
          if ch = ' ' then
            keep := true
          else if ch = #10 then
            keep := true
          else if ch = #13 then
            keep := true
          else if ch = #9 then
            keep := true
        end;
      if keep then
        AdvanceChar();
      if done = false then
        begin
          if keep = false then
            done := true
        end
    end;
end;

procedure ReadIdentifier;
var
  done: boolean;
  keep: boolean;
  ch: char;
begin
  ClearStr(current_text);
  done := false;
  while done = false do
    begin
      keep := false;
      if source_pos >= source_len then
        done := true
      ;
      if done = false then
        begin
          ch := SourceAt(source_pos);
          if ch >= 'A' then
            begin
              if ch <= 'Z' then
                keep := true
            end;
          if keep = false then
            begin
              if ch >= 'a' then
                begin
                  if ch <= 'z' then
                    keep := true
                end
            end;
          if keep = false then
            begin
              if ch = '_' then
                keep := true
            end;
          if keep = false then
            begin
              if ch >= '0' then
                begin
                  if ch <= '9' then
                    keep := true
                end
            end
        end;
      if keep then
        begin
          AppendChar(current_text, ch);
          AdvanceChar()
        end;
      if done = false then
        begin
          if keep = false then
            done := true
        end
    end;
  if UpCase(current_text[0]) = 'P' then
    begin
      if UpCase(current_text[1]) = 'R' then
        begin
          if UpCase(current_text[2]) = 'O' then
            begin
              if UpCase(current_text[3]) = 'G' then
                begin
                  if UpCase(current_text[4]) = 'R' then
                    begin
                      if UpCase(current_text[5]) = 'A' then
                        begin
                          if UpCase(current_text[6]) = 'M' then
                            begin
                              if current_text[7] = #0 then
                                current_kind := TOK_KW_PROGRAM
                              else
                                current_kind := TOK_IDENT
                            end
                          else
                            current_kind := TOK_IDENT
                        end
                      else
                        current_kind := TOK_IDENT
                    end
                  else
                    current_kind := TOK_IDENT
                end
              else
                current_kind := TOK_IDENT
            end
          else
            current_kind := TOK_IDENT
        end
      else
        current_kind := TOK_IDENT
    end
  else
    begin
      current_kind := TOK_IDENT
    end;
  if current_kind = TOK_KW_PROGRAM then
    current_kind := TOK_KW_PROGRAM
  else
    begin
      if UpCase(current_text[0]) = 'V' then
        begin
          if UpCase(current_text[1]) = 'A' then
            begin
              if UpCase(current_text[2]) = 'R' then
                begin
                  if current_text[3] = #0 then
                    current_kind := TOK_KW_VAR
                  else
                    current_kind := TOK_IDENT
                end
              else
                current_kind := TOK_IDENT
            end
          else
            current_kind := TOK_IDENT
        end
      else
        current_kind := TOK_IDENT;
      if current_kind = TOK_KW_VAR then
        current_kind := TOK_KW_VAR
      else
        begin
          if UpCase(current_text[0]) = 'B' then
            begin
              if UpCase(current_text[1]) = 'E' then
                begin
                  if UpCase(current_text[2]) = 'G' then
                    begin
                      if UpCase(current_text[3]) = 'I' then
                        begin
                          if UpCase(current_text[4]) = 'N' then
                            begin
                              if current_text[5] = #0 then
                                current_kind := TOK_KW_BEGIN
                              else
                                current_kind := TOK_IDENT
                            end
                          else
                            current_kind := TOK_IDENT
                        end
                      else
                        current_kind := TOK_IDENT
                    end
                  else
                    current_kind := TOK_IDENT
                end
              else
                current_kind := TOK_IDENT
            end
          else
            current_kind := TOK_IDENT;
          if current_kind = TOK_KW_BEGIN then
            current_kind := TOK_KW_BEGIN
          else
            begin
              if UpCase(current_text[0]) = 'E' then
                begin
                  if UpCase(current_text[1]) = 'N' then
                    begin
                      if UpCase(current_text[2]) = 'D' then
                        begin
                          if current_text[3] = #0 then
                            current_kind := TOK_KW_END
                          else
                            current_kind := TOK_IDENT
                        end
                      else
                        current_kind := TOK_IDENT
                    end
                  else
                    current_kind := TOK_IDENT
                end
              else
                current_kind := TOK_IDENT;
              if current_kind = TOK_KW_END then
                current_kind := TOK_KW_END
              else
                begin
                  if UpCase(current_text[0]) = 'I' then
                    begin
                      if UpCase(current_text[1]) = 'N' then
                        begin
                          if UpCase(current_text[2]) = 'T' then
                            begin
                              if UpCase(current_text[3]) = 'E' then
                                begin
                                  if UpCase(current_text[4]) = 'G' then
                                    begin
                                      if UpCase(current_text[5]) = 'E' then
                                        begin
                                          if UpCase(current_text[6]) = 'R' then
                                            begin
                                              if current_text[7] = #0 then
                                                current_kind := TOK_KW_INTEGER
                                              else
                                                current_kind := TOK_IDENT
                                            end
                                          else
                                            current_kind := TOK_IDENT
                                        end
                                      else
                                        current_kind := TOK_IDENT
                                    end
                                  else
                                    current_kind := TOK_IDENT
                                end
                              else
                                current_kind := TOK_IDENT
                            end
                          else
                            current_kind := TOK_IDENT
                        end
                      else
                        current_kind := TOK_IDENT
                    end
                  else
                    current_kind := TOK_IDENT;
                  if current_kind = TOK_KW_INTEGER then
                    current_kind := TOK_KW_INTEGER
                  else if StrEqIgnoreCase(current_text, kw_for) then
                    current_kind := TOK_IDENT
                  else if StrEqIgnoreCase(current_text, kw_to) then
                    current_kind := TOK_IDENT
                  else if StrEqIgnoreCase(current_text, kw_do) then
                    current_kind := TOK_IDENT
                  else if StrEqIgnoreCase(current_text, kw_repeat) then
                    current_kind := TOK_IDENT
                  else if StrEqIgnoreCase(current_text, kw_until) then
                    current_kind := TOK_IDENT
                  else if StrEqIgnoreCase(current_text, kw_procedure) then
                    current_kind := TOK_IDENT
                  else if StrEqIgnoreCase(current_text, kw_function) then
                    current_kind := TOK_IDENT
                  else
                    current_kind := TOK_IDENT
                end
            end
        end
    end;
  current_value := 0
end;

procedure ReadNumber;
var
  done: boolean;
  keep: boolean;
  digit: integer;
  ch: char;
begin
  ClearStr(current_text);
  current_value := 0;
  done := false;
  while done = false do
    begin
      keep := false;
      if source_pos >= source_len then
        done := true
      ;
      if done = false then
        begin
          ch := SourceAt(source_pos);
          if ch >= '0' then
            begin
              if ch <= '9' then
                keep := true
            end
        end;
      if keep then
        begin
          AppendChar(current_text, ch);
          digit := Ord(ch) - Ord('0');
          current_value := current_value * 10 + digit;
          AdvanceChar()
        end;
      if done = false then
        begin
          if keep = false then
            done := true
        end
    end;
  current_kind := TOK_INT;
end;

procedure ReadSymbol;
begin
  ClearStr(current_text);
  if MatchPair(':', '=') then
    begin
      AppendChar(current_text, ':');
      AppendChar(current_text, '=');
      AdvanceChar();
      AdvanceChar()
    end
  else if MatchPair('<', '=') then
    begin
      AppendChar(current_text, '<');
      AppendChar(current_text, '=');
      AdvanceChar();
      AdvanceChar()
    end
  else if MatchPair('>', '=') then
    begin
      AppendChar(current_text, '>');
      AppendChar(current_text, '=');
      AdvanceChar();
      AdvanceChar()
    end
  else if MatchPair('<', '>') then
    begin
      AppendChar(current_text, '<');
      AppendChar(current_text, '>');
      AdvanceChar();
      AdvanceChar()
    end
  else if MatchPair('.', '.') then
    begin
      AppendChar(current_text, '.');
      AppendChar(current_text, '.');
      AdvanceChar();
      AdvanceChar()
    end
  else
    begin
      AppendChar(current_text, SourceAt(source_pos));
      AdvanceChar()
    end;
  current_kind := TOK_SYMBOL;
  current_value := 0
end;

procedure ReadString;
var
  done: boolean;
begin
  ClearStr(current_text);
  current_kind := TOK_STR;
  current_value := 0;
  AdvanceChar();
  done := false;
  while done = false do
    begin
      if source_pos >= source_len then
        done := true
      else if SourceAt(source_pos) = '''' then
        begin
          AdvanceChar();
          done := true
        end
      else
        begin
          AppendChar(current_text, SourceAt(source_pos));
          AdvanceChar()
        end
    end
end;

procedure NextToken;
var
  ch: char;
begin
  SkipSpaces();
  if source_pos >= source_len then
    begin
      ClearStr(current_text);
      current_kind := TOK_EOF;
      current_value := 0
    end
  else
    begin
      ch := SourceAt(source_pos);
      if ch = '''' then
        ReadString()
      else if ch >= 'A' then
        begin
          if ch <= 'Z' then
            ReadIdentifier()
          else if ch >= 'a' then
            begin
              if ch <= 'z' then
                ReadIdentifier()
              else
                ReadSymbol()
            end
          else if ch = '_' then
            ReadIdentifier()
          else if ch >= '0' then
            begin
              if ch <= '9' then
                ReadNumber()
              else
                ReadSymbol()
            end
          else
            ReadSymbol()
        end
      else if ch = '_' then
        ReadIdentifier()
      else if ch >= 'a' then
        begin
          if ch <= 'z' then
            ReadIdentifier()
          else
            ReadSymbol()
        end
      else if ch >= '0' then
        begin
          if ch <= '9' then
            ReadNumber()
          else
            ReadSymbol()
        end
      else
        ReadSymbol()
    end
end;

procedure WriteToken;
begin
  if current_kind = TOK_IDENT then
    begin
      Write('IDENT ');
      WriteLn(current_text)
    end
  else if current_kind = TOK_INT then
    begin
      Write('INT ');
      WriteLn(current_value)
    end
  else if current_kind = TOK_SYMBOL then
    begin
      Write('SYM ');
      WriteLn(current_text)
    end
  else if current_kind = TOK_STR then
    begin
      Write('STR ');
      WriteLn(current_text)
    end
  else if current_kind = TOK_KW_PROGRAM then
    WriteLn('KW program')
  else if current_kind = TOK_KW_VAR then
    WriteLn('KW var')
  else if current_kind = TOK_KW_BEGIN then
    WriteLn('KW begin')
  else if current_kind = TOK_KW_END then
    WriteLn('KW end')
  else if current_kind = TOK_KW_INTEGER then
    WriteLn('KW integer')
  else if StrEqIgnoreCase(current_text, kw_writeln) then
    WriteLn('KW writeln')
  else
    WriteLn('EOF')
end;
