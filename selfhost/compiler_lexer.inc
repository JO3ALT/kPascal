procedure FailParse;
begin
  Write('p');
  Write('a');
  Write('r');
  Write('s');
  Write('e');
  Write(' ');
  Write('e');
  Write('r');
  Write('r');
  Write('o');
  Write('r');
  Write(' ');
  Write(parse_error_reason);
  Write(' ');
  Write(token_kind);
  Write(' ');
  Write(ast_stmt_count);
  Write(' ');
  Write(ast_expr_count);
  Write(' ');
  Write(ast_arg_count);
  WriteLn()
end;

function IsLetter(ch: char): boolean;
begin
  if ch >= 'a' then
    begin
      if ch <= 'z' then
        IsLetter := true
      else
        IsLetter := false
    end
  else if ch >= 'A' then
    begin
      if ch <= 'Z' then
        IsLetter := true
      else
        IsLetter := false
    end
  else if ch = '_' then
    begin
      IsLetter := true
    end
  else
    begin
      IsLetter := false
    end
end;

function IsDigit(ch: char): boolean;
begin
  if ch >= '0' then
    begin
      if ch <= '9' then
        IsDigit := true
      else
        IsDigit := false
    end
  else
    begin
      IsDigit := false
    end
end;

function IsIdentChar(ch: char): boolean;
begin
  if IsLetter(ch) then
    begin
      IsIdentChar := true
    end
  else if IsDigit(ch) then
    begin
      IsIdentChar := true
    end
  else
    begin
      IsIdentChar := false
    end
end;

procedure ClearToken;
begin
  token_value := 0;
  ClearText(token_text)
end;

procedure SkipWhitespace;
begin
  PrimeSourceStream();
  if not stream_eof then
    begin
      if stream_current_char <= ' ' then
        begin
          AdvanceSourceStream();
          SkipWhitespace()
        end
    end
end;

procedure ClassifyIdentifierToken;
begin
  if StrCmp(token_text, kw_program) = 0 then
    token_kind := TOK_KW_PROGRAM
  else if StrCmp(token_text, kw_const) = 0 then
    token_kind := TOK_KW_CONST
  else if StrCmp(token_text, kw_type) = 0 then
    token_kind := TOK_KW_TYPE
  else if StrCmp(token_text, kw_var) = 0 then
    token_kind := TOK_KW_VAR
  else if StrCmp(token_text, kw_procedure) = 0 then
    token_kind := TOK_KW_PROCEDURE
  else if StrCmp(token_text, kw_function) = 0 then
    token_kind := TOK_KW_FUNCTION
  else if StrCmp(token_text, kw_begin) = 0 then
    token_kind := TOK_KW_BEGIN
  else if StrCmp(token_text, kw_end) = 0 then
    token_kind := TOK_KW_END
  else if StrCmp(token_text, kw_read) = 0 then
    token_kind := TOK_KW_READ
  else if StrCmp(token_text, kw_readln) = 0 then
    token_kind := TOK_KW_READLN
  else if StrCmp(token_text, kw_write) = 0 then
    token_kind := TOK_KW_WRITE
  else if StrCmp(token_text, kw_writeln) = 0 then
    token_kind := TOK_KW_WRITELN
  else if StrCmp(token_text, kw_for) = 0 then
    token_kind := TOK_KW_FOR
  else if StrCmp(token_text, kw_to) = 0 then
    token_kind := TOK_KW_TO
  else if StrCmp(token_text, kw_downto) = 0 then
    token_kind := TOK_KW_DOWNTO
  else if StrCmp(token_text, kw_do) = 0 then
    token_kind := TOK_KW_DO
  else if StrCmp(token_text, kw_case) = 0 then
    token_kind := TOK_KW_CASE
  else if StrCmp(token_text, kw_of) = 0 then
    token_kind := TOK_KW_OF
  else if StrCmp(token_text, kw_else) = 0 then
    token_kind := TOK_KW_ELSE
  else if StrCmp(token_text, kw_if) = 0 then
    token_kind := TOK_KW_IF
  else if StrCmp(token_text, kw_then) = 0 then
    token_kind := TOK_KW_THEN
  else if StrCmp(token_text, kw_with) = 0 then
    token_kind := TOK_KW_WITH
  else if StrCmp(token_text, kw_while) = 0 then
    token_kind := TOK_KW_WHILE
  else if StrCmp(token_text, kw_repeat) = 0 then
    token_kind := TOK_KW_REPEAT
  else if StrCmp(token_text, kw_until) = 0 then
    token_kind := TOK_KW_UNTIL
  else if StrCmp(token_text, kw_record) = 0 then
    token_kind := TOK_KW_RECORD
  else if StrCmp(token_text, kw_array) = 0 then
    token_kind := TOK_KW_ARRAY
  else if StrCmp(token_text, kw_set) = 0 then
    token_kind := TOK_KW_SET
  else if StrCmp(token_text, kw_true) = 0 then
    token_kind := TOK_KW_TRUE
  else if StrCmp(token_text, kw_false) = 0 then
    token_kind := TOK_KW_FALSE
  else if StrCmp(token_text, kw_nil) = 0 then
    token_kind := TOK_KW_NIL
  else if StrCmp(token_text, kw_in) = 0 then
    token_kind := TOK_KW_IN
  else if StrCmp(token_text, kw_div) = 0 then
    token_kind := TOK_KW_DIV
  else if StrCmp(token_text, kw_mod) = 0 then
    token_kind := TOK_KW_MOD
  else if StrCmp(token_text, kw_and) = 0 then
    token_kind := TOK_KW_AND
  else if StrCmp(token_text, kw_or) = 0 then
    token_kind := TOK_KW_OR
  else if StrCmp(token_text, kw_xor) = 0 then
    token_kind := TOK_KW_XOR
  else if StrCmp(token_text, kw_not) = 0 then
    token_kind := TOK_KW_NOT
  else if StrCmp(token_text, kw_integer) = 0 then
    token_kind := TOK_KW_INTEGER
  else if StrCmp(token_text, kw_boolean) = 0 then
    token_kind := TOK_KW_BOOLEAN
  else if StrCmp(token_text, kw_char) = 0 then
    token_kind := TOK_KW_CHAR
  else if StrCmp(token_text, kw_real) = 0 then
    token_kind := TOK_KW_REAL
  else
    token_kind := TOK_IDENT
end;

procedure ReadIdentifierToken;
var i: integer;
begin
  ClearToken();
  i := 0;
  while i < 100000 do
    begin
      if stream_eof then
        begin
          i := 100000
        end
      else if stream_current_char = '_' then
        begin
          if i <= 255 then
            token_text[i] := stream_current_char;
          i := i + 1;
          AdvanceSourceStream()
        end
      else if stream_current_char < '0' then
        begin
          i := 100000
        end
      else if stream_current_char <= '9' then
        begin
          if i <= 255 then
            token_text[i] := stream_current_char;
          i := i + 1;
          AdvanceSourceStream()
        end
      else if stream_current_char < 'A' then
        begin
          i := 100000
        end
      else if stream_current_char <= 'Z' then
        begin
          if i <= 255 then
            token_text[i] := Chr(Ord(stream_current_char) + 32);
          i := i + 1;
          AdvanceSourceStream()
        end
      else if stream_current_char < 'a' then
        begin
          i := 100000
        end
      else if stream_current_char <= 'z' then
        begin
          if i <= 255 then
            token_text[i] := stream_current_char;
          i := i + 1;
          AdvanceSourceStream()
        end
      else
        begin
          i := 100000
        end
    end;
  ClassifyIdentifierToken()
end;

procedure ReadNumberToken;
var i: integer;
    frac_value: integer;
    frac_nonzero: boolean;
    peek_char: char;
begin
  ClearToken();
  i := 0;
  frac_value := 0;
  frac_nonzero := false;
  while i < 100000 do
    begin
      if stream_eof then
        begin
          i := 100000
        end
      else if IsDigit(stream_current_char) then
        begin
          token_value := token_value * 10 + Ord(stream_current_char) - Ord('0');
          i := i + 1;
          AdvanceSourceStream()
        end
      else
        begin
          i := 100000
        end
    end;
  if stream_current_char = '.' then
    begin
      AdvanceSourceStream();
      if IsDigit(stream_current_char) then
        begin
          while i < 100000 do
            begin
              if stream_eof then
                begin
                  i := 100000
                end
              else if IsDigit(stream_current_char) then
                begin
                  frac_value := frac_value * 10 + Ord(stream_current_char) - Ord('0');
                  if stream_current_char <> '0' then
                    begin
                      frac_nonzero := true
                    end;
                  i := i + 1;
                  AdvanceSourceStream()
                end
              else
                begin
                  i := 100000
                end
            end;
          token_kind := TOK_REAL_LIT;
          if frac_nonzero then
            begin
              bootstrap_capture_failed := true
            end
        end
      else
        begin
          peek_char := stream_current_char;
          source_buffered_char := peek_char;
          source_has_buffered_char := true;
          stream_current_char := '.';
          stream_eof := false;
          token_kind := TOK_INT
        end
    end
  else
    begin
      token_kind := TOK_INT
    end
end;

procedure ReadCharCodeToken;
var i: integer;
begin
  ClearToken();
  token_value := 0;
  AdvanceSourceStream();
  i := 0;
  while i < 100000 do
    begin
      if stream_eof then
        begin
          i := 100000
        end
      else if IsDigit(stream_current_char) then
        begin
          token_value := token_value * 10 + Ord(stream_current_char) - Ord('0');
          i := i + 1;
          AdvanceSourceStream()
        end
      else
        begin
          i := 100000
        end
    end;
  token_kind := TOK_INT
end;

procedure ReadStringToken;
var i: integer;
begin
  ClearToken();
  i := 0;
  AdvanceSourceStream();
  while i < 100000 do
    begin
      if stream_eof then
        begin
          i := 100000
        end
      else if stream_current_char = '''' then
        begin
          AdvanceSourceStream();
          if stream_current_char = '''' then
            begin
              if i <= 255 then
                token_text[i] := '''';
              i := i + 1;
              AdvanceSourceStream()
            end
          else
            begin
              i := 100000
            end
        end
      else
        begin
          if i <= 255 then
            token_text[i] := stream_current_char;
          i := i + 1;
          AdvanceSourceStream()
        end
    end;
  token_kind := TOK_STR
end;

procedure ReadSymbolToken;
begin
  ClearToken();
  if stream_current_char = '(' then
    begin
      token_kind := TOK_LPAREN;
      AdvanceSourceStream()
    end
  else if stream_current_char = ')' then
    begin
      token_kind := TOK_RPAREN;
      AdvanceSourceStream()
    end
  else if stream_current_char = '[' then
    begin
      token_kind := TOK_LBRACK;
      AdvanceSourceStream()
    end
  else if stream_current_char = ']' then
    begin
      token_kind := TOK_RBRACK;
      AdvanceSourceStream()
    end
  else if stream_current_char = ';' then
    begin
      token_kind := TOK_SEMI;
      AdvanceSourceStream()
    end
  else if stream_current_char = ':' then
    begin
      AdvanceSourceStream();
      if stream_current_char = '=' then
        begin
          token_kind := TOK_ASSIGN;
          AdvanceSourceStream()
        end
      else
        begin
          token_kind := TOK_COLON
        end
    end
  else if stream_current_char = ',' then
    begin
      token_kind := TOK_COMMA;
      AdvanceSourceStream()
    end
  else if stream_current_char = '.' then
    begin
      AdvanceSourceStream();
      if stream_current_char = '.' then
        begin
          token_kind := TOK_DOTDOT;
          AdvanceSourceStream()
        end
      else
        begin
          token_kind := TOK_DOT
        end
    end
  else if stream_current_char = '^' then
    begin
      token_kind := TOK_CARET;
      AdvanceSourceStream()
    end
  else if stream_current_char = '=' then
    begin
      token_kind := TOK_EQ;
      AdvanceSourceStream()
    end
  else if stream_current_char = '<' then
    begin
      AdvanceSourceStream();
      if stream_current_char = '=' then
        begin
          token_kind := TOK_LE;
          AdvanceSourceStream()
        end
      else if stream_current_char = '>' then
        begin
          token_kind := TOK_NE;
          AdvanceSourceStream()
        end
      else
        begin
          token_kind := TOK_LT
        end
    end
  else if stream_current_char = '>' then
    begin
      AdvanceSourceStream();
      if stream_current_char = '=' then
        begin
          token_kind := TOK_GE;
          AdvanceSourceStream()
        end
      else
        begin
          token_kind := TOK_GT
        end
    end
  else if stream_current_char = '+' then
    begin
      token_kind := TOK_PLUS;
      AdvanceSourceStream()
    end
  else if stream_current_char = '-' then
    begin
      token_kind := TOK_MINUS;
      AdvanceSourceStream()
    end
  else if stream_current_char = '*' then
    begin
      token_kind := TOK_STAR;
      AdvanceSourceStream()
    end
  else if stream_current_char = '/' then
    begin
      token_kind := TOK_SLASH;
      AdvanceSourceStream()
    end
  else
    begin
      FailParse()
    end
end;

procedure ReadToken;
begin
  SkipWhitespace();
  if stream_eof then
    begin
      token_kind := TOK_EOF;
      ClearToken()
    end
  else if stream_current_char = '_' then
    begin
      ReadIdentifierToken()
    end
  else if stream_current_char = '''' then
    begin
      ReadStringToken()
    end
  else if stream_current_char = '#' then
    begin
      ReadCharCodeToken()
    end
  else if stream_current_char < '0' then
    begin
      ReadSymbolToken()
    end
  else if stream_current_char <= '9' then
    begin
      ReadNumberToken()
    end
  else if stream_current_char < 'A' then
    begin
      ReadSymbolToken()
    end
  else if stream_current_char <= 'Z' then
    begin
      ReadIdentifierToken()
    end
  else if stream_current_char < 'a' then
    begin
      ReadSymbolToken()
    end
  else if stream_current_char <= 'z' then
    begin
      ReadIdentifierToken()
    end
  else
    begin
      ReadSymbolToken()
    end
end;

procedure ExpectToken(kind: integer);
begin
  if token_kind <> kind then
    begin
      parse_error_reason := 1;
      FailParse()
    end;
  ReadToken()
end;

procedure ExpectIdent(var dst: text_buf);
begin
  if token_kind <> TOK_IDENT then
    begin
      parse_error_reason := 2;
      FailParse()
    end;
  StrCopy(token_text, dst);
  ReadToken()
end;

procedure NextToken;
begin
  ReadToken()
end;

procedure ReadString;
begin
  ReadStringToken()
end;

procedure ReadNumber;
begin
  ReadNumberToken()
end;

procedure ReadSymbol;
begin
  ReadSymbolToken()
end;

procedure WriteToken;
begin
  WriteLn(token_kind)
end;

procedure ExpectKind(kind: integer);
begin
  ExpectToken(kind)
end;

procedure ExpectAssignSymbol;
begin
  ExpectToken(TOK_ASSIGN)
end;

procedure ExpectSymbolChar(kind: integer);
begin
  ExpectToken(kind)
end;
