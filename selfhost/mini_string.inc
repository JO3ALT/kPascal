procedure ClearStr(var dst: lexeme_buf);
var
  i: integer;
begin
  i := 0;
  while i < 32 do
    begin
      dst[i] := #0;
      i := i + 1
    end
end;

procedure AppendChar(var dst: lexeme_buf; ch: char);
var
  i: integer;
begin
  i := 0;
  while i < 32 do
    begin
      if dst[i] = #0 then
        begin
          dst[i] := ch;
          if i < 31 then
            dst[i + 1] := #0;
          i := 32
        end
      else
        i := i + 1
    end
end;

procedure StrCopy(var src: lexeme_buf; var dst: lexeme_buf);
var
  i: integer;
  done: boolean;
begin
  i := 0;
  done := false;
  while i < 32 do
    begin
      if done then
        dst[i] := #0
      else
        begin
          dst[i] := src[i];
          if src[i] = #0 then
            done := true
        end;
      i := i + 1
    end
end;

function StrEqIgnoreCase(var lhs: lexeme_buf; var rhs: lexeme_buf): boolean;
var
  i: integer;
  ok: boolean;
begin
  i := 0;
  ok := true;
  while i < 32 do
    begin
      if UpCase(lhs[i]) <> UpCase(rhs[i]) then
        begin
          ok := false;
          i := 32
        end
      else if lhs[i] = #0 then
        i := 32
      else
        i := i + 1
    end;
  StrEqIgnoreCase := ok
end;
