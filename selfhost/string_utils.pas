procedure ClearStr(var s: array of char);
var i: integer;
begin
  for i := 0 to High(s) do
    s[i] := #0
end;

function StrLen(var s: array of char): integer;
var i: integer;
begin
  i := 0;
  while (i <= High(s)) and (s[i] <> #0) do
    i := i + 1;
  StrLen := i
end;

procedure AppendChar(var s: array of char; ch: char);
var len: integer;
begin
  len := StrLen(s);
  if len >= High(s) then
    exit;
  s[len] := ch;
  s[len + 1] := #0
end;

procedure AppendStr(var dst: array of char; var src: array of char);
var dst_len, i: integer;
begin
  dst_len := StrLen(dst);
  i := 0;
  while (i <= High(src)) and (src[i] <> #0) and (dst_len < High(dst)) do
    begin
      dst[dst_len] := src[i];
      dst_len := dst_len + 1;
      i := i + 1
    end;
  if dst_len <= High(dst) then
    dst[dst_len] := #0
end;

procedure CopyTextToCharArray(var src: array of char; var dst: array of char);
var i: integer;
begin
  i := 0;
  while (i <= High(dst)) and (i <= High(src)) and (src[i] <> #0) do
    begin
      dst[i] := src[i];
      i := i + 1
    end;
  if i <= High(dst) then
    dst[i] := #0;
  while i <= High(dst) do
    begin
      dst[i] := #0;
      i := i + 1
    end
end;

procedure StrCopy(var src: array of char; var dst: array of char);
var i: integer;
begin
  i := 0;
  while (i <= High(src)) and (src[i] <> #0) do
    begin
      if i <= High(dst) then
        dst[i] := src[i];
      i := i + 1
    end;
  if i <= High(dst) then
    dst[i] := #0
end;

function StrCmp(var a: array of char; var b: array of char): integer;
var i: integer;
begin
  i := 0;
  while (i <= High(a)) and (i <= High(b)) do
    begin
      if a[i] <> b[i] then
        begin
          StrCmp := Ord(a[i]) - Ord(b[i]);
          exit
        end;
      if a[i] = #0 then
        begin
          StrCmp := 0;
          exit
        end;
      i := i + 1
    end;
  StrCmp := 0
end;

function ToLowerChar(ch: char): char;
begin
  if (ch >= 'A') and (ch <= 'Z') then
    ToLowerChar := Chr(Ord(ch) + 32)
  else
    ToLowerChar := ch
end;

function StrCmpIgnoreCase(var a: array of char; var b: array of char): integer;
var i: integer;
    ca, cb: char;
begin
  i := 0;
  while (i <= High(a)) and (i <= High(b)) do
    begin
      ca := ToLowerChar(a[i]);
      cb := ToLowerChar(b[i]);
      if ca <> cb then
        begin
          StrCmpIgnoreCase := Ord(ca) - Ord(cb);
          exit
        end;
      if ca = #0 then
        begin
          StrCmpIgnoreCase := 0;
          exit
        end;
      i := i + 1
    end;
  StrCmpIgnoreCase := 0
end;

function StrEq(var a: array of char; var b: array of char): boolean;
begin
  StrEq := StrCmp(a, b) = 0
end;

function StrEqIgnoreCase(var a: array of char; var b: array of char): boolean;
begin
  StrEqIgnoreCase := StrCmpIgnoreCase(a, b) = 0
end;

function StrEqLit(var buf: array of char; const target: string): boolean;
var i: integer;
begin
  i := 0;
  while (i < Length(target)) and (i <= High(buf)) do
    begin
      if buf[i] = #0 then
        begin
          StrEqLit := false;
          exit
        end;
      if buf[i] <> target[i + 1] then
        begin
          StrEqLit := false;
          exit
        end;
      i := i + 1
    end;
  if i < Length(target) then
    begin
      StrEqLit := false;
      exit
    end;
  if (i <= High(buf)) and (buf[i] <> #0) then
    StrEqLit := false
  else
    StrEqLit := true
end;

function StrEqIgnoreCaseLit(var buf: array of char; const target: string): boolean;
var i: integer;
    ch: char;
begin
  i := 0;
  while (i < Length(target)) and (i <= High(buf)) do
    begin
      ch := buf[i];
      if ch = #0 then
        begin
          StrEqIgnoreCaseLit := false;
          exit
        end;
      if ToLowerChar(ch) <> ToLowerChar(target[i + 1]) then
        begin
          StrEqIgnoreCaseLit := false;
          exit
        end;
      i := i + 1
    end;
  if i < Length(target) then
    begin
      StrEqIgnoreCaseLit := false;
      exit
    end;
  if (i <= High(buf)) and (buf[i] <> #0) then
    StrEqIgnoreCaseLit := false
  else
    StrEqIgnoreCaseLit := true
end;

function HasNameEqIgnoreCase(var buf: array of char; const target: string): boolean;
begin
  HasNameEqIgnoreCase := StrEqIgnoreCaseLit(buf, target)
end;

function StartsWith(var text: array of char; var prefix: array of char): boolean;
var i: integer;
begin
  i := 0;
  while (i <= High(prefix)) and (prefix[i] <> #0) do
    begin
      if (i > High(text)) or (text[i] <> prefix[i]) then
        begin
          StartsWith := false;
          exit
        end;
      i := i + 1
    end;
  StartsWith := true
end;

procedure TrimLeft(var s: array of char);
var read_idx, write_idx: integer;
begin
  read_idx := 0;
  while (read_idx <= High(s)) and (s[read_idx] <> #0) and (s[read_idx] <= ' ') do
    read_idx := read_idx + 1;
  write_idx := 0;
  while (read_idx <= High(s)) and (s[read_idx] <> #0) do
    begin
      s[write_idx] := s[read_idx];
      write_idx := write_idx + 1;
      read_idx := read_idx + 1
    end;
  while write_idx <= High(s) do
    begin
      s[write_idx] := #0;
      write_idx := write_idx + 1
    end
end;

procedure TrimRight(var s: array of char);
var len: integer;
begin
  len := StrLen(s);
  while (len > 0) and (s[len - 1] <= ' ') do
    begin
      s[len - 1] := #0;
      len := len - 1
    end
end;

function ParseInt(var src: array of char; var value: integer): boolean;
var i, sign, digits: integer;
    ch: char;
begin
  i := 0;
  while (i <= High(src)) and (src[i] <> #0) and (src[i] <= ' ') do
    i := i + 1;
  sign := 1;
  if (i <= High(src)) and (src[i] = '+') then
    i := i + 1
  else if (i <= High(src)) and (src[i] = '-') then
    begin
      sign := -1;
      i := i + 1
    end;
  value := 0;
  digits := 0;
  while (i <= High(src)) do
    begin
      ch := src[i];
      if (ch >= '0') and (ch <= '9') then
        begin
          value := value * 10 + (Ord(ch) - Ord('0'));
          digits := digits + 1;
          i := i + 1
        end
      else
        break
    end;
  if digits = 0 then
    begin
      ParseInt := false;
      exit
    end;
  value := value * sign;
  ParseInt := true
end;
