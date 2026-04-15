type
  text_buf = array[0..255] of char;
  text_cell_ptr = ^integer;

procedure ClearStr(var s: text_buf);
var i: integer;
    p: text_cell_ptr;
    addr: integer;
begin
  addr := Addr(s);
  for i := 0 to 255 do
    begin
      SetAddr(p, addr);
      p^ := 0;
      addr := addr + 4
    end
end;

procedure ClearText(var s: text_buf);
var i: integer;
    p: text_cell_ptr;
    addr: integer;
begin
  addr := Addr(s);
  for i := 0 to 255 do
    begin
      SetAddr(p, addr);
      p^ := 0;
      addr := addr + 4
    end
end;

function StrLen(var s: text_buf): integer;
var i: integer;
begin
  StrLen := 256;
  i := 0;
  while i <= 255 do
    begin
      if s[i] = #0 then
        begin
          StrLen := i;
          i := 256
        end
      else
        begin
          i := i + 1
        end
    end
end;

procedure AppendChar(var s: text_buf; ch: char);
var len: integer;
begin
  len := StrLen(s);
  if len < 255 then
    begin
      s[len] := ch;
      s[len + 1] := #0
    end
end;

procedure AppendStr(var dst: text_buf; var src: text_buf);
var dst_len: integer;
    i: integer;
    copying: boolean;
begin
  dst_len := StrLen(dst);
  copying := true;
  for i := 0 to 255 do
    begin
      if copying then
        begin
          if src[i] = #0 then
            copying := false
          else if dst_len < 255 then
            begin
              dst[dst_len] := src[i];
              dst_len := dst_len + 1
            end
        end
    end;
  if dst_len <= 255 then
    dst[dst_len] := #0
end;

procedure CopyTextToCharArray(var src: text_buf; var dst: text_buf);
var i: integer;
    copying: boolean;
    src_ptr: text_cell_ptr;
    dst_ptr: text_cell_ptr;
    src_addr: integer;
    dst_addr: integer;
    cell: integer;
begin
  src_addr := Addr(src);
  dst_addr := Addr(dst);
  copying := true;
  for i := 0 to 255 do
    begin
      SetAddr(src_ptr, src_addr);
      SetAddr(dst_ptr, dst_addr);
      if copying then
        begin
          cell := src_ptr^;
          dst_ptr^ := cell;
          if cell = 0 then
            copying := false
        end
      else
        dst_ptr^ := 0;
      src_addr := src_addr + 4;
      dst_addr := dst_addr + 4
    end
end;

procedure StrCopy(var src: text_buf; var dst: text_buf);
var i: integer;
begin
  for i := 0 to 255 do
    begin
      dst[i] := src[i];
    end
end;

function StrCmp(var a: text_buf; var b: text_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmp := 0;
  done := false;
  for i := 0 to 255 do
    begin
      if done = false then
        begin
          if a[i] <> b[i] then
            begin
              StrCmp := Ord(a[i]) - Ord(b[i]);
              done := true
            end
          else if a[i] = #0 then
            begin
              done := true
            end
        end
    end
end;

function ToLowerChar(ch: char): char;
begin
  if ch >= 'A' then
    begin
      if ch <= 'Z' then
        ToLowerChar := Chr(Ord(ch) + 32)
      else
        ToLowerChar := ch
    end
  else
    ToLowerChar := ch
end;

function StrCmpIgnoreCase(var a: text_buf; var b: text_buf): integer;
var i: integer;
    ca: char;
    cb: char;
    done: boolean;
begin
  StrCmpIgnoreCase := 0;
  done := false;
  for i := 0 to 255 do
    begin
      if done = false then
        begin
          ca := ToLowerChar(a[i]);
          cb := ToLowerChar(b[i]);
          if ca <> cb then
            begin
              StrCmpIgnoreCase := Ord(ca) - Ord(cb);
              done := true
            end
          else if ca = #0 then
            begin
              done := true
            end
        end
    end
end;

function StrEq(var a: text_buf; var b: text_buf): boolean;
begin
  StrEq := StrCmp(a, b) = 0
end;

function StrEqIgnoreCase(var a: text_buf; var b: text_buf): boolean;
begin
  StrEqIgnoreCase := StrCmpIgnoreCase(a, b) = 0
end;

function StartsWith(var text: text_buf; var prefix: text_buf): boolean;
var i: integer;
    ok: boolean;
    done: boolean;
begin
  ok := true;
  done := false;
  for i := 0 to 255 do
    begin
      if done = false then
        begin
          if prefix[i] = #0 then
            done := true
          else if text[i] <> prefix[i] then
            begin
              ok := false;
              done := true
            end
        end
    end;
  StartsWith := ok
end;

procedure TrimLeft(var s: text_buf);
var i: integer;
    start_idx: integer;
    write_idx: integer;
    found: boolean;
    copying: boolean;
begin
  start_idx := 256;
  found := false;
  for i := 0 to 255 do
    begin
      if found = false then
        begin
          if s[i] = #0 then
            begin
              start_idx := 256;
              found := true
            end
          else if s[i] > ' ' then
            begin
              start_idx := i;
              found := true
            end
        end
    end;
  write_idx := 0;
  copying := true;
  if start_idx <= 255 then
    begin
      for i := start_idx to 255 do
        begin
          if copying then
            begin
              if s[i] = #0 then
                copying := false
              else
                begin
                  s[write_idx] := s[i];
                  write_idx := write_idx + 1
                end
            end
        end
    end;
  while write_idx <= 255 do
    begin
      s[write_idx] := #0;
      write_idx := write_idx + 1
    end
end;

procedure TrimRight(var s: text_buf);
var len: integer;
    trimming: boolean;
begin
  len := StrLen(s);
  trimming := true;
  while len > 0 do
    begin
      if trimming then
        begin
          if s[len - 1] <= ' ' then
            begin
              s[len - 1] := #0;
              len := len - 1
            end
          else
            trimming := false
        end
      else
        len := 0
    end
end;

function ParseInt(var src: text_buf; var value: integer): boolean;
var i: integer;
    sign: integer;
    digits: integer;
    start_idx: integer;
    found: boolean;
    ch: char;
begin
  start_idx := 256;
  found := false;
  for i := 0 to 255 do
    begin
      if found = false then
        begin
          if src[i] = #0 then
            begin
              start_idx := 256;
              found := true
            end
          else if src[i] > ' ' then
            begin
              start_idx := i;
              found := true
            end
        end
    end;

  if start_idx > 255 then
    begin
      ParseInt := false;
      value := 0
    end
  else
    begin
      i := start_idx;
      sign := 1;
      if src[i] = '+' then
        i := i + 1
      else if src[i] = '-' then
        begin
          sign := -1;
          i := i + 1
        end;
      value := 0;
      digits := 0;
      while i <= 255 do
        begin
          ch := src[i];
          if ch >= '0' then
            begin
              if ch <= '9' then
                begin
                  value := value * 10 + (Ord(ch) - Ord('0'));
                  digits := digits + 1;
                  i := i + 1
                end
              else
                i := 256
            end
          else
            i := 256
        end;
      if digits = 0 then
        ParseInt := false
      else
        begin
          value := value * sign;
          ParseInt := true
        end
    end
end;

procedure InitStringUtils;
begin
  kw_program := 'program';
  kw_const := 'const';
  kw_type := 'type';
  kw_var := 'var';
  kw_procedure := 'procedure';
  kw_function := 'function';
  kw_begin := 'begin';
  kw_end := 'end';
  kw_read := 'read';
  kw_readln := 'readln';
  kw_write := 'write';
  kw_writeln := 'writeln';
  kw_for := 'for';
  kw_to := 'to';
  kw_downto := 'downto';
  kw_do := 'do';
  kw_case := 'case';
  kw_of := 'of';
  kw_else := 'else';
  kw_if := 'if';
  kw_then := 'then';
  kw_with := 'with';
  kw_while := 'while';
  kw_repeat := 'repeat';
  kw_until := 'until';
  kw_record := 'record';
  kw_array := 'array';
  kw_set := 'set';
  kw_true := 'true';
  kw_false := 'false';
  kw_nil := 'nil';
  kw_in := 'in';
  kw_div := 'div';
  kw_mod := 'mod';
  kw_and := 'and';
  kw_or := 'or';
  kw_xor := 'xor';
  kw_not := 'not';
  kw_integer := 'integer';
  kw_boolean := 'boolean';
  kw_char := 'char';
  kw_real := 'real'
end;
