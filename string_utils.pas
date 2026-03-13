procedure ClearStr(var dst: array[dst_lo..dst_hi: integer] of char);
var
  i: integer;
begin
  for i := dst_lo to dst_hi do
    dst[i] := #0
end;

procedure AppendChar(var dst: array[dst_lo..dst_hi: integer] of char; ch: char);
var
  i: integer;
  pos: integer;
begin
  i := dst_lo;
  pos := dst_hi + 1;
  while i <= dst_hi do
    begin
      if dst[i] = #0 then
        begin
          pos := i;
          i := dst_hi + 1
        end
      else
        i := i + 1
    end;
  if pos <= dst_hi then
    begin
      dst[pos] := ch;
      if pos < dst_hi then
        dst[pos + 1] := #0
    end
end;

procedure AppendStr(src: array[src_lo..src_hi: integer] of char;
                    var dst: array[dst_lo..dst_hi: integer] of char);
var
  i: integer;
  j: integer;
  done: boolean;
begin
  j := dst_lo;
  done := false;
  while j <= dst_hi do
    begin
      if dst[j] = #0 then
        done := true
      else if done then
        j := dst_hi + 1
      else
        j := j + 1
    end;
  if j <= dst_hi then
    begin
      i := src_lo;
      done := false;
      while i <= src_hi do
        begin
          if done then
            i := src_hi + 1
          else if j > dst_hi then
            done := true
          else if src[i] = #0 then
            done := true
          else
            begin
              dst[j] := src[i];
              i := i + 1;
              j := j + 1
            end
        end;
      if j <= dst_hi then
        dst[j] := #0
    end
end;

procedure StrCopy(src: array[src_lo..src_hi: integer] of char;
                  var dst: array[dst_lo..dst_hi: integer] of char);
var
  i: integer;
  j: integer;
  done: boolean;
begin
  j := dst_lo;
  i := src_lo;
  done := false;
  while i <= src_hi do
    begin
      if done then
        i := src_hi + 1
      else if j > dst_hi then
        done := true
      else if src[i] = #0 then
        done := true
      else
        begin
          dst[j] := src[i];
          i := i + 1;
          j := j + 1
        end
    end;
  if j <= dst_hi then
    dst[j] := #0;
  j := j + 1;
  while j <= dst_hi do
    begin
      dst[j] := #0;
      j := j + 1
    end
end;

function StrEq(lhs: array[lhs_lo..lhs_hi: integer] of char;
               rhs: array[rhs_lo..rhs_hi: integer] of char): boolean;
var
  ia: integer;
  ib: integer;
  same: boolean;
  done: boolean;
begin
  ia := lhs_lo;
  ib := rhs_lo;
  same := true;
  done := false;
  while ia <= lhs_hi do
    begin
      if done then
        ia := lhs_hi + 1
      else if ib > rhs_hi then
        done := true
      else if lhs[ia] = #0 then
        done := true
      else if rhs[ib] = #0 then
        done := true
      else if lhs[ia] <> rhs[ib] then
        begin
          same := false;
          done := true
        end
      else
        begin
          ia := ia + 1;
          ib := ib + 1
        end
    end;
  if not same then
    StrEq := false
  else
    begin
      StrEq := true;
      if ia <= lhs_hi then
        begin
          if lhs[ia] <> #0 then
            StrEq := false
        end;
      if ib <= rhs_hi then
        begin
          if rhs[ib] <> #0 then
            StrEq := false
        end
    end
end;

function StrCmp(lhs: array[lhs_lo..lhs_hi: integer] of char;
                rhs: array[rhs_lo..rhs_hi: integer] of char): integer;
var
  ia: integer;
  ib: integer;
  done: boolean;
  result_value: integer;
begin
  ia := lhs_lo;
  ib := rhs_lo;
  done := false;
  result_value := 0;
  while ia <= lhs_hi do
    begin
      if done then
        ia := lhs_hi + 1
      else if ib > rhs_hi then
        done := true
      else if lhs[ia] = #0 then
        done := true
      else if rhs[ib] = #0 then
        done := true
      else if lhs[ia] < rhs[ib] then
        begin
          result_value := -1;
          done := true
        end
      else if lhs[ia] > rhs[ib] then
        begin
          result_value := 1;
          done := true
        end
      else
        begin
          ia := ia + 1;
          ib := ib + 1
        end
    end;
  if result_value <> 0 then
    StrCmp := result_value
  else
    begin
      if ia > lhs_hi then
        StrCmp := 0
      else if ib > rhs_hi then
        StrCmp := 1
      else if lhs[ia] = #0 then
        begin
          if rhs[ib] = #0 then
            StrCmp := 0
          else
            StrCmp := -1
        end
      else if rhs[ib] = #0 then
        StrCmp := 1
      else
        StrCmp := -1
    end
end;

function StartsWith(text: array[text_lo..text_hi: integer] of char;
                    prefix: array[prefix_lo..prefix_hi: integer] of char): boolean;
var
  is: integer;
  ip: integer;
  ok: boolean;
  done: boolean;
begin
  is := text_lo;
  ip := prefix_lo;
  ok := true;
  done := false;
  while ip <= prefix_hi do
    begin
      if done then
        ip := prefix_hi + 1
      else if prefix[ip] = #0 then
        done := true
      else if is > text_hi then
        begin
          ok := false;
          done := true
        end
      else if text[is] = #0 then
        begin
          ok := false;
          done := true
        end
      else if text[is] <> prefix[ip] then
        begin
          ok := false;
          done := true
        end
      else
        begin
          is := is + 1;
          ip := ip + 1
        end
    end;
  StartsWith := ok
end;

procedure TrimLeft(var text: array[text_lo..text_hi: integer] of char);
var
  first: integer;
  i: integer;
  j: integer;
  done: boolean;
begin
  first := text_lo;
  done := false;
  while first <= text_hi do
    begin
      if done then
        first := text_hi + 1
      else if text[first] = ' ' then
        first := first + 1
      else
        done := true
    end;
  if not done then
    begin
      text[text_lo] := #0;
      i := text_lo + 1;
      while i <= text_hi do
        begin
          text[i] := #0;
          i := i + 1
        end
    end
  else
    begin
      i := first;
      j := text_lo;
      while i <= text_hi do
        begin
          text[j] := text[i];
          i := i + 1;
          j := j + 1
        end;
      while j <= text_hi do
        begin
          text[j] := #0;
          j := j + 1
        end
    end
end;

procedure TrimRight(var text: array[text_lo..text_hi: integer] of char);
var
  last: integer;
  cut: integer;
  i: integer;
  done: boolean;
begin
  last := text_lo - 1;
  i := text_lo;
  done := false;
  while i <= text_hi do
    begin
      if done then
        i := text_hi + 1
      else if text[i] = #0 then
        done := true
      else
        begin
          last := i;
          i := i + 1
        end
    end;
  cut := last;
  done := false;
  while cut >= text_lo do
    begin
      if done then
        cut := text_lo - 1
      else if text[cut] = ' ' then
        cut := cut - 1
      else
        done := true
    end;
  if done then
    cut := cut + 1;
  if cut < text_lo then
    begin
      text[text_lo] := #0;
      i := text_lo + 1;
      while i <= text_hi do
        begin
          text[i] := #0;
          i := i + 1
        end
    end
  else if cut < text_hi then
    begin
      text[cut + 1] := #0;
      i := cut + 2;
      while i <= text_hi do
        begin
          text[i] := #0;
          i := i + 1
        end
    end
end;

function ParseInt(text: array[text_lo..text_hi: integer] of char; var value: integer): boolean;
var
  i: integer;
  sign: integer;
  digit: integer;
  saw_digit: boolean;
  done: boolean;
begin
  value := 0;
  sign := 1;
  saw_digit := false;
  done := false;
  i := text_lo;
  while i <= text_hi do
    begin
      if done then
        i := text_hi + 1
      else if text[i] = ' ' then
        i := i + 1
      else if text[i] = '+' then
        begin
          i := i + 1;
          done := true
        end
      else if text[i] = '-' then
        begin
          sign := -1;
          i := i + 1;
          done := true
        end
      else
        done := true
    end;

  done := false;
  while i <= text_hi do
    begin
      if text[i] = #0 then
        done := true
      else if done then
        i := text_hi + 1
      else if text[i] < '0' then
        begin
          ParseInt := false;
          value := 0;
          i := text_hi + 1
        end
      else if text[i] > '9' then
        begin
          ParseInt := false;
          value := 0;
          i := text_hi + 1
        end
      else
        begin
          digit := Ord(text[i]) - Ord('0');
          value := value * 10 + digit;
          saw_digit := true;
          i := i + 1
        end
    end;

  if not saw_digit then
    begin
      ParseInt := false;
      value := 0
    end
  else
    begin
      value := value * sign;
      ParseInt := true
    end
end;

function StrEqIgnoreCase(lhs: array[lhs_lo..lhs_hi: integer] of char;
                         rhs: array[rhs_lo..rhs_hi: integer] of char): boolean;
var
  i: integer;
  j: integer;
  same: boolean;
  done: boolean;
begin
  i := lhs_lo;
  j := rhs_lo;
  same := true;
  done := false;
  while i <= lhs_hi do
    begin
      if done then
        i := lhs_hi + 1
      else if j > rhs_hi then
        done := true
      else if lhs[i] = #0 then
        done := true
      else if rhs[j] = #0 then
        done := true
      else if UpCase(lhs[i]) <> UpCase(rhs[j]) then
        begin
          same := false;
          done := true
        end
      else
        begin
          i := i + 1;
          j := j + 1
        end
    end;
  if not same then
    StrEqIgnoreCase := false
  else
    begin
      StrEqIgnoreCase := true;
      if i <= lhs_hi then
        begin
          if lhs[i] <> #0 then
            StrEqIgnoreCase := false
        end;
      if j <= rhs_hi then
        begin
          if rhs[j] <> #0 then
            StrEqIgnoreCase := false
        end
    end
end;

function StrEqLit(text: array[text_lo..text_hi: integer] of char;
                  lit: array[lit_lo..lit_hi: integer] of char): boolean;
begin
  StrEqLit := StrEq(text, lit)
end;

function StrEqIgnoreCaseLit(text: array[text_lo..text_hi: integer] of char;
                            lit: array[lit_lo..lit_hi: integer] of char): boolean;
begin
  StrEqIgnoreCaseLit := StrEqIgnoreCase(text, lit)
end;

function HasNameEqIgnoreCase(name: array[name_lo..name_hi: integer] of char;
                             lit: array[lit_lo..lit_hi: integer] of char): boolean;
begin
  if name[name_lo] = #0 then
    HasNameEqIgnoreCase := false
  else
    HasNameEqIgnoreCase := StrEqIgnoreCase(name, lit)
end;
